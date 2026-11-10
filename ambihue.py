#!/usr/bin/env python3
"""
ambihue - proof of concept: Philips Ambilight -> Philips Hue.

Reads the colours the TV's Ambilight has already worked out (so it follows
every input, Apple TV included) and pushes them to Hue lights via the bridge.

Standard library only. Usage:

  python3 ambihue.py probe <tv-ip>          # does the TV expose the API?
  python3 ambihue.py pair-tv <tv-ip>        # one-time: enter the PIN shown on TV
  python3 ambihue.py peek                   # print live Ambilight colours
  python3 ambihue.py pair-hue [bridge-ip]   # one-time: press the bridge button when asked
  python3 ambihue.py lights                 # list Hue lights and their ids
  python3 ambihue.py run 3:left 5:right 7:top
  python3 ambihue.py run 3:left 5:right --min-brightness 0.2 --brightness 0.5

Sides: left, right, top, bottom, all. Ctrl+C stops and restores the lights.

run is tuned to be calm: colours are averaged over --smooth seconds, each
update fades for as long as the gap to the next one, changes smaller than
--deadzone are skipped, and lights that share a side are driven as one Hue
group so they change at the same instant (--no-group turns that off).

PoC note: this uses the normal Hue REST API, which is limited to roughly 10
light commands or 1 group command per second in total, so more lights =
lower refresh rate. The Pi version should use the Hue Entertainment API for
smooth 25+ fps streaming.
"""
import argparse
import base64
import hashlib
import hmac
import http.client
import json
import math
import os
import random
import signal
import ssl
import string
import sys
import time
import urllib.parse
import urllib.request

CONFIG_PATH = os.path.expanduser("~/.ambihue.json")
# Shared secret used by Philips' own remote apps to sign pairing requests.
PHILIPS_SECRET = base64.b64decode(
    "ZmVay1EQVFOaZhwQ4Kv81ypLAZNczV9sG4KkseXWn1NEk6cXmPKO/MCa9sryslvLCFMnNe4Z4CPXzToowvhHvA=="
)
SIDES = ("left", "right", "top", "bottom")
# Bridge budget from the Hue docs: about 10 light commands or 1 group command
# per second. Past that the bridge queues commands and the lights lag behind.
HUE_LIGHT_COST = 0.1
HUE_GROUP_COST = 1.0
# Added to every channel before the colour is worked out. A near-black frame's
# tint is mostly noise, and at a raised minimum brightness the lamp would show
# it fully saturated. This pulls dark frames towards white instead.
DARK_LIFT = 8

# The TV uses a self-signed certificate.
SSL_CTX = ssl.create_default_context()
SSL_CTX.check_hostname = False
SSL_CTX.verify_mode = ssl.CERT_NONE


def load_config():
    if not os.path.exists(CONFIG_PATH):
        return {}
    with open(CONFIG_PATH) as f:
        return json.load(f)


def save_config(cfg):
    with open(CONFIG_PATH, "w") as f:
        json.dump(cfg, f, indent=2)
    os.chmod(CONFIG_PATH, 0o600)


def die(msg):
    print(msg, file=sys.stderr)
    sys.exit(1)


def require(cfg, *keys):
    missing = [k for k in keys if cfg.get(k) is None]
    if len(missing) > 0:
        die(f"Missing {', '.join(missing)} in {CONFIG_PATH}. Run the pairing steps first.")


# ---------------------------------------------------------------- TV (jointSPACE)

class TVAuthError(Exception):
    """The TV rejected the stored credentials."""


class TV:
    """One kept-alive connection to the TV's jointSPACE API.

    The TV stops answering new TLS handshakes while an earlier connection is
    still waiting to be closed, so every response is read to the end on the
    same connection and the digest retry reuses it. The nonce is reused too,
    which makes a normal poll a single request.
    """

    def __init__(self, base, user=None, password=None, timeout=10):
        u = urllib.parse.urlsplit(base)
        self.https = u.scheme == "https"
        self.host = u.hostname
        self.port = u.port
        self.prefix = u.path.rstrip("/")
        self.user = user
        self.password = password
        self.timeout = timeout
        self.conn = None
        self.challenge = None
        self.nc = 0

    def close(self):
        if self.conn is not None:
            self.conn.close()
            self.conn = None

    def _authorization(self, method, uri):
        ch = self.challenge
        algo = ch.get("algorithm", "MD5").upper()
        if algo not in ("MD5", "SHA-256"):
            raise TVAuthError(f"Unsupported digest algorithm {algo}")

        def h(text):
            return hashlib.new(algo.replace("-", "").lower(), text.encode()).hexdigest()

        ha1 = h(f"{self.user}:{ch['realm']}:{self.password}")
        ha2 = h(f"{method}:{uri}")
        fields = {"username": self.user, "realm": ch["realm"], "nonce": ch["nonce"], "uri": uri}
        quoted = ["username", "realm", "nonce", "uri", "response"]
        if "auth" in [q.strip() for q in ch.get("qop", "").split(",")]:
            self.nc += 1
            nc = f"{self.nc:08x}"
            cnonce = os.urandom(8).hex()
            fields["response"] = h(f"{ha1}:{ch['nonce']}:{nc}:{cnonce}:auth:{ha2}")
            fields.update(qop="auth", nc=nc, cnonce=cnonce)
            quoted.append("cnonce")
        else:
            fields["response"] = h(f"{ha1}:{ch['nonce']}:{ha2}")
        if ch.get("opaque") is not None:
            fields["opaque"] = ch["opaque"]
            quoted.append("opaque")
        fields["algorithm"] = algo
        return "Digest " + ", ".join(
            f'{k}="{v}"' if k in quoted else f"{k}={v}" for k, v in fields.items()
        )

    def _exchange(self, method, uri, data):
        headers = {"Content-Type": "application/json", "Connection": "keep-alive"}
        if self.challenge is not None and self.user is not None:
            headers["Authorization"] = self._authorization(method, uri)
        # A kept-alive connection can have been dropped by the TV while idle,
        # so the first failure on a reused connection gets one fresh attempt.
        for fresh in (self.conn is None, True):
            if self.conn is None:
                cls = http.client.HTTPSConnection if self.https else http.client.HTTPConnection
                kwargs = {"context": SSL_CTX} if self.https else {}
                self.conn = cls(self.host, self.port, timeout=self.timeout, **kwargs)
            try:
                self.conn.request(method, uri, body=data, headers=headers)
                resp = self.conn.getresponse()
                return resp.status, resp.getheader("WWW-Authenticate"), resp.read()
            except (OSError, http.client.HTTPException):
                self.close()
                if fresh:
                    raise

    def request(self, method, path, body=None):
        uri = f"{self.prefix}/{path}"
        data = json.dumps(body).encode() if body is not None else None
        status, challenge, raw = self._exchange(method, uri, data)
        if status == 401 and self.user is not None and challenge is not None:
            # First request, or the nonce expired: answer the new challenge.
            scheme, _, params = challenge.partition(" ")
            if scheme.lower() != "digest":
                raise TVAuthError(f"TV asked for {scheme} auth, expected Digest")
            self.challenge = urllib.request.parse_keqv_list(urllib.request.parse_http_list(params))
            self.nc = 0
            status, challenge, raw = self._exchange(method, uri, data)
        if status == 401:
            raise TVAuthError("TV rejected the credentials (401)")
        if status >= 400:
            raise http.client.HTTPException(f"TV answered {status} for {method} {uri}")
        if len(raw) == 0:
            return None
        return json.loads(raw)


def tv_client(cfg):
    return TV("https://%s:1926/6" % cfg["tv_ip"], cfg.get("tv_user"), cfg.get("tv_pass"))


def cmd_probe(args):
    for label, base in (
        ("https :1926 /6", f"https://{args.ip}:1926/6"),
        ("http  :1925 /6", f"http://{args.ip}:1925/6"),
        ("http  :1925 /1", f"http://{args.ip}:1925/1"),
    ):
        tv = TV(base, timeout=5)
        try:
            res = tv.request("GET", "system")
        except Exception as e:
            print(f"[--] {label}: {e}")
            continue
        finally:
            tv.close()
        print(f"[OK] {label}")
        print(json.dumps(res, indent=2))
        return
    die("TV did not answer on any jointSPACE port. Make sure it's on and on the same network.")


def cmd_pair_tv(args):
    cfg = load_config()
    cfg["tv_ip"] = args.ip
    cfg.pop("tv_user", None)
    cfg.pop("tv_pass", None)
    device_id = "".join(random.choices(string.ascii_letters + string.digits, k=16))
    device = {
        "device_name": "ambihue",
        "device_os": "macOS",
        "app_name": "ambihue",
        "type": "native",
        "app_id": "app.ambihue",
        "id": device_id,
    }
    tv = tv_client(cfg)
    res = tv.request("POST", "pair/request", {"scope": ["read", "write", "control"], "device": device})
    if res is None or res.get("error_id") != "SUCCESS":
        die(f"Pair request failed: {res}")
    pin = input("Enter the PIN shown on the TV: ").strip()
    ts = res["timestamp"]
    sig = base64.b64encode(
        hmac.new(PHILIPS_SECRET, f"{ts}{pin}".encode(), hashlib.sha1).hexdigest().encode()
    ).decode()
    cfg["tv_user"] = tv.user = device_id
    cfg["tv_pass"] = tv.password = res["auth_key"]
    grant = {
        "auth": {"auth_AppId": "1", "pin": pin, "auth_timestamp": ts, "auth_signature": sig},
        "device": device,
    }
    try:
        tv.request("POST", "pair/grant", grant)
    except (TVAuthError, http.client.HTTPException) as e:
        die(f"Pair grant failed ({e}). Wrong PIN or it timed out, try again.")
    finally:
        tv.close()
    save_config(cfg)
    print(f"Paired with TV. Credentials saved to {CONFIG_PATH}")


def lit(layer):
    return any(p[c] > 0 for side in layer.values() for p in side.values() for c in "rgb")


class Ambilight:
    """Polls the TV for per-side colours, reconnecting with backoff.

    /ambilight/processed is what the TV's own LEDs show, but some sets (the
    2023 OLED708 among them) always answer it with black. In "auto" a black
    processed frame is checked against /ambilight/measured, and if that one
    has colour the reader stays on measured.
    """

    def __init__(self, cfg, source="auto"):
        self.tv = tv_client(cfg)
        self.auto = source == "auto"
        self.source = "processed" if self.auto else source
        self.backoff = 0

    def _get(self, source):
        data = self.tv.request("GET", f"ambilight/{source}")
        if not isinstance(data, dict) or not isinstance(data.get("layer1"), dict):
            raise http.client.HTTPException(f"Unexpected Ambilight response: {str(data)[:200]}")
        return data["layer1"]

    def read(self):
        """Returns the layer, or None after a failed read (it has slept already)."""
        try:
            layer = self._get(self.source)
            if self.auto and self.source == "processed" and not lit(layer):
                measured = self._get("measured")
                if lit(measured):
                    print("ambilight/processed is black, using ambilight/measured", file=sys.stderr)
                    self.source = "measured"
                    layer = measured
        except TVAuthError as e:
            die(f"{e}. Re-pair with: ambihue.py pair-tv {self.tv.host}")
        except (OSError, http.client.HTTPException, ValueError) as e:
            self.tv.close()
            self.backoff = min(5, max(0.5, self.backoff * 2))
            print(f"TV read failed ({e}), reconnecting in {self.backoff:g}s", file=sys.stderr)
            time.sleep(self.backoff)
            return None
        self.backoff = 0
        return layer


def side_average(layer, side):
    sides = SIDES if side == "all" else (side,)
    pixels = []
    for s in sides:
        pixels.extend((layer.get(s) or {}).values())
    if len(pixels) == 0:
        return (0, 0, 0)
    n = len(pixels)
    return (
        sum(p["r"] for p in pixels) / n,
        sum(p["g"] for p in pixels) / n,
        sum(p["b"] for p in pixels) / n,
    )


def cmd_peek(args):
    cfg = load_config()
    require(cfg, "tv_ip", "tv_user")
    ambilight = Ambilight(cfg, args.source)
    try:
        while True:
            layer = ambilight.read()
            if layer is None:
                continue
            parts = []
            for s in SIDES:
                if len(layer.get(s) or {}) == 0:
                    continue
                r, g, b = side_average(layer, s)
                parts.append(f"{s}: ({r:3.0f},{g:3.0f},{b:3.0f}) x{len(layer[s])}")
            print(" | ".join(parts), flush=True)
            time.sleep(args.interval)
    except KeyboardInterrupt:
        print()
    finally:
        ambilight.tv.close()


# ---------------------------------------------------------------- Hue

def hue_request(cfg, method, path, body=None):
    url = f"http://{cfg['hue_ip']}/api{path}"
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(url, data=data, method=method, headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=5) as r:
        return json.loads(r.read())


def discover_bridge():
    with urllib.request.urlopen("https://discovery.meethue.com", timeout=5) as r:
        bridges = json.loads(r.read())
    if len(bridges) == 0:
        die("No Hue bridge found. Pass its IP: pair-hue <bridge-ip>")
    return bridges[0]["internalipaddress"]


def cmd_pair_hue(args):
    cfg = load_config()
    cfg["hue_ip"] = args.ip if args.ip is not None else discover_bridge()
    print(f"Using bridge at {cfg['hue_ip']}")
    print(f"Press the link button on the bridge now (waiting up to {args.wait:g}s)...", flush=True)
    deadline = time.monotonic() + args.wait
    while True:
        try:
            entry = hue_request(cfg, "POST", "", {"devicetype": "ambihue#mac"})[0]
        except OSError as e:
            # A network blip while waiting is not a reason to start over.
            entry = {"error": {"type": 101, "description": str(e)}}
        if entry.get("success") is not None:
            break
        error = entry.get("error", {})
        # 101 = link button not pressed yet
        if error.get("type") != 101:
            die(f"Bridge said: {error.get('description', entry)}")
        if time.monotonic() > deadline:
            die("Link button was not pressed in time, try again.")
        time.sleep(1)
    cfg["hue_user"] = entry["success"]["username"]
    save_config(cfg)
    print("Paired with Hue bridge.")


def cmd_lights(args):
    cfg = load_config()
    require(cfg, "hue_ip", "hue_user")
    lights = hue_request(cfg, "GET", f"/{cfg['hue_user']}/lights")
    for lid, light in sorted(lights.items(), key=lambda kv: int(kv[0])):
        state = light["state"]
        colour = "colour" if state.get("xy") is not None else "no colour"
        power = "unreachable" if not state.get("reachable", True) else "on" if state["on"] else "off"
        print(f"{lid:>3}  {light['name']:<30} {colour:<10} {power}")


def rgb_to_hue(rgb, bri_min, bri_max):
    """sRGB 0-255 -> Hue CIE xy + bri (Wide RGB D65 conversion)."""
    def lin(c):
        c = (c + DARK_LIFT) / (255 + DARK_LIFT)
        return ((c + 0.055) / 1.055) ** 2.4 if c > 0.04045 else c / 12.92

    r, g, b = (lin(c) for c in rgb)
    x_ = r * 0.664511 + g * 0.154324 + b * 0.162028
    y_ = r * 0.283881 + g * 0.668433 + b * 0.047685
    z_ = r * 0.000088 + g * 0.072310 + b * 0.986039
    total = x_ + y_ + z_
    level = bri_min + (bri_max - bri_min) * max(rgb) / 255
    bri = max(1, min(254, round(254 * level)))
    return (round(x_ / total, 4), round(y_ / total, 4)), bri


def snapshot(lights, ids):
    states = {}
    for lid in ids:
        s = lights[lid]["state"]
        restore = {"on": s["on"], "bri": s.get("bri")}
        if s.get("colormode") == "ct" and s.get("ct") is not None:
            restore["ct"] = s["ct"]
        elif s.get("xy") is not None:
            restore["xy"] = s["xy"]
        states[lid] = {k: v for k, v in restore.items() if v is not None}
    return states


def hue_put(cfg, path, body, seen_errors=None):
    """Sets a light's or group's state. The bridge answers 200 even when it
    refuses, so its per-field errors are printed (once each when seen_errors
    is given)."""
    try:
        res = hue_request(cfg, "PUT", f"/{cfg['hue_user']}{path}", body)
        errors = [e["error"].get("description", str(e)) for e in res if e.get("error") is not None]
    except (OSError, ValueError) as e:
        errors = [str(e)]
    for msg in errors:
        if seen_errors is None or (path, msg) not in seen_errors:
            print(f"Hue update failed for {path}: {msg}", file=sys.stderr)
        if seen_errors is not None:
            seen_errors.add((path, msg))


def restore_lights(cfg, saved):
    # A second Ctrl+C must not leave half the lights on the TV's colours.
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    print("\nRestoring lights...")
    for lid, state in saved.items():
        path = f"/lights/{lid}/state"
        if state["on"]:
            hue_put(cfg, path, {**state, "transitiontime": 4})
        else:
            # An off light refuses colour changes, so put its colour back
            # while it is still on and only then switch it off.
            hue_put(cfg, path, {**state, "on": True, "transitiontime": 0})
            hue_put(cfg, path, {"on": False})


def interrupt(signum, frame):
    raise KeyboardInterrupt


def hue_targets(cfg, lights, mapping, use_groups, created):
    """Turns the light:side mapping into the things colours are sent to.

    Lights that share a side become one Hue group, so they change at the same
    instant instead of one after another. A group with exactly those lights is
    reused if the bridge has one, otherwise one is made and its id is added to
    `created` so it can be deleted on exit.
    """
    by_side = {}
    for lid, side in mapping:
        by_side.setdefault(side, []).append(lid)
    targets = []
    groups = None
    for side, lids in by_side.items():
        if not use_groups or len(lids) == 1:
            for lid in lids:
                colour = lights[lid]["state"].get("xy") is not None
                targets.append({"side": side, "path": f"/lights/{lid}/state", "cost": HUE_LIGHT_COST, "colour": colour})
            continue
        if groups is None:
            groups = hue_request(cfg, "GET", f"/{cfg['hue_user']}/groups")
        gid = next((g for g, info in groups.items() if sorted(info["lights"]) == sorted(lids)), None)
        if gid is None:
            body = {"name": f"ambihue {side}", "type": "LightGroup", "lights": lids}
            res = hue_request(cfg, "POST", f"/{cfg['hue_user']}/groups", body)[0]
            if res.get("success") is None:
                die(f"Could not group lights {', '.join(lids)}: {res.get('error', {}).get('description', res)}")
            gid = res["success"]["id"]
            created.append(gid)
        elif groups[gid]["name"].startswith("ambihue "):
            # Left behind by a run that was killed before it could clean up.
            created.append(gid)
        targets.append({"side": side, "path": f"/groups/{gid}/action", "cost": HUE_GROUP_COST, "colour": True})
    return targets


def cmd_run(args):
    cfg = load_config()
    require(cfg, "tv_ip", "tv_user", "hue_ip", "hue_user")
    if not 0 <= args.min_brightness <= args.brightness <= 1:
        die("Need 0 <= --min-brightness <= --brightness <= 1")
    lights = hue_request(cfg, "GET", f"/{cfg['hue_user']}/lights")
    mapping = []
    for item in args.mapping:
        lid, _, side = item.partition(":")
        side = side or "all"
        if side not in SIDES and side != "all":
            die(f"Unknown side '{side}' in '{item}'")
        if lights.get(lid) is None:
            die(f"No Hue light with id '{lid}'. Run: ambihue.py lights")
        if not lights[lid]["state"].get("reachable", True):
            print(f"Light {lid} ({lights[lid]['name']}) is unreachable, is it powered?", file=sys.stderr)
        mapping.append((lid, side))
    if len(mapping) == 0:
        die("Give at least one light, e.g. run 3:left 5:right")

    # kill and a closed terminal restore the lights the same way Ctrl+C does.
    signal.signal(signal.SIGTERM, interrupt)
    signal.signal(signal.SIGHUP, interrupt)
    ambilight = Ambilight(cfg, args.source)
    saved = snapshot(lights, [lid for lid, _ in mapping])
    created = []
    seen_errors = set()
    try:
        targets = hue_targets(cfg, lights, mapping, args.group, created)
        interval = max(1 / args.fps, sum(t["cost"] for t in targets))
        # A fade as long as the gap between updates gives a continuous drift
        # instead of step, pause, step.
        transition = args.transition if args.transition is not None else max(1, round(interval * 10))
        print(
            f"Syncing {len(mapping)} light(s) with {len(targets)} command(s) every {interval:.1f}s, "
            f"{transition / 10:g}s fade. Ctrl+C to stop."
        )
        # The TV is polled faster than the bridge can be updated, so the
        # smoothing averages real samples instead of one frame per update.
        tick = min(interval, 0.1)
        next_send = 0
        while True:
            start = time.monotonic()
            layer = ambilight.read()
            if layer is None:
                continue
            for t in targets:
                if t["side"] != "all" and len(layer.get(t["side"]) or {}) == 0:
                    die(f"The TV has no Ambilight LEDs on the {t['side']} side.")
                rgb = side_average(layer, t["side"])
                if args.smooth > 0 and t.get("rgb") is not None:
                    weight = 1 - math.exp(-(start - t["at"]) / args.smooth)
                    rgb = tuple(old + (new - old) * weight for old, new in zip(t["rgb"], rgb))
                t["rgb"] = rgb
                t["at"] = start
            if start >= next_send:
                next_send = start + interval
                for t in targets:
                    sent = t.get("sent")
                    if sent is not None and max(abs(a - b) for a, b in zip(t["rgb"], sent)) < args.deadzone:
                        continue
                    xy, bri = rgb_to_hue(t["rgb"], args.min_brightness, args.brightness)
                    body = {"bri": bri, "transitiontime": transition}
                    if t["colour"]:
                        body["xy"] = list(xy)
                    if body == t.get("body"):
                        continue
                    # "on" only goes out once: resending it slows the bridge,
                    # and a light switched off by hand mid-sync stays off.
                    hue_put(cfg, t["path"], body if sent is not None else {**body, "on": True}, seen_errors)
                    t["sent"] = t["rgb"]
                    t["body"] = body
            time.sleep(max(0, tick - (time.monotonic() - start)))
    except KeyboardInterrupt:
        pass
    finally:
        restore_lights(cfg, saved)
        for gid in created:
            try:
                hue_request(cfg, "DELETE", f"/{cfg['hue_user']}/groups/{gid}")
            except OSError as e:
                print(f"Could not delete Hue group {gid}: {e}", file=sys.stderr)
        ambilight.tv.close()


def main():
    p = argparse.ArgumentParser(description="Philips Ambilight -> Hue proof of concept")
    sub = p.add_subparsers(dest="cmd", required=True)
    sp = sub.add_parser("probe", help="check whether the TV exposes the API")
    sp.add_argument("ip")
    sp.set_defaults(fn=cmd_probe)
    sp = sub.add_parser("pair-tv", help="pair with the TV (PIN shown on screen)")
    sp.add_argument("ip")
    sp.set_defaults(fn=cmd_pair_tv)
    source = {"choices": ("auto", "processed", "measured"), "default": "auto", "help": "which TV endpoint to read"}
    sp = sub.add_parser("peek", help="print live Ambilight colours")
    sp.add_argument("--source", **source)
    sp.add_argument("--interval", type=float, default=0.5, help="seconds between polls")
    sp.set_defaults(fn=cmd_peek)
    sp = sub.add_parser("pair-hue", help="pair with the Hue bridge")
    sp.add_argument("ip", nargs="?")
    sp.add_argument("--wait", type=float, default=60, help="seconds to wait for the link button")
    sp.set_defaults(fn=cmd_pair_hue)
    sub.add_parser("lights", help="list Hue lights").set_defaults(fn=cmd_lights)
    sp = sub.add_parser("run", help="sync lights, e.g. run 3:left 5:right 7:top")
    sp.add_argument("mapping", nargs="*")
    sp.add_argument("--fps", type=float, default=10, help="upper limit on updates per second")
    sp.add_argument("--brightness", type=float, default=1.0, help="lamp brightness for a white picture, 0-1")
    sp.add_argument("--min-brightness", type=float, default=0.0, help="lamp brightness for a black picture, 0-1")
    sp.add_argument("--smooth", type=float, default=1.5, help="seconds of colour averaging, 0 = off")
    sp.add_argument("--deadzone", type=float, default=4, help="skip colour changes smaller than this (0-255)")
    sp.add_argument("--transition", type=int, help="Hue fade in 100ms steps (default: the gap between updates)")
    sp.add_argument("--group", action=argparse.BooleanOptionalAction, default=True,
                    help="drive lights that share a side as one Hue group")
    sp.add_argument("--source", **source)
    sp.set_defaults(fn=cmd_run)
    args = p.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
