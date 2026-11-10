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

run boosts saturation (--saturation), because the TV reports the muted
average of the picture's edge, not the vivid colour its own LEDs show. It is
also tuned to be calm. The TV is polled --fps times a second, and what the
lights do depends on how big the change is:

  - a big change (--cut, a scene cut) goes to the lights at once, short fade
  - anything smaller drifts: averaged over --smooth seconds and sent at most
    every --drift seconds with a fade that long
  - changes below --deadzone are not sent at all

Lights that share a side are driven as one Hue group so they change at the
same instant (--no-group turns that off).

While the TV's Ambilight is switched off, or the TV is in standby, the lights
go back to how they were, and syncing resumes when Ambilight is back
(--no-follow syncs regardless).

PoC note: this uses the normal Hue REST API, which is limited to roughly 10
light commands or 1 group command per second in total, so more lights =
lower refresh rate. The Pi version should use the Hue Entertainment API for
smooth 25+ fps streaming.
"""
import argparse
import base64
import colorsys
import fcntl
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
import threading
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
# Below this level (0-255) a frame's colour fades towards white. A near-black
# frame's tint is mostly noise, and at a raised minimum brightness the lamp
# would otherwise show it fully saturated.
DARK_FADE = 24
# Fade for a scene cut, in 100ms steps: quick, but not a flash.
CUT_FADE = 3
# Seconds of averaging behind "what is on screen right now", which cuts are
# detected on. One bright frame does not move it far enough to count.
CUT_SMOOTH = 0.2
# Seconds without an answer before the TV counts as switched off.
TV_GONE_AFTER = 5

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


def find_nodes(tree, contexts, found=None):
    """Maps settings-menu context names to their node ids."""
    found = {} if found is None else found
    if isinstance(tree, dict):
        if tree.get("context") in contexts and tree.get("node_id") is not None:
            found.setdefault(tree["context"], tree["node_id"])
        tree = list(tree.values())
    if isinstance(tree, list):
        for item in tree:
            find_nodes(item, contexts, found)
    return found


class Ambilight:
    """Polls the TV for per-side colours, reconnecting with backoff.

    /ambilight/processed is what the TV's own LEDs show, but some sets (the
    2023 OLED708 among them) always answer it with black. In "auto" a black
    processed frame is checked against /ambilight/measured, and if that one
    has colour the reader stays on measured.

    With follow=True a second connection checks once a second whether the
    TV's Ambilight is switched on. /ambilight/power and
    /ambilight/currentconfiguration say "off" on the OLED708 while the LEDs
    are lit, so the answer comes from the settings menu: the Ambilight style
    entry names its active child, and one of the children is Off. The query
    is a POST, but it only reads.
    """

    def __init__(self, cfg, source="auto", follow=False):
        self.tv = tv_client(cfg)
        self.auto = source == "auto"
        self.source = "processed" if self.auto else source
        self.backoff = 0
        self.failing_since = None
        # None until the first style check has answered.
        self.on = None if follow else True
        self.started = time.monotonic()
        if follow:
            threading.Thread(target=self._watch, args=(cfg,), daemon=True).start()

    def _get(self, source):
        data = self.tv.request("GET", f"ambilight/{source}")
        if not isinstance(data, dict) or not isinstance(data.get("layer1"), dict):
            raise http.client.HTTPException(f"Unexpected Ambilight response: {str(data)[:200]}")
        return data["layer1"]

    def _watch(self, cfg):
        """Keeps self.on current. It has a thread and connection of its own
        because about one style query in fifty takes the TV two seconds,
        which would freeze the colour polling if they shared one."""
        tv = tv_client(cfg)
        nodes = None
        while True:
            try:
                if nodes is None:
                    structure = tv.request("GET", "menuitems/settings/structure")
                    nodes = find_nodes(structure, ("ambilight_style", "ambilight_off"))
                query = {"nodes": [{"nodeid": nodes["ambilight_style"]}]}
                current = tv.request("POST", "menuitems/settings/current", query)
                self.on = current["values"][0]["value"]["data"]["activenode_id"] != nodes["ambilight_off"]
            except (KeyError, IndexError, TypeError):
                print("This TV does not report its Ambilight style, syncing regardless of it.", file=sys.stderr)
                self.on = True
                return
            except (OSError, http.client.HTTPException, ValueError, TVAuthError):
                # Standby or a blip. read() is the one that notices a TV that
                # is gone, so the last known answer stands.
                tv.close()
            time.sleep(1)

    def idle(self):
        """True when the lights should go back to how they were: Ambilight is
        switched off, or the TV has not answered for a while (standby)."""
        gone = self.failing_since is not None and time.monotonic() - self.failing_since > TV_GONE_AFTER
        return self.on is False or gone

    def read(self):
        """Returns the layer, or None when there is nothing to show: a failed
        read, or Ambilight switched off. It has slept already in both cases."""
        try:
            if self.on is None and time.monotonic() - self.started < TV_GONE_AFTER:
                # Not known yet. Waiting beats flashing the lights on a TV
                # whose Ambilight turns out to be off.
                time.sleep(0.05)
                return None
            if self.on is False:
                self.failing_since = None
                time.sleep(0.25)
                return None
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
            if self.failing_since is None:
                # Said once, not every retry: a TV in standby fails for hours.
                self.failing_since = time.monotonic()
                print(f"TV read failed ({e}), retrying until it answers", file=sys.stderr)
            time.sleep(self.backoff)
            return None
        self.backoff = 0
        self.failing_since = None
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


def vivid(rgb, gain):
    """Boosts saturation the way the TV does for its own LEDs.

    /ambilight/measured is the plain average of the picture's edge, which is
    muted (saturation around 0.4 on typical content). The curve lifts that
    without pushing greys into colour: 0.4 becomes 0.72 at the default gain.
    """
    h, s, v = colorsys.rgb_to_hsv(*(c / 255 for c in rgb))
    s = (1 - (1 - s) ** gain) * min(1, v * 255 / DARK_FADE)
    return tuple(c * 255 for c in colorsys.hsv_to_rgb(h, s, v))


def rgb_to_hue(rgb, bri_min, bri_max):
    """sRGB 0-255 -> Hue CIE xy + bri (Wide RGB D65 conversion)."""
    def lin(c):
        c /= 255
        return ((c + 0.055) / 1.055) ** 2.4 if c > 0.04045 else c / 12.92

    r, g, b = (lin(c) for c in rgb)
    x_ = r * 0.664511 + g * 0.154324 + b * 0.162028
    y_ = r * 0.283881 + g * 0.668433 + b * 0.047685
    z_ = r * 0.000088 + g * 0.072310 + b * 0.986039
    total = x_ + y_ + z_
    level = bri_min + (bri_max - bri_min) * max(rgb) / 255
    bri = max(1, min(254, round(254 * level)))
    if total == 0:
        return (0.3227, 0.329), bri
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
    # Cheap commands first, so a single lamp is not held up behind a group.
    return sorted(targets, key=lambda t: t["cost"])


def blend(old, new, dt, seconds):
    """Moves a running average towards a new sample."""
    if seconds <= 0:
        return new
    weight = 1 - math.exp(-dt / seconds)
    return tuple(o + (n - o) * weight for o, n in zip(old, new))


def distance(a, b):
    return max(abs(x - y) for x, y in zip(a, b))


def cmd_run(args):
    cfg = load_config()
    require(cfg, "tv_ip", "tv_user", "hue_ip", "hue_user")
    # Two syncs would fight over the lights, and the second one's cleanup
    # would delete the first one's Hue group. The lock dies with the process.
    lock = open(CONFIG_PATH)
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        die("Another ambihue run is already driving the lights. Stop that one first.")
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
    ambilight = Ambilight(cfg, args.source, follow=args.follow)
    ids = [lid for lid, _ in mapping]
    saved = {}
    synced = False  # True while the lights are ours and `saved` is what to put back
    waiting = False
    created = []
    seen_errors = set()
    try:
        targets = hue_targets(cfg, lights, mapping, args.group, created)
        drift_fade = args.transition if args.transition is not None else max(1, round(args.drift * 10))
        cuts = args.cut > 0 and args.smooth > CUT_SMOOTH
        print(
            f"Syncing {len(mapping)} light(s), polling the TV {args.fps:g}x/s. "
            + (f"Cuts fade in {CUT_FADE / 10:g}s, the rest drifts" if cuts else "Drifting")
            + f" every {args.drift:g}s. Ctrl+C to stop."
        )
        bridge_free = 0  # when the bridge's command budget allows the next send
        while True:
            start = time.monotonic()
            layer = ambilight.read()
            if layer is None:
                if ambilight.idle() and not waiting:
                    waiting = True
                    if synced:
                        restore_lights(cfg, saved)
                        synced = False
                    print("Ambilight is off or the TV is not answering. Leaving the lights alone until it is back.")
                continue
            if waiting:
                waiting = False
                print("Ambilight is back, syncing.")
            if not synced:
                # Taken fresh each time: the lights may have been changed by
                # hand while Ambilight was off.
                saved = snapshot(hue_request(cfg, "GET", f"/{cfg['hue_user']}/lights"), ids)
                targets = [{k: t[k] for k in ("side", "path", "cost", "colour")} for t in targets]
                synced = True
            for t in targets:
                if t["side"] != "all" and len(layer.get(t["side"]) or {}) == 0:
                    die(f"The TV has no Ambilight LEDs on the {t['side']} side.")
                rgb = side_average(layer, t["side"])
                if t.get("calm") is None:
                    t["now"] = t["calm"] = rgb
                else:
                    t["now"] = blend(t["now"], rgb, start - t["at"], CUT_SMOOTH)
                    t["calm"] = blend(t["calm"], rgb, start - t["at"], args.smooth)
                    if cuts and distance(t["now"], t["calm"]) >= args.cut:
                        # Scene cut: drop both averages onto the newest frame
                        # (the fast one is still only part of the way there)
                        # and send it as soon as the bridge allows.
                        t["now"] = t["calm"] = rgb
                        t["cut"] = True
                t["at"] = start
            # Whoever has waited longest goes first, so one busy light cannot
            # use up the whole bridge budget.
            for t in sorted(targets, key=lambda t: t.get("sent_at", 0)):
                if start < bridge_free:
                    break
                sent = t.get("sent")
                cut = t.pop("cut", False)
                if sent is not None and not cut:
                    if start < t["drift_at"] or distance(t["calm"], sent) < args.deadzone:
                        continue
                state = rgb_to_hue(vivid(t["calm"], args.saturation), args.min_brightness, args.brightness)
                if state == t.get("state"):
                    continue
                body = {"bri": state[1], "transitiontime": CUT_FADE if cut else drift_fade}
                if t["colour"]:
                    body["xy"] = list(state[0])
                if sent is None:
                    # "on" only goes out once: resending it slows the bridge,
                    # and a light switched off by hand mid-sync stays off.
                    body["on"] = True
                hue_put(cfg, t["path"], body, seen_errors)
                t["sent"] = t["calm"]
                t["state"] = state
                t["sent_at"] = start
                t["drift_at"] = start + args.drift
                bridge_free = start + t["cost"]
            time.sleep(max(0, 1 / args.fps - (time.monotonic() - start)))
    except KeyboardInterrupt:
        pass
    finally:
        # A second Ctrl+C must not leave half the lights on the TV's colours.
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        if synced:
            print("\nRestoring lights...")
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
    sp.add_argument("--fps", type=float, default=20, help="TV polls per second")
    sp.add_argument("--brightness", type=float, default=1.0, help="lamp brightness for a white picture, 0-1")
    sp.add_argument("--min-brightness", type=float, default=0.0, help="lamp brightness for a black picture, 0-1")
    sp.add_argument("--saturation", type=float, default=2.5, help="colour boost, 1 = the TV's raw colours")
    sp.add_argument("--smooth", type=float, default=1.5, help="seconds of colour averaging, 0 = off")
    sp.add_argument("--cut", type=float, default=30, help="a change this big (0-255) goes out at once, 0 = never")
    sp.add_argument("--drift", type=float, default=3, help="seconds between updates for smaller changes")
    sp.add_argument("--deadzone", type=float, default=4, help="skip colour changes smaller than this (0-255)")
    sp.add_argument("--transition", type=int, help="fade for drift updates in 100ms steps (default: --drift)")
    sp.add_argument("--follow", action=argparse.BooleanOptionalAction, default=True,
                    help="restore the lights while the TV's Ambilight is off, resume when it is back")
    sp.add_argument("--group", action=argparse.BooleanOptionalAction, default=True,
                    help="drive lights that share a side as one Hue group")
    sp.add_argument("--source", **source)
    sp.set_defaults(fn=cmd_run)
    args = p.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
