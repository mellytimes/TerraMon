#!/usr/bin/env python3
"""
TerraMon - terminal (TUI) monitor for a Terraria dedicated server.

What it does
  * Watches the Terraria server (vanilla or tModLoader). If it is not running,
    it starts it inside a `screen` session (with crash-loop protection).
  * Compares your public IP with your DuckDNS record and updates DuckDNS
    automatically when they differ.
  * Downloads the latest vanilla dedicated server (terraria.org) or the latest
    tModLoader (GitHub) from inside the TUI - using wget, or Python if wget
    is missing.
  * Shows public IP, DuckDNS IP, server status, version, uptime, RAM, CPU,
    network traffic, errors and the live server console log.
  * Auto-detects the vanilla server, tModLoader and DuckDNS folders.

Only uses the Python 3 standard library. Needs `screen` to start the server.

Usage
  python3 terramon.py             interactive TUI
  python3 terramon.py --headless  no UI (for systemd) - still auto-starts / updates DNS
  python3 terramon.py --status    print a one-shot status report and exit
  python3 terramon.py --scan      print what auto-detection finds and exit

Files
  ~/.config/terramon/config.json        settings (auto-filled, safe to edit)
  ~/.local/state/terramon/terramon.log  TerraMon's own event log
  ~/.local/state/terramon/server.log    console output of the server TerraMon started
  ~/servers/                            where downloaded servers are installed
"""

import argparse
import curses
import fcntl
import ipaddress
import json
import locale
import os
import re
import shutil
import signal
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from collections import deque
from datetime import datetime

APP_NAME = "TerraMon"
APP_VERSION = "1.0"
UA = f"{APP_NAME}/{APP_VERSION}"

HOME = os.path.expanduser("~")
CONF_DIR = os.path.join(HOME, ".config", "terramon")
CONF_PATH = os.path.join(CONF_DIR, "config.json")
STATE_DIR = os.path.join(HOME, ".local", "state", "terramon")
SERVER_LOG = os.path.join(STATE_DIR, "server.log")
APP_LOG = os.path.join(STATE_DIR, "terramon.log")
LOCK_PATH = os.path.join(STATE_DIR, "terramon.lock")
SCREENRC = os.path.join(STATE_DIR, "screenrc")
DOWNLOAD_ROOT = os.path.join(HOME, "servers")
MARKER = ".terramon_version"

VANILLA_BIN = "TerrariaServer.bin.x86_64"
TMOD_SCRIPT = "start-tModLoaderServer.sh"

VANILLA_LIST_URL = "https://terraria.org/api/get/dedicated-servers-names"
VANILLA_DL_URL = "https://terraria.org/api/download/pc-dedicated-server/{name}"
TMOD_RELEASE_URL = "https://api.github.com/repos/tModLoader/tModLoader/releases/latest"
TMOD_LATEST_DL = "https://github.com/tModLoader/tModLoader/releases/latest/download/tModLoader.zip"
PUBLIC_IP_URLS = [
    "https://api.ipify.org",
    "https://ipv4.icanhazip.com",
    "https://checkip.amazonaws.com",
    "https://ifconfig.me/ip",
]

DEFAULTS = {
    "active_server": "auto",        # "vanilla", "tmodloader" or "auto"
    "vanilla_dir": "",              # folder containing TerrariaServer.bin.x86_64
    "vanilla_serverconfig": "",
    "tmod_dir": "",                 # folder containing start-tModLoaderServer.sh
    "tmod_serverconfig": "",
    "tmod_extra_args": ["-nosteam"],
    "duckdns_script": "",
    "duckdns_domain": "",           # subdomain only, e.g. "mellyterraria"
    "duckdns_token": "",
    "screen_session": "terraria",
    "port": 7777,                   # used if the serverconfig has no port=
    "auto_restart": True,
    "auto_duckdns": True,
    "use_wget": True,
    "check_interval": 2,            # seconds between server checks
    "ip_check_interval": 60,        # seconds between public IP / DuckDNS checks
    "startup_grace": 240,           # seconds a start may take before we complain
    "max_restarts": 3,              # auto-restarts allowed inside restart_window
    "restart_window": 600,
}

SKIP_DIRS = {"node_modules", "dotnet", "__pycache__", "proc", "sys", "dev", "run",
             "Content", "Libraries", "Mods", "Worlds", "Players", "Logs"}
SHELL_NAMES = {"screen", "bash", "sh", "dash", "zsh", "sudo", "su", "nohup", "timeout",
               "env", "script", "tail", "less", "grep", "watch"}
WGET_ERRORS = {1: "generic error", 3: "file write error (disk full / permissions?)",
               4: "network failure", 5: "SSL error", 6: "authentication failed",
               7: "protocol error", 8: "server returned an error (404/403?)"}

try:
    CLK_TCK = os.sysconf("SC_CLK_TCK")
except (ValueError, OSError, AttributeError):
    CLK_TCK = 100


# --- Prefer IPv4 everywhere (a broken IPv6 route should never break us) ------
_orig_getaddrinfo = socket.getaddrinfo


def _prefer_ipv4(host, port, family=0, *args, **kwargs):
    res = _orig_getaddrinfo(host, port, family, *args, **kwargs)
    v4 = [r for r in res if r[0] == socket.AF_INET]
    return v4 or res


socket.getaddrinfo = _prefer_ipv4


# --- Small helpers -----------------------------------------------------------
def human_bytes(n):
    if n is None:
        return "-"
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if abs(n) < 1024 or unit == "TB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return "-"


def human_duration(s):
    if s is None:
        return "-"
    s = int(max(0, s))
    d, s = divmod(s, 86400)
    h, s = divmod(s, 3600)
    m, s = divmod(s, 60)
    if d:
        return f"{d}d {h:02d}h {m:02d}m"
    if h:
        return f"{h}h {m:02d}m {s:02d}s"
    return f"{m}m {s:02d}s"


def clock(t):
    return datetime.fromtimestamp(t).strftime("%H:%M:%S") if t else "-"


def version_tuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", str(v or "")))


def describe_error(e):
    if isinstance(e, urllib.error.HTTPError):
        return f"HTTP {e.code} {e.reason}"
    if isinstance(e, urllib.error.URLError):
        return f"network error: {e.reason}"
    if isinstance(e, (socket.timeout, TimeoutError)):
        return "timed out"
    return f"{type(e).__name__}: {e}"


def http_get(url, timeout=15, max_bytes=2_000_000, headers=None):
    h = {"User-Agent": UA}
    h.update(headers or {})
    req = urllib.request.Request(url, headers=h)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read(max_bytes).decode("utf-8", "replace")


def probe_size(url):
    try:
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=20) as r:
            n = r.headers.get("Content-Length")
            return int(n) if n and n.isdigit() and int(n) > 0 else None
    except Exception:
        return None


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        return None


def github_latest_via_redirect(url):
    """Find the latest release tag from GitHub's /latest/download/ redirect (no API needed)."""
    opener = urllib.request.build_opener(_NoRedirect)
    loc = None
    try:
        with opener.open(urllib.request.Request(url, headers={"User-Agent": UA}), timeout=20) as r:
            loc = r.headers.get("Location")
    except urllib.error.HTTPError as e:
        if e.code in (301, 302, 303, 307, 308):
            loc = e.headers.get("Location")
        else:
            raise
    m = re.search(r"/releases/download/([^/]+)/tModLoader\.zip$", loc or "")
    if not m or not loc.startswith("https://"):
        raise RuntimeError("could not find the latest tModLoader release on GitHub")
    return urllib.parse.unquote(m.group(1)), loc


def safe_getsize(p):
    try:
        return os.path.getsize(p)
    except OSError:
        return 0


def make_executable(path):
    try:
        mode = os.stat(path).st_mode
        os.chmod(path, mode | 0o755)
        return True
    except OSError:
        return False


def write_marker(d, version):
    try:
        with open(os.path.join(d, MARKER), "w") as f:
            f.write(str(version).strip() + "\n")
    except OSError:
        pass


def read_marker(d):
    for p in (os.path.join(d, MARKER), os.path.join(os.path.dirname(d), MARKER)):
        try:
            with open(p) as f:
                v = f.read(100).strip()
                if v:
                    return v
        except OSError:
            pass
    return None


def detect_version(kind, d):
    if not d:
        return None
    v = read_marker(d)
    if v:
        return v
    if kind == "vanilla":
        m = re.findall(r"(?:^|/)(\d{4,6})(?=/|$)", d)
        if m:
            return ".".join(m[-1])
    return None


def safe_extract(zpath, dest):
    dest_real = os.path.realpath(dest)
    with zipfile.ZipFile(zpath) as z:
        bad = z.testzip()
        if bad:
            raise RuntimeError(f"zip is corrupted (bad file: {bad})")
        for info in z.infolist():
            target = os.path.realpath(os.path.join(dest, info.filename))
            if target != dest_real and not target.startswith(dest_real + os.sep):
                raise RuntimeError(f"unsafe path in zip: {info.filename}")
            z.extract(info, dest)
            mode = (info.external_attr >> 16) & 0o777
            if mode and not info.is_dir():
                try:
                    os.chmod(target, mode | 0o600)
                except OSError:
                    pass


def parse_serverconfig(path):
    out = {}
    try:
        with open(path, errors="replace") as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                out[k.strip().lower()] = v.strip()
    except OSError:
        pass
    return out


def resolve_world_path(conf_path, world, server_dir=None):
    if not world:
        return None
    w = os.path.expanduser(world)
    if not os.path.isabs(w):
        w = os.path.join(server_dir or os.path.dirname(conf_path), w)
    return w


def parse_duck_script(path):
    try:
        with open(path, errors="replace") as f:
            text = f.read(16384)
    except OSError:
        return None
    if "duckdns.org" not in text:
        return None
    dm = re.search(r"domains=([A-Za-z0-9.,_-]+)", text)
    tm = re.search(r"token=([A-Za-z0-9-]{16,})", text)
    if not dm or not tm:
        return None
    domain = dm.group(1).split(",")[0]
    if domain.endswith(".duckdns.org"):
        domain = domain[: -len(".duckdns.org")]
    if not domain:
        return None
    return {"script": path, "domain": domain, "token": tm.group(1)}


# --- Auto-detection ----------------------------------------------------------
def scan_filesystem(max_depth=6, max_dirs=40000):
    found = {"vanilla": [], "tmodloader": [], "duckdns": [], "serverconfig": []}
    roots = []
    for r in (HOME, "/home", "/opt", "/srv", "/root"):
        if os.path.isdir(r) and r not in roots:
            roots.append(r)
    seen = set()
    count = 0
    for root in roots:
        base = root.rstrip(os.sep).count(os.sep)
        for dirpath, dirnames, filenames in os.walk(root, onerror=lambda e: None):
            try:
                real = os.path.realpath(dirpath)
            except OSError:
                dirnames[:] = []
                continue
            if real in seen:
                dirnames[:] = []
                continue
            seen.add(real)
            count += 1
            if count > max_dirs:
                return found
            depth = dirpath.rstrip(os.sep).count(os.sep) - base
            if depth >= max_depth:
                dirnames[:] = []
            else:
                dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in SKIP_DIRS]
            names = set(filenames)
            if VANILLA_BIN in names:
                found["vanilla"].append(real)
            if TMOD_SCRIPT in names:
                found["tmodloader"].append(real)
            for fn in filenames:
                low = fn.lower()
                p = os.path.join(real, fn)
                if low.endswith(".sh") and "duck" in low:
                    info = parse_duck_script(p)
                    if info:
                        found["duckdns"].append(info)
                elif low.startswith("serverconfig") and low.endswith(".txt"):
                    found["serverconfig"].append(p)
    return found


def pick_best_dir(dirs, kind):
    if not dirs:
        return None

    def key(d):
        try:
            mt = os.path.getmtime(d)
        except OSError:
            mt = 0
        return (version_tuple(detect_version(kind, d)), mt)

    return sorted(dirs, key=key)[-1]


def pick_serverconfig(paths, kind):
    best, best_score = None, -1
    for p in paths:
        cfg = parse_serverconfig(p)
        if "world" not in cfg and "autocreate" not in cfg:
            continue
        score = 1
        w = resolve_world_path(p, cfg.get("world"))
        if w and os.path.isfile(w):
            score += 10
            is_tmod = os.path.isfile(w[:-4] + ".twld") or "tmodloader" in w.lower()
            if (kind == "tmodloader") == is_tmod:
                score += 5
        if os.path.dirname(p) == HOME:
            score += 3
        if score > best_score:
            best, best_score = p, score
    return best


def valid_vanilla(d):
    return bool(d) and os.path.isfile(os.path.join(d, VANILLA_BIN))


def valid_tmod(d):
    return bool(d) and os.path.isfile(os.path.join(d, TMOD_SCRIPT))


# --- /proc readers -----------------------------------------------------------
def find_server_process():
    """Return (pid, kind) of the real game process, or (None, None)."""
    me = os.getpid()
    try:
        entries = sorted((int(n) for n in os.listdir("/proc") if n.isdigit()))
    except OSError:
        return None, None
    for pid in entries:
        if pid == me:
            continue
        try:
            with open(f"/proc/{pid}/cmdline", "rb") as f:
                raw = f.read()
        except OSError:
            continue
        args = [a.decode("utf-8", "replace") for a in raw.split(b"\0") if a]
        if not args:
            continue
        a0 = os.path.basename(args[0]).lower()
        if a0 in SHELL_NAMES or a0.startswith("python"):
            continue
        bases = [os.path.basename(a) for a in args]
        if a0.startswith("terrariaserver") or (
                a0.startswith("mono") and any(b.startswith("TerrariaServer") for b in bases)):
            return pid, "vanilla"
        if (a0.startswith("dotnet") and "tModLoader.dll" in bases) or a0.startswith("tmodloader"):
            return pid, "tmodloader"
    return None, None


def proc_cpu_ticks(pid):
    try:
        with open(f"/proc/{pid}/stat") as f:
            data = f.read()
        fields = data[data.rfind(")") + 2:].split()
        return int(fields[11]) + int(fields[12])
    except (OSError, ValueError, IndexError):
        return None


def proc_start_epoch(pid):
    try:
        with open(f"/proc/{pid}/stat") as f:
            data = f.read()
        start_ticks = int(data[data.rfind(")") + 2:].split()[19])
        with open("/proc/stat") as f:
            for line in f:
                if line.startswith("btime"):
                    return int(line.split()[1]) + start_ticks / CLK_TCK
    except (OSError, ValueError, IndexError):
        pass
    return None


def proc_rss(pid):
    try:
        with open(f"/proc/{pid}/status") as f:
            for line in f:
                if line.startswith("VmRSS:"):
                    return int(line.split()[1]) * 1024
    except (OSError, ValueError, IndexError):
        pass
    return None


def proc_cwd(pid):
    try:
        return os.readlink(f"/proc/{pid}/cwd")
    except OSError:
        return None


def read_cpu_totals():
    try:
        with open("/proc/stat") as f:
            parts = f.readline().split()
        vals = [int(x) for x in parts[1:]]
        idle = vals[3] + (vals[4] if len(vals) > 4 else 0)
        return sum(vals), idle
    except (OSError, ValueError, IndexError):
        return None


def read_mem():
    info = {}
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                k, v = line.split(":", 1)
                info[k] = int(v.split()[0]) * 1024
    except (OSError, ValueError, IndexError):
        return None, None
    return info.get("MemTotal"), info.get("MemAvailable")


def read_net():
    rx = tx = 0
    try:
        with open("/proc/net/dev") as f:
            lines = f.readlines()[2:]
        for line in lines:
            if ":" not in line:
                continue
            name, data = line.split(":", 1)
            if name.strip() == "lo":
                continue
            fields = data.split()
            rx += int(fields[0])
            tx += int(fields[8])
    except (OSError, ValueError, IndexError):
        return None
    return rx, tx


def port_listening(port):
    hexport = f":{int(port):04X}"
    for path in ("/proc/net/tcp", "/proc/net/tcp6"):
        try:
            with open(path) as f:
                next(f, None)
                for line in f:
                    parts = line.split()
                    if len(parts) > 3 and parts[1].endswith(hexport) and parts[3] == "0A":
                        return True
        except OSError:
            pass
    return False


def screen_session_exists(name):
    if not shutil.which("screen"):
        return False
    try:
        r = subprocess.run(["screen", "-ls"], capture_output=True, text=True, timeout=5)
    except (OSError, subprocess.SubprocessError):
        return False
    return re.search(r"\d+\." + re.escape(name) + r"\s", r.stdout) is not None


# --- Config ------------------------------------------------------------------
class Config:
    def __init__(self):
        self.lock = threading.RLock()
        self.data = json.loads(json.dumps(DEFAULTS))
        self.load_error = None
        self.load()

    def load(self):
        try:
            with open(CONF_PATH) as f:
                raw = json.load(f)
            if not isinstance(raw, dict):
                raise ValueError("config is not a JSON object")
            for k, v in raw.items():
                if k not in DEFAULTS:
                    continue
                d = DEFAULTS[k]
                if isinstance(d, bool):
                    ok = isinstance(v, bool)
                elif isinstance(d, (int, float)):
                    ok = isinstance(v, (int, float)) and not isinstance(v, bool) and v > 0
                elif isinstance(d, list):
                    ok = isinstance(v, list) and all(isinstance(x, str) for x in v)
                else:
                    ok = isinstance(v, str)
                if ok:
                    self.data[k] = v
        except FileNotFoundError:
            pass
        except Exception as e:
            self.load_error = f"config.json unreadable ({e}); using defaults (old file kept as config.json.bad)"
            try:
                shutil.copy(CONF_PATH, CONF_PATH + ".bad")
            except OSError:
                pass

    def save(self):
        with self.lock:
            try:
                os.makedirs(CONF_DIR, exist_ok=True)
                tmp = CONF_PATH + ".tmp"
                with open(tmp, "w") as f:
                    json.dump(self.data, f, indent=2)
                os.chmod(tmp, 0o600)  # holds the DuckDNS token
                os.replace(tmp, CONF_PATH)
                return None
            except OSError as e:
                return str(e)

    def __getitem__(self, k):
        with self.lock:
            return self.data[k]

    def __setitem__(self, k, v):
        with self.lock:
            self.data[k] = v

    def copy(self):
        with self.lock:
            return json.loads(json.dumps(self.data))


# --- Downloader --------------------------------------------------------------
class Cancelled(Exception):
    pass


class Downloader:
    def __init__(self, mon):
        self.mon = mon
        self.lock = threading.Lock()
        self.busy = False
        self.kind = None
        self.phase = "idle"
        self.got = 0
        self.total = None
        self.method = None
        self.started = None
        self.finished = None
        self.result = None
        self._cancel = False
        self._proc = None

    def snapshot(self):
        with self.lock:
            return dict(busy=self.busy, kind=self.kind, phase=self.phase, got=self.got,
                        total=self.total, method=self.method, started=self.started,
                        finished=self.finished, result=self.result)

    def _set(self, **kw):
        with self.lock:
            for k, v in kw.items():
                setattr(self, k, v)

    def _check_cancel(self):
        if self._cancel:
            raise Cancelled()

    def start(self, kind):
        with self.lock:
            if self.busy:
                self.mon.log("WARN", "A download is already running - press C to cancel it first.")
                return
            self.busy, self.kind, self.phase = True, kind, "starting"
            self.got, self.total, self.method = 0, None, None
            self.started, self.finished, self.result = time.time(), None, None
            self._cancel = False
        threading.Thread(target=self._run, args=(kind,), daemon=True).start()

    def cancel(self):
        with self.lock:
            if not self.busy:
                self.mon.log("INFO", "No download is running.")
                return
            self._cancel = True
            p = self._proc
        if p and p.poll() is None:
            try:
                p.terminate()
            except OSError:
                pass

    def _run(self, kind):
        label = "Vanilla server" if kind == "vanilla" else "tModLoader"
        self.mon.log("INFO", f"Downloading latest {label}...")
        result = "error"
        try:
            if kind == "vanilla":
                self._install_vanilla()
            else:
                self._install_tmod()
            result = "done"
        except Cancelled:
            result = "cancelled"
            self.mon.log("WARN", "Download cancelled.")
        except Exception as e:
            self.mon.log("ERROR", f"{label} download failed: {describe_error(e)}")
        finally:
            with self.lock:
                self.busy = False
                self.result = result
                self.phase = result
                self.finished = time.time()
                self._proc = None

    def _install_vanilla(self):
        self._set(phase="checking latest version")
        data = json.loads(http_get(VANILLA_LIST_URL, timeout=20))
        names = sorted({n for n in data if isinstance(n, str)
                        and re.fullmatch(r"terraria-server-\d+\.zip", n)}, key=version_tuple)
        if not names:
            raise RuntimeError("terraria.org did not list any server versions")
        name = names[-1]
        digits = re.search(r"(\d+)", name).group(1)
        version = ".".join(digits)
        root = os.path.join(DOWNLOAD_ROOT, "vanilla")
        final = os.path.join(root, digits)
        linux = os.path.join(final, "Linux")
        if os.path.isfile(os.path.join(linux, VANILLA_BIN)):
            self.mon.log("INFO", f"Vanilla {version} is already installed at {linux}")
            self.mon.on_installed("vanilla", linux, version)
            return
        part = os.path.join(root, name + ".part")
        self._fetch(VANILLA_DL_URL.format(name=name), part)
        d = self._unpack(part, root, final, VANILLA_BIN, keep_top=True)
        for exe in (VANILLA_BIN, "TerrariaServer"):
            if os.path.isfile(os.path.join(d, exe)):
                make_executable(os.path.join(d, exe))
        write_marker(d, version)
        self.mon.on_installed("vanilla", d, version)

    def _install_tmod(self):
        self._set(phase="checking latest release")
        tag, dl_url, size = None, None, None
        try:
            rel = json.loads(http_get(TMOD_RELEASE_URL, timeout=20,
                                      headers={"Accept": "application/vnd.github+json"}))
            tag = str(rel.get("tag_name") or "").strip()
            asset = next((a for a in rel.get("assets", []) if a.get("name") == "tModLoader.zip"), None)
            if asset and str(asset.get("browser_download_url", "")).startswith("https://"):
                dl_url, size = asset["browser_download_url"], asset.get("size")
        except Exception as e:
            # GitHub's API allows only 60 requests/hour without login - use the plain redirect instead
            self.mon.log("INFO", f"GitHub API unavailable ({describe_error(e)}) - using release redirect.")
        if not tag or not dl_url:
            tag, dl_url = github_latest_via_redirect(TMOD_LATEST_DL)
        self._check_cancel()
        safe_tag = re.sub(r"[^A-Za-z0-9._-]", "_", tag)
        root = os.path.join(DOWNLOAD_ROOT, "tmodloader")
        final = os.path.join(root, safe_tag)
        if os.path.isfile(os.path.join(final, TMOD_SCRIPT)):
            self.mon.log("INFO", f"tModLoader {tag} is already installed at {final}")
            self.mon.on_installed("tmodloader", final, tag)
            return
        part = os.path.join(root, f"tModLoader-{safe_tag}.zip.part")
        self._fetch(dl_url, part, total_hint=size)
        d = self._unpack(part, root, final, TMOD_SCRIPT, keep_top=False)
        for dp, _, fns in os.walk(d):
            for fn in fns:
                if fn.endswith(".sh"):
                    make_executable(os.path.join(dp, fn))
        write_marker(d, tag)
        self.mon.on_installed("tmodloader", d, tag)

    def _fetch(self, url, part, total_hint=None):
        os.makedirs(os.path.dirname(part), exist_ok=True)
        try:
            os.remove(part)
        except FileNotFoundError:
            pass
        self._set(phase="connecting")
        total = total_hint if isinstance(total_hint, int) and total_hint > 0 else probe_size(url)
        self._check_cancel()
        free = shutil.disk_usage(os.path.dirname(part)).free
        need = (total or 150 * 1024 * 1024) * 3
        if free < need:
            raise RuntimeError(f"not enough disk space (need about {human_bytes(need)}, "
                               f"free {human_bytes(free)})")
        self._set(total=total, phase="downloading")
        try:
            done = False
            if self.mon.cfg["use_wget"]:
                if shutil.which("wget"):
                    done = self._fetch_wget(url, part)
                else:
                    self.mon.log("INFO", "wget is not installed - using the built-in Python downloader.")
            if not done:
                self._fetch_python(url, part)
            size = safe_getsize(part)
            if size == 0:
                raise RuntimeError("downloaded file is empty")
            if total and size != total:
                raise RuntimeError(f"incomplete download ({human_bytes(size)} of {human_bytes(total)})")
        except BaseException:
            try:
                os.remove(part)
            except OSError:
                pass
            raise

    def _fetch_wget(self, url, part):
        self._set(method="wget")
        errlog = part + ".wget.log"
        cmd = ["wget", "-4", "--tries=3", "--timeout=30", "--no-verbose",
               "--user-agent", UA, "-O", part, url]
        try:
            with open(errlog, "w") as ef:
                with self.lock:
                    self._check_cancel()
                    p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=ef)
                    self._proc = p
                while p.poll() is None:
                    if self._cancel:
                        try:
                            p.terminate()
                            p.wait(10)
                        except (OSError, subprocess.SubprocessError):
                            p.kill()
                        raise Cancelled()
                    self._set(got=safe_getsize(part))
                    time.sleep(0.25)
            self._set(got=safe_getsize(part))
            self._check_cancel()
            if p.returncode == 0:
                return True
            try:
                with open(errlog, errors="replace") as ef:
                    tail = " ".join(ef.read().split())[-200:]
            except OSError:
                tail = ""
            if p.returncode == 2:
                self.mon.log("WARN", "This wget doesn't support the options used - falling back to Python.")
                return False
            raise RuntimeError(f"wget failed: {WGET_ERRORS.get(p.returncode, f'exit code {p.returncode}')}"
                               + (f" ({tail})" if tail else ""))
        finally:
            try:
                os.remove(errlog)
            except OSError:
                pass

    def _fetch_python(self, url, part):
        self._set(method="python", got=0)
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=30) as r, open(part, "wb") as f:
            got = 0
            while True:
                self._check_cancel()
                chunk = r.read(256 * 1024)
                if not chunk:
                    break
                f.write(chunk)
                got += len(chunk)
                self._set(got=got)

    def _unpack(self, part, root, final, needle, keep_top):
        self._set(phase="verifying")
        self._check_cancel()
        if not zipfile.is_zipfile(part):
            raise RuntimeError("downloaded file is not a valid zip (the site may have returned an error page)")
        tmp = os.path.join(root, f".extract-{os.getpid()}")
        shutil.rmtree(tmp, ignore_errors=True)
        os.makedirs(tmp)
        try:
            self._set(phase="extracting")
            safe_extract(part, tmp)
            hit = None
            for dp, _, fns in os.walk(tmp):
                if needle in fns:
                    hit = dp
                    break
            if not hit:
                raise RuntimeError(f"{needle} was not found inside the zip")
            rel = os.path.relpath(hit, tmp)
            parts = [] if rel == "." else rel.split(os.sep)
            if keep_top and len(parts) >= 2:
                source = os.path.join(tmp, parts[0])
            elif keep_top:
                source = tmp
            else:
                source = hit
            if os.path.exists(final):
                os.replace(final, f"{final}.old-{int(time.time())}")
            shutil.move(source, final)
            inside = os.path.relpath(hit, source)
            return final if inside == "." else os.path.join(final, inside)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
            try:
                os.remove(part)
            except OSError:
                pass


# --- Monitor (all the logic; no UI) ------------------------------------------
class Monitor:
    def __init__(self, cfg, headless=False):
        self.cfg = cfg
        self.headless = headless
        self.lock = threading.RLock()
        self.stop_event = threading.Event()
        self.server_wake = threading.Event()
        self.net_wake = threading.Event()
        self.events = deque(maxlen=300)
        self._last_msg = {}
        self.s = dict(
            pid=None, proc_kind=None, state="CHECKING", listening=False, screen_alive=False,
            port=None, uptime=None, cpu_proc=None, rss=None, cpu_sys=None,
            mem_total=None, mem_avail=None, rx_rate=None, tx_rate=None, rx_total=None,
            tx_total=None, public_ip=None, public_ip_time=None, public_ip_ok=False,
            duck_ip=None, duck_status="checking...", duck_level="warn", duck_last_update=None,
            duck_last_result=None, world=None, version=None, server_dir=None, scanning=False,
        )
        self.manual_stop = False
        self.start_requested = False
        self.restart_requested = False
        self.stopping_since = None
        self.duck_force = False
        self.restart_times = deque()
        self.last_start_attempt = 0.0
        self.next_start_allowed = 0.0
        self.our_launch_time = None
        self.first_seen = {}
        self._was_running = None
        self._launch_pending = False
        self._prev_proc = None
        self._prev_cpu = None
        self._prev_net = None
        self.duck_updated_ip = None
        self.duck_updated_at = 0.0
        self.downloader = Downloader(self)
        self.threads = []
        self._rotate_app_log()
        if cfg.load_error:
            self.log("ERROR", cfg.load_error)
        if hasattr(os, "geteuid") and os.geteuid() == 0:
            self.log("WARN", "Running as root. Recommended: run TerraMon as the 'terraria' user.")

    # ---- logging
    def _rotate_app_log(self):
        try:
            os.makedirs(STATE_DIR, exist_ok=True)
            if safe_getsize(APP_LOG) > 1_000_000:
                os.replace(APP_LOG, APP_LOG + ".1")
        except OSError:
            pass

    def redact(self, msg):
        tok = self.cfg["duckdns_token"]
        return msg.replace(tok, "***") if tok and len(tok) > 4 else msg

    def log(self, level, msg, key=None, every=0):
        msg = self.redact(str(msg))
        t = time.time()
        if key and every:
            with self.lock:
                if t - self._last_msg.get(key, 0) < every:
                    return
                self._last_msg[key] = t
        with self.lock:
            self.events.append((t, level, msg))
        line = f"{datetime.fromtimestamp(t):%Y-%m-%d %H:%M:%S} [{level}] {msg}"
        try:
            with open(APP_LOG, "a") as f:
                f.write(line + "\n")
        except OSError:
            pass
        if self.headless:
            print(line, flush=True)

    # ---- detection
    def rescan(self, announce=True):
        with self.lock:
            if self.s["scanning"]:
                return
            self.s["scanning"] = True
        try:
            if announce:
                self.log("INFO", "Scanning for server / DuckDNS folders...")
            found = scan_filesystem()
            self.apply_detection(found, announce)
        except Exception as e:
            self.log("ERROR", f"Folder scan failed: {describe_error(e)}")
        finally:
            with self.lock:
                self.s["scanning"] = False

    def apply_detection(self, found, announce=True):
        c = self.cfg
        changed = []
        if not valid_vanilla(c["vanilla_dir"]):
            best = pick_best_dir(found["vanilla"], "vanilla")
            if best:
                c["vanilla_dir"] = best
                changed.append(f"vanilla server -> {best}")
        if not valid_tmod(c["tmod_dir"]):
            best = pick_best_dir(found["tmodloader"], "tmodloader")
            if best:
                c["tmod_dir"] = best
                changed.append(f"tModLoader -> {best}")
        for kind, key in (("vanilla", "vanilla_serverconfig"), ("tmodloader", "tmod_serverconfig")):
            if not os.path.isfile(c[key] or ""):
                best = pick_serverconfig(found["serverconfig"], kind)
                if best:
                    c[key] = best
                    changed.append(f"{kind} serverconfig -> {best}")
        if not (c["duckdns_domain"] and c["duckdns_token"]) and found["duckdns"]:
            infos = sorted(found["duckdns"], key=lambda i: not i["script"].startswith(HOME))
            info = infos[0]
            c["duckdns_domain"], c["duckdns_token"], c["duckdns_script"] = (
                info["domain"], info["token"], info["script"])
            changed.append(f"DuckDNS -> {info['domain']}.duckdns.org ({info['script']})")
        if changed:
            err = c.save()
            for m in changed:
                self.log("INFO", f"Auto-detected {m}")
            if err:
                self.log("ERROR", f"Could not save config: {err}")
        elif announce:
            self.log("INFO", "Scan finished - nothing new found.")
        if not valid_vanilla(c["vanilla_dir"]) and not valid_tmod(c["tmod_dir"]):
            self.log("WARN", "No Terraria server found. Press D to download one.")
        if not (c["duckdns_domain"] and c["duckdns_token"]):
            self.log("WARN", "DuckDNS not found (no duck.sh). Set duckdns_domain/token in config.json.")
        self.net_wake.set()
        self.server_wake.set()

    def resolve_kind(self):
        with self.lock:
            pk = self.s["proc_kind"]
        if pk:
            return pk
        a = self.cfg["active_server"]
        if a in ("vanilla", "tmodloader"):
            return a
        if valid_vanilla(self.cfg["vanilla_dir"]):
            return "vanilla"
        if valid_tmod(self.cfg["tmod_dir"]):
            return "tmodloader"
        return "vanilla"

    def kind_paths(self, kind):
        if kind == "tmodloader":
            return self.cfg["tmod_dir"], self.cfg["tmod_serverconfig"]
        return self.cfg["vanilla_dir"], self.cfg["vanilla_serverconfig"]

    def current_port(self, kind):
        _, conf = self.kind_paths(kind)
        p = parse_serverconfig(conf).get("port") if conf else None
        try:
            port = int(p) if p else int(self.cfg["port"])
            return port if 0 < port < 65536 else 7777
        except (TypeError, ValueError):
            return 7777

    # ---- server control
    def request_start(self):
        with self.lock:
            self.manual_stop = False
            self.start_requested = True
            self.next_start_allowed = 0
        self.server_wake.set()

    def stop_server(self, restart=False):
        session = self.cfg["screen_session"]
        with self.lock:
            pid = self.s["pid"]
        if not pid and not screen_session_exists(session):
            if restart:
                self.log("INFO", "Server was not running - starting it.")
                self.request_start()
            else:
                self.log("INFO", "Server is not running.")
            return
        if not screen_session_exists(session):
            self.log("ERROR", f"Server is running but not in a screen session named '{session}', "
                              "so TerraMon can't send it 'exit'. Stop it manually (type exit in its console).")
            return
        try:
            subprocess.run(["screen", "-S", session, "-p", "0", "-X", "stuff", "exit\r"],
                           capture_output=True, timeout=10)
        except (OSError, subprocess.SubprocessError) as e:
            self.log("ERROR", f"Could not send 'exit' to the server: {describe_error(e)}")
            return
        with self.lock:
            self.manual_stop = not restart
            self.restart_requested = restart
            self.stopping_since = time.time()
            self.next_start_allowed = 0
        self.log("INFO", "Sent 'exit' to the server (it saves the world, then closes)."
                 + (" It will start again after it stops." if restart else ""))
        self.server_wake.set()

    def toggle_auto_restart(self):
        self.cfg["auto_restart"] = not self.cfg["auto_restart"]
        if self.cfg["auto_restart"]:
            with self.lock:
                self.restart_times.clear()
                self.manual_stop = False
        self._save_cfg()
        self.log("INFO", f"Auto-restart {'ON' if self.cfg['auto_restart'] else 'OFF'}")
        self.server_wake.set()

    def toggle_kind(self):
        new = "tmodloader" if self.resolve_kind() == "vanilla" else "vanilla"
        self.cfg["active_server"] = new
        self._save_cfg()
        name = "tModLoader" if new == "tmodloader" else "Vanilla"
        with self.lock:
            running = self.s["pid"] is not None
        self.log("INFO", f"Server type set to {name}." + (" Press X to restart onto it." if running else ""))
        self.server_wake.set()

    def force_duck_update(self):
        with self.lock:
            self.duck_force = True
        self.log("INFO", "DuckDNS update requested.")
        self.net_wake.set()

    def _save_cfg(self):
        err = self.cfg.save()
        if err:
            self.log("ERROR", f"Could not save config: {err}")

    def on_installed(self, kind, d, version):
        key = "tmod_dir" if kind == "tmodloader" else "vanilla_dir"
        self.cfg[key] = d
        self._save_cfg()
        name = "tModLoader" if kind == "tmodloader" else "Vanilla"
        self.log("INFO", f"{name} {version} ready at {d}")
        with self.lock:
            running = self.s["pid"] is not None
        if self.resolve_kind() != kind:
            self.log("INFO", f"Press T to switch the server type to {name}.")
        elif running:
            self.log("INFO", "Press X to restart the server on the new version.")
        if kind == "tmodloader" and not os.path.isfile(self.cfg["tmod_serverconfig"] or ""):
            self.log("WARN", "No serverconfig set for tModLoader - set tmod_serverconfig in config.json.")
        self.server_wake.set()

    def _validate_launch(self, kind):
        """Return (cmd, cwd) or (None, reason)."""
        d, conf = self.kind_paths(kind)
        name = "tModLoader" if kind == "tmodloader" else "Vanilla server"
        if kind == "vanilla":
            if not valid_vanilla(d):
                return None, f"{name} not found - press D to download it or R to rescan."
            exe = os.path.join(d, VANILLA_BIN)
            if not os.access(exe, os.X_OK) and not make_executable(exe):
                return None, f"{exe} is not executable and chmod failed (check file owner)."
            cmd = [exe]
        else:
            if not valid_tmod(d):
                return None, f"{name} not found - press D to download it or R to rescan."
            for dp, _, fns in os.walk(d):
                for fn in fns:
                    if fn.endswith(".sh"):
                        make_executable(os.path.join(dp, fn))
            cmd = ["bash", os.path.join(d, TMOD_SCRIPT)] + list(self.cfg["tmod_extra_args"])
        if not conf or not os.path.isfile(conf):
            return None, (f"No serverconfig for {name}. Create one (e.g. ~/serverconfig.txt) "
                          "and press R, or set it in config.json.")
        sc = parse_serverconfig(conf)
        world = sc.get("world")
        if world:
            if world.startswith("~"):
                return None, f"world= in {conf} uses '~'. Terraria can't read that - use the full path."
            w = resolve_world_path(conf, world, d)
            if not os.path.isfile(w):
                return None, f"World file not found: {w} (from {conf})"
            if not os.access(w, os.R_OK | os.W_OK):
                return None, f"No read/write permission on world file {w} (chown it to this user)."
        elif "autocreate" not in sc:
            return None, f"{conf} has no world= line - the server would wait for input forever."
        return cmd + ["-config", conf], d

    def start_server(self, kind):
        session = self.cfg["screen_session"]
        if not shutil.which("screen"):
            self.log("ERROR", "'screen' is not installed. As root run: apt install screen",
                     key="noscreen", every=300)
            return False
        cmd, cwd = self._validate_launch(kind)
        if cmd is None:
            self.log("ERROR", f"Can't start server: {cwd}", key="launch:" + cwd, every=300)
            return False
        try:
            os.makedirs(STATE_DIR, exist_ok=True)
            if os.path.exists(SERVER_LOG):
                os.replace(SERVER_LOG, SERVER_LOG + ".1")
            with open(SCREENRC, "w") as f:
                f.write("logfile flush 1\n")
        except OSError as e:
            self.log("WARN", f"Could not prepare server log: {e}")
        attempts = [
            ["screen", "-c", SCREENRC, "-L", "-Logfile", SERVER_LOG, "-dmS", session] + cmd,
            ["screen", "-dmS", session] + cmd,
        ]
        last_err = ""
        for i, full in enumerate(attempts):
            try:
                r = subprocess.run(full, cwd=cwd, capture_output=True, text=True, timeout=15)
            except (OSError, subprocess.SubprocessError) as e:
                last_err = describe_error(e)
                continue
            if r.returncode == 0:
                if i == 1:
                    self.log("WARN", "Started without console logging (old screen version).")
                name = "tModLoader" if kind == "tmodloader" else "Vanilla"
                self.log("INFO", f"Started {name} server in screen session '{session}' "
                                 f"(view it: screen -r {session}).")
                with self.lock:
                    self.our_launch_time = time.time()
                self._launch_pending = True
                return True
            last_err = (r.stderr or r.stdout or f"exit code {r.returncode}").strip()[:200]
        self.log("ERROR", f"screen failed to start the server: {last_err}", key="screenfail", every=120)
        return False

    # ---- periodic work
    def server_tick(self):
        t = time.time()
        pid, kind = find_server_process()
        session = self.cfg["screen_session"]
        screen_alive = screen_session_exists(session)
        active = kind or self.resolve_kind()
        port = self.current_port(active)
        listening = port_listening(port)

        upd = dict(pid=pid, proc_kind=kind, screen_alive=screen_alive, port=port, listening=listening)

        # system stats
        c = read_cpu_totals()
        if c and self._prev_cpu:
            dt, di = c[0] - self._prev_cpu[0], c[1] - self._prev_cpu[1]
            upd["cpu_sys"] = max(0.0, min(100.0, 100.0 * (1 - di / dt))) if dt > 0 else None
        self._prev_cpu = c
        upd["mem_total"], upd["mem_avail"] = read_mem()
        n = read_net()
        if n:
            upd["rx_total"], upd["tx_total"] = n
            if self._prev_net:
                dt = t - self._prev_net[2]
                drx, dtx = n[0] - self._prev_net[0], n[1] - self._prev_net[1]
                if dt > 0 and drx >= 0 and dtx >= 0:
                    upd["rx_rate"], upd["tx_rate"] = drx / dt, dtx / dt
            self._prev_net = (n[0], n[1], t)

        # server process stats
        if pid:
            ticks = proc_cpu_ticks(pid)
            if ticks is not None and self._prev_proc and self._prev_proc[0] == pid:
                dt = t - self._prev_proc[2]
                upd["cpu_proc"] = max(0.0, (ticks - self._prev_proc[1]) / CLK_TCK / dt * 100) if dt > 0 else None
            else:
                upd["cpu_proc"] = None
            self._prev_proc = (pid, ticks, t) if ticks is not None else None
            upd["rss"] = proc_rss(pid)
            if pid not in self.first_seen:
                self.first_seen = {pid: t}
            start = proc_start_epoch(pid)
            if start is None or start > t + 5 or t - start > 10 * 365 * 86400:
                start = self.first_seen[pid]
            upd["uptime"] = t - start
            upd["server_dir"] = proc_cwd(pid) or self.kind_paths(kind)[0]
        else:
            self._prev_proc = None
            upd.update(cpu_proc=None, rss=None, uptime=None, server_dir=self.kind_paths(active)[0])

        d, conf = self.kind_paths(active)
        upd["version"] = detect_version(active, upd["server_dir"] or d) or detect_version(active, d)
        world = parse_serverconfig(conf).get("world") if conf else None
        upd["world"] = os.path.splitext(os.path.basename(world))[0] if world else None

        with self.lock:
            stopping = self.stopping_since is not None
            if pid:
                if stopping and t - self.stopping_since < 180:
                    state = "STOPPING"
                else:
                    state = "ONLINE" if listening else "STARTING"
            elif screen_alive:
                state = "STARTING"
            else:
                state = "OFFLINE"
                self.stopping_since = None
            upd["state"] = state
            self.s.update(upd)

        running = pid is not None
        if running:
            self._launch_pending = False
        down = not running and not screen_alive
        if down and (self._was_running or self._launch_pending):
            if self._was_running and (self.manual_stop or self.restart_requested):
                self.log("INFO", "Server stopped.")
            else:
                last = tail_lines(SERVER_LOG, 1) if self._launch_pending or self._was_running else None
                what = ("Server exited right after starting" if self._launch_pending and not self._was_running
                        else "Server stopped unexpectedly (crash or closed from its console)")
                self.log("ERROR", what + (f". Last log line: {last[0].strip()[:160]}" if last else
                                          ". Check SERVER LOG below."))
            self._launch_pending = False
        if self._was_running is False and running and state != "OFFLINE":
            self.log("INFO", f"Server process detected (PID {pid}).")
        self._was_running = running
        if running and listening:
            with self.lock:
                self.start_requested = False
        self._maybe_start(t, pid, screen_alive, listening, port, active)

    def _maybe_start(self, t, pid, screen_alive, listening, port, kind):
        grace = self.cfg["startup_grace"]
        if pid or screen_alive:
            with self.lock:
                olt = self.our_launch_time
            if screen_alive and not pid and olt and t - olt > grace:
                self.log("ERROR", f"Screen session is open but the server never started after {int(grace)}s. "
                                  f"Look at SERVER LOG or run: screen -r {self.cfg['screen_session']}",
                         key="stuck", every=600)
            return
        if self.downloader.snapshot()["phase"] == "extracting":
            return
        with self.lock:
            manual = self.start_requested or self.restart_requested
            auto = self.cfg["auto_restart"] and not self.manual_stop
            if not (manual or auto) or t < self.next_start_allowed:
                return
        if listening:
            self.log("ERROR", f"Port {port} is already used by another program - can't start Terraria.",
                     key="portbusy", every=300)
            with self.lock:
                self.next_start_allowed = t + 30
            return
        if not manual:
            while self.restart_times and t - self.restart_times[0] > self.cfg["restart_window"]:
                self.restart_times.popleft()
            if len(self.restart_times) >= self.cfg["max_restarts"]:
                self.cfg["auto_restart"] = False
                self._save_cfg()
                self.log("ERROR", f"Server stopped {len(self.restart_times)} times in "
                                  f"{int(self.cfg['restart_window'] // 60)} min - auto-restart turned OFF "
                                  "to avoid a crash loop. Fix the error in SERVER LOG, then press S.")
                return
        ok = self.start_server(kind)
        with self.lock:
            if ok:
                if not manual:
                    self.restart_times.append(t)
                self.start_requested = False
                self.restart_requested = False
                self.manual_stop = False
                self.next_start_allowed = t + 15
            else:
                self.start_requested = False
                self.restart_requested = False
                self.next_start_allowed = t + 60

    def net_tick(self, allow_update=True):
        t = time.time()
        ip, err = None, None
        for url in PUBLIC_IP_URLS:
            try:
                txt = http_get(url, timeout=8, max_bytes=64).strip()
                ipaddress.IPv4Address(txt)
                ip = txt
                break
            except Exception as e:
                err = f"{urllib.parse.urlparse(url).netloc}: {describe_error(e)}"
        with self.lock:
            old = self.s["public_ip"]
            if ip:
                self.s.update(public_ip=ip, public_ip_time=t, public_ip_ok=True)
            else:
                self.s["public_ip_ok"] = False
        if ip and old and ip != old:
            self.log("INFO", f"Public IP changed: {old} -> {ip}")
        if not ip:
            self.log("ERROR", f"Can't get public IP (no internet? check the container gateway). Last: {err}",
                     key="pubip", every=300)

        domain = (self.cfg["duckdns_domain"] or "").strip()
        token = (self.cfg["duckdns_token"] or "").strip()
        if domain.endswith(".duckdns.org"):
            domain = domain[: -len(".duckdns.org")]
        if not domain or not token:
            self._duck("not configured (press R to rescan)", "warn")
            return
        fqdn = f"{domain}.duckdns.org"
        dns_ip = None
        try:
            dns_ip = socket.getaddrinfo(fqdn, None, socket.AF_INET)[0][4][0]
        except Exception as e:
            self.log("WARN", f"Can't resolve {fqdn}: {describe_error(e)}", key="dnsres", every=300)
        with self.lock:
            self.s["duck_ip"] = dns_ip
            force = self.duck_force
            self.duck_force = False
        if not ip:
            self._duck("unknown (no public IP)", "warn")
            return
        if dns_ip == ip and not force:
            self._duck("IN SYNC", "ok")
            return
        if not allow_update:
            self._duck("OUT OF SYNC", "bad")
            return
        if not force and self.duck_updated_ip == ip and t - self.duck_updated_at < 900:
            self._duck("updated - waiting for DNS", "warn")
            return
        if not force and not self.cfg["auto_duckdns"]:
            self._duck("OUT OF SYNC (auto-update off)", "bad")
            return
        url = "https://www.duckdns.org/update?" + urllib.parse.urlencode(
            {"domains": domain, "token": token, "ip": ip})
        try:
            ans = http_get(url, timeout=20, max_bytes=64).strip()
        except Exception as e:
            ans = None
            msg = describe_error(e)
        with self.lock:
            self.s["duck_last_update"] = t
        if ans and ans.startswith("OK"):
            self.duck_updated_ip, self.duck_updated_at = ip, t
            with self.lock:
                self.s["duck_last_result"] = "OK"
            self._duck("updated - waiting for DNS" if dns_ip != ip else "IN SYNC", "ok")
            self.log("INFO", f"DuckDNS updated: {fqdn} -> {ip}")
        else:
            reason = ("DuckDNS answered KO - wrong token or subdomain" if ans and ans.startswith("KO")
                      else (f"unexpected answer '{ans}'" if ans else msg))
            with self.lock:
                self.s["duck_last_result"] = "FAILED"
            self._duck("update FAILED", "bad")
            self.log("ERROR", f"DuckDNS update failed: {reason}", key="duckfail", every=300)

    def _duck(self, status, level):
        with self.lock:
            self.s["duck_status"] = status
            self.s["duck_level"] = level

    # ---- threads
    def _loop(self, fn, wake, interval_key):
        while not self.stop_event.is_set():
            try:
                fn()
            except Exception as e:
                self.log("ERROR", f"Internal error in {fn.__name__}: {describe_error(e)}",
                         key="loop:" + fn.__name__, every=60)
            wake.wait(max(1, float(self.cfg[interval_key])))
            wake.clear()

    def start_threads(self):
        for fn, wake, key in ((self.server_tick, self.server_wake, "check_interval"),
                              (self.net_tick, self.net_wake, "ip_check_interval")):
            th = threading.Thread(target=self._loop, args=(fn, wake, key), daemon=True)
            th.start()
            self.threads.append(th)

    def shutdown(self):
        self.stop_event.set()
        self.server_wake.set()
        self.net_wake.set()

    def snapshot(self):
        with self.lock:
            s = dict(self.s)
            s["events"] = list(self.events)[-60:]
        s["dl"] = self.downloader.snapshot()
        s["cfg"] = self.cfg.copy()
        s["kind"] = self.resolve_kind()
        return s


# --- TUI ---------------------------------------------------------------------
ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[A-Za-z]|\x1b[()][A-Za-z0-9]|\x1b.")


def tail_lines(path, n, max_bytes=16384):
    try:
        with open(path, "rb") as f:
            f.seek(0, os.SEEK_END)
            size = f.tell()
            f.seek(max(0, size - max_bytes))
            data = f.read().decode("utf-8", "replace")
    except OSError:
        return None
    out = []
    for raw in data.replace("\r\n", "\n").split("\n"):
        line = ANSI_RE.sub("", raw.split("\r")[-1])
        line = "".join(ch for ch in line if ch >= " " or ch == "\t").replace("\t", "  ")
        if line.strip():
            out.append(line)
    return out[-n:]


class UI:
    KEYS = " S Start/Stop  X Restart  D Download  C Cancel dl  U Update DNS  A Auto  T Type  R Rescan  H Help  Q Quit "

    def __init__(self, mon):
        self.mon = mon
        self.scr = None
        self.mode = "main"
        self.ascii = "utf" not in (locale.getpreferredencoding(False) or "").lower()
        self.C = {}

    def run(self, stdscr):
        self.scr = stdscr
        try:
            curses.curs_set(0)
        except curses.error:
            pass
        self._init_colors()
        stdscr.keypad(True)
        stdscr.timeout(500)
        while True:
            try:
                self.draw()
            except Exception as e:
                self.mon.log("ERROR", f"Display error: {describe_error(e)}", key="draw", every=30)
            try:
                ch = stdscr.getch()
            except KeyboardInterrupt:
                ch = ord("q")
            if ch == -1 or ch == curses.KEY_RESIZE:
                continue
            if self.handle(ch) == "quit":
                return

    def _init_colors(self):
        for k in ("ok", "bad", "warn", "info", "head", "dim"):
            self.C[k] = 0
        self.C["head"] = curses.A_BOLD
        self.C["dim"] = curses.A_DIM
        try:
            if curses.has_colors():
                curses.start_color()
                try:
                    curses.use_default_colors()
                    bg = -1
                except curses.error:
                    bg = curses.COLOR_BLACK
                pairs = {"ok": curses.COLOR_GREEN, "bad": curses.COLOR_RED,
                         "warn": curses.COLOR_YELLOW, "info": curses.COLOR_CYAN}
                for i, (k, col) in enumerate(pairs.items(), start=1):
                    curses.init_pair(i, col, bg)
                    self.C[k] = curses.color_pair(i)
                self.C["head"] = self.C["info"] | curses.A_BOLD
        except curses.error:
            pass

    def clean(self, text):
        text = str(text)
        if self.ascii:
            text = text.encode("ascii", "replace").decode("ascii")
        return "".join(ch if ch >= " " else " " for ch in text)

    def put(self, y, x, text, attr=0):
        h, w = self.scr.getmaxyx()
        if y < 0 or y >= h or x >= w:
            return x
        t = self.clean(text)[: max(0, w - x - (1 if y == h - 1 else 0))]
        if t:
            try:
                self.scr.addstr(y, x, t, attr)
            except curses.error:
                pass
        return x + len(t)

    def row(self, y, segs, x=2):
        for text, attr in segs:
            x = self.put(y, x, text, attr)
        return y + 1

    def section(self, y, title):
        w = self.scr.getmaxyx()[1]
        self.put(y, 0, ("-- " + title + " ").ljust(w - 1, "-"), self.C["head"])
        return y + 1

    def draw(self):
        scr = self.scr
        scr.erase()
        h, w = scr.getmaxyx()
        if h < 20 or w < 64:
            self.put(0, 0, "Terminal too small - need at least 64x20. Please resize.", self.C["bad"])
            scr.refresh()
            return
        S = self.mon.snapshot()
        C = self.C
        cfg = S["cfg"]
        kind = S["kind"]
        kname = "tModLoader" if kind == "tmodloader" else "Vanilla"

        # title bar
        now = datetime.now().strftime("%Y-%m-%d %H:%M:%S ")
        self.put(0, 0, " " * (w - 1), curses.A_REVERSE)
        self.put(0, 0, f" {APP_NAME} {APP_VERSION} - Terraria Server Monitor", curses.A_REVERSE | curses.A_BOLD)
        self.put(0, max(0, w - len(now) - 1), now, curses.A_REVERSE)

        y = self.section(1, "SERVER")
        state = S["state"]
        scol = {"ONLINE": C["ok"], "STARTING": C["warn"], "STOPPING": C["warn"],
                "OFFLINE": C["bad"]}.get(state, C["warn"]) | curses.A_BOLD
        y = self.row(y, [("Status : ", 0), (f"[ {state} ]", scol), ("   Type: ", 0), (kname, C["info"]),
                         ("   Version: ", 0), (S["version"] or "unknown", C["info"])])
        port = S["port"]
        y = self.row(y, [("World  : ", 0), (S["world"] or "-", C["info"]),
                         ("   Port: ", 0), (f"{port} ", 0),
                         ("listening" if S["listening"] else "closed", C["ok"] if S["listening"] else C["dim"]),
                         ("   PID: ", 0), (str(S["pid"] or "-"), 0)])
        ar = cfg["auto_restart"]
        y = self.row(y, [("Uptime : ", 0), (human_duration(S["uptime"]), 0),
                         ("   Auto-restart: ", 0), ("ON" if ar else "OFF", C["ok"] if ar else C["bad"]),
                         (f"   Screen: {cfg['screen_session']}", 0),
                         (" (open)" if S["screen_alive"] else " (none)", C["dim"])])
        cp = "-" if S["cpu_proc"] is None else f"{S['cpu_proc']:.1f}%"
        cs = "-" if S["cpu_sys"] is None else f"{S['cpu_sys']:.1f}%"
        y = self.row(y, [("CPU    : ", 0), (f"server {cp}", C["info"]), (" (100% = 1 core)", C["dim"]),
                         (f"   system {cs}", 0)])
        mt, ma = S["mem_total"], S["mem_avail"]
        used = (mt - ma) if (mt and ma is not None) else None
        y = self.row(y, [("RAM    : ", 0), (f"server {human_bytes(S['rss'])}", C["info"]),
                         (f"   system {human_bytes(used)} / {human_bytes(mt)} used", 0)])

        y = self.section(y, "NETWORK")
        pip = S["public_ip"] or "unknown"
        y = self.row(y, [("Public IP : ", 0), (pip, C["ok"] if S["public_ip_ok"] else C["bad"]),
                         (f"   (checked {clock(S['public_ip_time'])})", C["dim"])])
        dom = cfg["duckdns_domain"]
        if dom:
            dom = dom if dom.endswith(".duckdns.org") else dom + ".duckdns.org"
        lvl = {"ok": C["ok"], "bad": C["bad"]}.get(S["duck_level"], C["warn"])
        y = self.row(y, [("DuckDNS   : ", 0), (dom or "-", 0), (" -> ", 0), (S["duck_ip"] or "?", C["info"]),
                         ("   ", 0), (f"[{S['duck_status']}]", lvl | curses.A_BOLD)])
        lr = S["duck_last_result"]
        y = self.row(y, [("DNS update: ", 0),
                         (f"last {clock(S['duck_last_update'])}" + (f" ({lr})" if lr else ""),
                          C["bad"] if lr == "FAILED" else 0),
                         ("   auto-update ", 0),
                         ("ON" if cfg["auto_duckdns"] else "OFF", C["ok"] if cfg["auto_duckdns"] else C["bad"])])
        y = self.row(y, [("Traffic   : ", 0),
                         (f"down {human_bytes(S['rx_rate'])}/s  up {human_bytes(S['tx_rate'])}/s", C["info"]),
                         (f"   total down {human_bytes(S['rx_total'])}  up {human_bytes(S['tx_total'])}", C["dim"])])

        y = self.section(y, "FOLDERS" + ("  (scanning...)" if S["scanning"] else ""))
        vd, td = cfg["vanilla_dir"], cfg["tmod_dir"]
        y = self.row(y, [("Vanilla    : ", 0), (vd, 0) if valid_vanilla(vd) else ("not found - press D", C["warn"])])
        y = self.row(y, [("tModLoader : ", 0), (td, 0) if valid_tmod(td) else ("not found - press D", C["warn"])])
        conf = cfg["tmod_serverconfig"] if kind == "tmodloader" else cfg["vanilla_serverconfig"]
        y = self.row(y, [("Config     : ", 0),
                         (conf, 0) if conf and os.path.isfile(conf) else ("not found", C["warn"])])
        ds = cfg["duckdns_script"]
        y = self.row(y, [("DuckDNS    : ", 0),
                         (ds, 0) if ds else (("set in config.json", 0) if dom else ("not found", C["warn"]))])

        dl = S["dl"]
        if dl["busy"] or (dl["finished"] and time.time() - dl["finished"] < 30):
            y = self.section(y, "DOWNLOAD")
            y = self._draw_download(y, dl, w)

        # events + server log share the rest
        bottom = h - 1
        remaining = bottom - y
        ev_rows = max(3, min(8, remaining // 2))
        y = self.section(y, "EVENTS / ERRORS")
        events = S["events"][-(ev_rows):]
        for t, level, msg in events:
            col = {"ERROR": C["bad"] | curses.A_BOLD, "WARN": C["warn"]}.get(level, 0)
            y = self.row(y, [(f"{clock(t)} ", C["dim"]), (f"{level:<5} ", col), (msg, col)])
        if bottom - y >= 3:
            y = self.section(y, "SERVER LOG (last lines)")
            lines = tail_lines(SERVER_LOG, bottom - y)
            if lines is None:
                self.row(y, [("(no log yet - it appears when TerraMon starts the server)", C["dim"])])
            else:
                for line in lines:
                    y = self.row(y, [(line, 0)])

        self.put(h - 1, 0, self.KEYS.ljust(w - 1), curses.A_REVERSE)
        if self.mode != "main":
            self._draw_dialog(S)
        scr.refresh()

    def _draw_download(self, y, dl, w):
        C = self.C
        what = "tModLoader" if dl["kind"] == "tmodloader" else "Vanilla server"
        got, total = dl["got"], dl["total"]
        el = max(0.001, (dl["finished"] or time.time()) - (dl["started"] or time.time()))
        speed = got / el if got else 0
        if total:
            frac = max(0.0, min(1.0, got / total))
            barw = max(10, min(40, w - 60))
            fill = int(barw * frac)
            bar = "[" + "#" * fill + "." * (barw - fill) + f"] {frac * 100:5.1f}%"
            size = f" {human_bytes(got)} / {human_bytes(total)}"
        else:
            bar, size = "", f"{human_bytes(got)} downloaded"
        col = {"done": C["ok"], "error": C["bad"], "cancelled": C["warn"]}.get(dl["phase"], C["info"])
        y = self.row(y, [(f"{what}: ", 0), (dl["phase"], col | curses.A_BOLD),
                         (f"   via {dl['method']}" if dl["method"] else "", C["dim"])])
        return self.row(y, [(bar, C["info"]), (size, 0), (f"  {human_bytes(speed)}/s" if got else "", C["dim"])])

    def _draw_dialog(self, S):
        h, w = self.scr.getmaxyx()
        if self.mode == "download":
            lines = ["Download a server (latest version)", "",
                     "1  Vanilla Terraria dedicated server (terraria.org)",
                     "2  tModLoader server (GitHub)", "",
                     f"Installs into {DOWNLOAD_ROOT}/  using " +
                     ("wget" if S["cfg"]["use_wget"] and shutil.which("wget") else "Python"),
                     "", "Esc  cancel"]
        elif self.mode == "confirm_stop":
            lines = ["Stop the server?", "", "It will save the world and close.",
                     "Auto-restart will NOT start it again until you press S.", "", "Y  yes     N  no"]
        elif self.mode == "confirm_restart":
            lines = ["Restart the server?", "", "It saves the world, closes, then starts again.", "",
                     "Y  yes     N  no"]
        elif self.mode == "confirm_quit":
            lines = ["A download is still running.", "Quit anyway? (download will be cancelled)", "",
                     "Y  yes     N  no"]
        else:
            lines = ["TerraMon help", "",
                     "S  start / stop the server (stop = sends 'exit', world is saved)",
                     "X  restart the server (e.g. after downloading a new version)",
                     "D  download latest Vanilla or tModLoader server",
                     "C  cancel the running download",
                     "U  force a DuckDNS update now",
                     "A  toggle auto-restart (starts server whenever it is down)",
                     "T  switch server type Vanilla <-> tModLoader",
                     "R  rescan folders for servers / duck.sh / serverconfig",
                     "Q  quit TerraMon (the Terraria server keeps running)", "",
                     f"Settings: {CONF_PATH}",
                     f"Logs    : {STATE_DIR}/", "",
                     "Any key to close"]
        bw = min(w - 2, max(len(line) for line in lines) + 6)
        bh = min(h - 2, len(lines) + 2)
        y0, x0 = max(0, (h - bh) // 2), max(0, (w - bw) // 2)
        for i in range(bh):
            self.put(y0 + i, x0, " " * bw, curses.A_REVERSE)
        for i, line in enumerate(lines[: bh - 2]):
            attr = curses.A_REVERSE | (curses.A_BOLD if i == 0 else 0)
            self.put(y0 + 1 + i, x0 + 3, line[: bw - 6], attr)

    def handle(self, ch):
        try:
            key = chr(ch).lower() if 0 <= ch < 256 else ""
        except ValueError:
            key = ""
        m = self.mon
        if self.mode == "download":
            self.mode = "main"
            if key == "1":
                m.downloader.start("vanilla")
            elif key == "2":
                m.downloader.start("tmodloader")
            return None
        if self.mode in ("confirm_stop", "confirm_restart", "confirm_quit"):
            mode, self.mode = self.mode, "main"
            if key == "y":
                if mode == "confirm_stop":
                    m.stop_server(restart=False)
                elif mode == "confirm_restart":
                    m.stop_server(restart=True)
                else:
                    m.downloader.cancel()
                    return "quit"
            return None
        if self.mode == "help":
            self.mode = "main"
            return None
        if key == "q":
            if m.downloader.snapshot()["busy"]:
                self.mode = "confirm_quit"
            else:
                return "quit"
        elif key == "s":
            with m.lock:
                up = m.s["pid"] is not None or m.s["screen_alive"]
            if up:
                self.mode = "confirm_stop"
            else:
                m.log("INFO", "Start requested.")
                m.request_start()
        elif key == "x":
            self.mode = "confirm_restart"
        elif key == "d":
            self.mode = "download"
        elif key == "c":
            m.downloader.cancel()
        elif key == "u":
            m.force_duck_update()
        elif key == "a":
            m.toggle_auto_restart()
        elif key == "t":
            m.toggle_kind()
        elif key == "r":
            threading.Thread(target=m.rescan, daemon=True).start()
        elif key in ("h", "?"):
            self.mode = "help"
        return None


# --- Entry points ------------------------------------------------------------
def print_status(mon):
    s = mon.snapshot()
    cfg = s["cfg"]
    print(f"Server     : {s['state']}  type={s['kind']}  version={s['version'] or 'unknown'}  "
          f"pid={s['pid'] or '-'}  port={s['port']} ({'listening' if s['listening'] else 'closed'})")
    print(f"World      : {s['world'] or '-'}   uptime={human_duration(s['uptime'])}")
    print(f"CPU / RAM  : server {s['cpu_proc'] if s['cpu_proc'] is not None else '-'}%  "
          f"rss={human_bytes(s['rss'])}  system RAM {human_bytes((s['mem_total'] or 0) - (s['mem_avail'] or 0))}"
          f" / {human_bytes(s['mem_total'])}")
    print(f"Public IP  : {s['public_ip'] or 'unknown'}")
    print(f"DuckDNS    : {cfg['duckdns_domain'] or '-'} -> {s['duck_ip'] or '?'}  [{s['duck_status']}]")
    print(f"Folders    : vanilla={cfg['vanilla_dir'] or '-'}")
    print(f"             tmod={cfg['tmod_dir'] or '-'}")
    print(f"             config={cfg['vanilla_serverconfig'] or '-'}")
    print(f"             duck={cfg['duckdns_script'] or '-'}")
    errs = [e for e in s["events"] if e[1] in ("ERROR", "WARN")]
    for t, lvl, msg in errs[-10:]:
        print(f"{lvl:<5}      : {msg}")


def run_headless(mon):
    stop = threading.Event()
    signal.signal(signal.SIGTERM, lambda *a: stop.set())
    signal.signal(signal.SIGINT, lambda *a: stop.set())
    mon.start_threads()
    mon.log("INFO", f"{APP_NAME} running headless. Ctrl+C / SIGTERM to exit (the server keeps running).")
    while not stop.wait(1):
        pass
    mon.shutdown()


def main():
    ap = argparse.ArgumentParser(description="Terraria server monitor")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--headless", action="store_true", help="run without UI (for systemd)")
    g.add_argument("--status", action="store_true", help="print status once and exit")
    g.add_argument("--scan", action="store_true", help="print auto-detection results and exit")
    args = ap.parse_args()

    try:
        os.makedirs(STATE_DIR, exist_ok=True)
    except OSError as e:
        print(f"Cannot create {STATE_DIR}: {e}", file=sys.stderr)
        sys.exit(1)
    locale.setlocale(locale.LC_ALL, "")
    cfg = Config()

    if args.scan:
        found = scan_filesystem()
        print("Vanilla servers :", *(found["vanilla"] or ["(none)"]), sep="\n  ")
        print("tModLoader      :", *(found["tmodloader"] or ["(none)"]), sep="\n  ")
        print("serverconfig    :", *(found["serverconfig"] or ["(none)"]), sep="\n  ")
        print("DuckDNS scripts :", *([f"{i['script']}  ({i['domain']}.duckdns.org)" for i in found["duckdns"]]
                                    or ["(none)"]), sep="\n  ")
        print("\nWould use:")
        print("  vanilla :", pick_best_dir(found["vanilla"], "vanilla"))
        print("  tmod    :", pick_best_dir(found["tmodloader"], "tmodloader"))
        print("  config  :", pick_serverconfig(found["serverconfig"], "vanilla"))
        return

    mon = Monitor(cfg, headless=args.headless or args.status)
    if args.status:
        mon.headless = False
        mon.rescan(announce=False)
        mon.server_tick()
        time.sleep(1)
        mon.server_tick()
        mon.net_tick(allow_update=False)
        print_status(mon)
        return

    lock_file = open(LOCK_PATH, "w")
    try:
        fcntl.flock(lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("TerraMon is already running (another terminal or the systemd service).", file=sys.stderr)
        sys.exit(1)

    print("TerraMon: scanning for server folders...", flush=True)
    mon.rescan(announce=False)

    if args.headless:
        run_headless(mon)
        return
    if not sys.stdout.isatty():
        print("Not a terminal. Use --headless to run without the UI.", file=sys.stderr)
        sys.exit(1)
    mon.start_threads()
    try:
        curses.wrapper(UI(mon).run)
    finally:
        mon.shutdown()
    print("TerraMon closed. The Terraria server (if running) keeps running in screen.")


if __name__ == "__main__":
    main()
