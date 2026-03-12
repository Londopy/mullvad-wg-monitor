"""
Mullvad WireGuard Latency Monitor  v2.0
───────────────────────────────────────
Features:
  • Multi-region support (LAX, NYC, SEA, CHI, ATL, DAL, MIA)
  • Per-packet ping animation with live row updates
  • Jitter column (max - min)
  • Ping count slider (2–20 packets)
  • Threshold alerts (highlight + notification)
  • Export results to CSV / JSON
  • Copy best server to clipboard
  • Historical graphing (SQLite, time-series per server)
  • Side-by-side run comparison with delta column
  • Traceroute tab with hop visualisation
  • Speed test (HTTP throughput to nearest datacenter)
  • Dark / light theme toggle
  • Auto-ping on a configurable schedule
  • System tray mode (pystray + Pillow)
  • "Best server" auto-connect via Mullvad CLI
  • Seaborn statistics dashboard
  • Interactive Folium map with user location
"""

# ── STDLIB ────────────────────────────────────────────────────────────────────
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import threading
import subprocess
import platform
import re
import webbrowser
import tempfile
import urllib.request
import urllib.parse
import urllib.error
import json
import math
import csv
import sqlite3
import time
import os
import sys
import copy
from pathlib import Path
from datetime import datetime

# ── THIRD-PARTY ───────────────────────────────────────────────────────────────
import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
import matplotlib.gridspec as gridspec
import matplotlib.patches as mpatches
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import seaborn as sns
import pandas as pd
import numpy as np
import folium

try:
    import pystray
    from PIL import Image, ImageDraw
    TRAY_AVAILABLE = True
except ImportError:
    TRAY_AVAILABLE = False

# ── DATABASE PATH ─────────────────────────────────────────────────────────────
DB_DIR  = Path.home() / ".mullvad_ping"
DB_DIR.mkdir(exist_ok=True)
DB_PATH = DB_DIR / "history.db"

# ── THEME SYSTEM ──────────────────────────────────────────────────────────────
DARK = {
    "bg":      "#0d1117", "bg2":   "#161b22", "bg3":   "#21262d", "bg4": "#2d333b",
    "fg":      "#e6edf3", "fg_dim":"#8b949e", "fg_dark":"#484f58",
    "accent":  "#00e5ff", "green": "#7ee787", "red":   "#f85149",
    "yellow":  "#e3b341", "orange":"#ff9500", "purple":"#bc8cff",
    "sel_bg":  "#21262d", "sel_fg":"#00e5ff",
    "entry_bg":"#21262d", "entry_hl":"#00e5ff",
    "name":    "dark",
}
LIGHT = {
    "bg":      "#f6f8fa", "bg2":   "#ffffff",  "bg3":  "#eaeef2", "bg4": "#d0d7de",
    "fg":      "#1f2328", "fg_dim":"#636e7b",  "fg_dark":"#adbac7",
    "accent":  "#0969da", "green": "#1a7f37",  "red":  "#cf222e",
    "yellow":  "#9a6700", "orange":"#bc4c00",  "purple":"#8250df",
    "sel_bg":  "#ddf4ff", "sel_fg":"#0969da",
    "entry_bg":"#ffffff", "entry_hl":"#0969da",
    "name":    "light",
}
T = dict(DARK)   # mutable current theme — mutated in place on toggle

MONO = ("Courier New", 10)
UI   = ("Segoe UI",    10)

# ── REGION & SERVER DEFINITIONS ───────────────────────────────────────────────
def _s(city, *ranges):
    """Build server hostname list from (start, end) range tuples."""
    out = []
    for lo, hi in ranges:
        out += [f"us-{city}-wg-{str(n).zfill(3)}.relays.mullvad.net" for n in range(lo, hi+1)]
    return out

REGIONS = {
    "Los Angeles": {
        "code":    "lax",
        "center":  [33.95, -118.25],
        "zoom":    10,
        "servers": _s("lax", (1,8),(201,203),(402,409),(601,608),(701,704)),
        "datacenters": {
            "LAX-A": {"lat":34.0522,"lon":-118.2437,"color":"#00e5ff",
                      "location":"CoreSite LA1 — Downtown LA",
                      "ranges":[(1,8)]},
            "LAX-B": {"lat":33.9425,"lon":-118.4081,"color":"#7ee787",
                      "location":"Equinix LA3 — El Segundo",
                      "ranges":[(201,203)]},
            "LAX-C": {"lat":34.1808,"lon":-118.3090,"color":"#e3b341",
                      "location":"Zayo Burbank",
                      "ranges":[(402,409)]},
            "LAX-D": {"lat":33.6846,"lon":-117.8265,"color":"#f78166",
                      "location":"Equinix LA4 — Irvine",
                      "ranges":[(601,608)]},
            "LAX-E": {"lat":33.7701,"lon":-118.1937,"color":"#bc8cff",
                      "location":"CoreSite LA2 — Long Beach",
                      "ranges":[(701,704)]},
        },
    },
    "New York": {
        "code":    "nyc",
        "center":  [40.73, -73.95],
        "zoom":    10,
        "servers": _s("nyc", (1,8),(201,205),(401,408),(601,606)),
        "datacenters": {
            "NYC-A": {"lat":40.7589,"lon":-73.9851,"color":"#00e5ff",
                      "location":"Equinix NY9 — Manhattan",
                      "ranges":[(1,8)]},
            "NYC-B": {"lat":40.6892,"lon":-74.0445,"color":"#7ee787",
                      "location":"Zayo NYC — Jersey City",
                      "ranges":[(201,205)]},
            "NYC-C": {"lat":40.7282,"lon":-73.7949,"color":"#e3b341",
                      "location":"Equinix NY5 — Secaucus",
                      "ranges":[(401,408)]},
            "NYC-D": {"lat":40.6501,"lon":-73.9496,"color":"#f78166",
                      "location":"Corelink — Brooklyn",
                      "ranges":[(601,606)]},
        },
    },
    "Seattle": {
        "code":    "sea",
        "center":  [47.61, -122.33],
        "zoom":    11,
        "servers": _s("sea", (1,6),(201,204),(401,406)),
        "datacenters": {
            "SEA-A": {"lat":47.6062,"lon":-122.3321,"color":"#00e5ff",
                      "location":"Equinix SE2 — Seattle",
                      "ranges":[(1,6)]},
            "SEA-B": {"lat":47.5480,"lon":-122.0370,"color":"#7ee787",
                      "location":"Sabey Intergate — Bellevue",
                      "ranges":[(201,204)]},
            "SEA-C": {"lat":47.6741,"lon":-122.1215,"color":"#e3b341",
                      "location":"Westin Building — Redmond",
                      "ranges":[(401,406)]},
        },
    },
    "Chicago": {
        "code":    "chi",
        "center":  [41.88, -87.63],
        "zoom":    11,
        "servers": _s("chi", (1,6),(201,205),(401,406)),
        "datacenters": {
            "CHI-A": {"lat":41.8827,"lon":-87.6233,"color":"#00e5ff",
                      "location":"Equinix CH4 — Chicago",
                      "ranges":[(1,6)]},
            "CHI-B": {"lat":41.9742,"lon":-87.8073,"color":"#7ee787",
                      "location":"CyrusOne — Elk Grove",
                      "ranges":[(201,205)]},
            "CHI-C": {"lat":41.8500,"lon":-87.9500,"color":"#e3b341",
                      "location":"Flexential — Westmont",
                      "ranges":[(401,406)]},
        },
    },
    "Dallas": {
        "code":    "dal",
        "center":  [32.78, -96.80],
        "zoom":    11,
        "servers": _s("dal", (1,6),(201,204),(401,405)),
        "datacenters": {
            "DAL-A": {"lat":32.7767,"lon":-96.7970,"color":"#00e5ff",
                      "location":"Equinix DA2 — Dallas",
                      "ranges":[(1,6)]},
            "DAL-B": {"lat":32.9537,"lon":-96.8903,"color":"#7ee787",
                      "location":"CyrusOne — Carrollton",
                      "ranges":[(201,204)]},
            "DAL-C": {"lat":32.8998,"lon":-97.0403,"color":"#e3b341",
                      "location":"Stream Global — Irving",
                      "ranges":[(401,405)]},
        },
    },
    "Atlanta": {
        "code":    "atl",
        "center":  [33.75, -84.39],
        "zoom":    11,
        "servers": _s("atl", (1,5),(201,204),(401,404)),
        "datacenters": {
            "ATL-A": {"lat":33.7490,"lon":-84.3880,"color":"#00e5ff",
                      "location":"Equinix AT2 — Atlanta",
                      "ranges":[(1,5)]},
            "ATL-B": {"lat":33.8748,"lon":-84.4660,"color":"#7ee787",
                      "location":"QTS — Suwanee",
                      "ranges":[(201,204)]},
            "ATL-C": {"lat":33.6407,"lon":-84.4277,"color":"#e3b341",
                      "location":"Corelink — College Park",
                      "ranges":[(401,404)]},
        },
    },
    "Miami": {
        "code":    "mia",
        "center":  [25.78, -80.19],
        "zoom":    11,
        "servers": _s("mia", (1,5),(201,203),(401,404)),
        "datacenters": {
            "MIA-A": {"lat":25.7617,"lon":-80.1918,"color":"#00e5ff",
                      "location":"Equinix MI1 — Miami",
                      "ranges":[(1,5)]},
            "MIA-B": {"lat":25.9145,"lon":-80.1576,"color":"#7ee787",
                      "location":"CyrusOne — North Miami",
                      "ranges":[(201,203)]},
            "MIA-C": {"lat":25.7742,"lon":-80.3350,"color":"#e3b341",
                      "location":"Datasite — Doral",
                      "ranges":[(401,404)]},
        },
    },
}

def get_server_group(server, region_name):
    """Return datacenter group name for a server in the given region."""
    region = REGIONS[region_name]
    n = int(re.search(r"wg-(\d+)", server).group(1))
    for dc_name, dc in region["datacenters"].items():
        for lo, hi in dc["ranges"]:
            if lo <= n <= hi:
                return dc_name
    return list(region["datacenters"].keys())[0]


# ── GEO HELPERS ───────────────────────────────────────────────────────────────
def haversine_km(lat1, lon1, lat2, lon2):
    R = 6371.0
    p1,p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = math.radians(lat2-lat1), math.radians(lon2-lon1)
    a = math.sin(dp/2)**2 + math.cos(p1)*math.cos(p2)*math.sin(dl/2)**2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))

def fetch_location_ip():
    try:
        url = "http://ip-api.com/json/?fields=status,country,regionName,city,lat,lon,isp,query"
        req = urllib.request.Request(url, headers={"User-Agent": "MullvadPingTool/2.0"})
        with urllib.request.urlopen(req, timeout=6) as r:
            d = json.loads(r.read().decode())
        if d.get("status") == "success":
            return {"lat":d["lat"],"lon":d["lon"],"city":d.get("city",""),
                    "region":d.get("regionName",""),"country":d.get("country",""),
                    "isp":d.get("isp",""),"ip":d.get("query",""),"source":"ip"}
    except Exception:
        pass
    return None

def geocode_address(query):
    try:
        q = urllib.parse.quote(query)
        url = (f"https://nominatim.openstreetmap.org/search"
               f"?q={q}&format=json&addressdetails=1&limit=6")
        req = urllib.request.Request(
            url, headers={"User-Agent":"MullvadPingTool/2.0 (github.com/mullvad-lax-ping)"})
        with urllib.request.urlopen(req, timeout=8) as r:
            results = json.loads(r.read().decode())
        out = []
        for r in results:
            addr = r.get("address", {})
            city   = addr.get("city") or addr.get("town") or addr.get("village") or ""
            out.append({"lat":float(r["lat"]),"lon":float(r["lon"]),
                        "display_name":r["display_name"],
                        "city":city,"region":addr.get("state",""),
                        "country":addr.get("country",""),"source":"address"})
        return out
    except Exception:
        return []

# ── PING ENGINE ───────────────────────────────────────────────────────────────
def ping_stream(host, count, callback):
    """
    Ping host `count` times, calling callback(ms_or_None) after each reply.
    Returns (avg, mn, mx, loss_pct, jitter).
    """
    flag   = "-n" if platform.system() == "Windows" else "-c"
    times  = []
    failed = 0
    try:
        proc = subprocess.Popen(
            ["ping", flag, str(count), host],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, bufsize=1)
        for line in proc.stdout:
            # Windows: "Reply from X: bytes=32 time=12ms TTL=128"
            # Linux:   "64 bytes from X: icmp_seq=1 ttl=64 time=12.3 ms"
            m_win  = re.search(r"time[=<](\d+)ms", line)
            m_unix = re.search(r"time=([\d.]+)\s*ms", line)
            m_fail = re.search(r"(Request timed out|Destination Host Unreachable"
                               r"|100% packet loss|no route)", line, re.IGNORECASE)
            if m_win:
                ms = float(m_win.group(1))
                times.append(ms); callback(ms)
            elif m_unix:
                ms = float(m_unix.group(1))
                times.append(ms); callback(ms)
            elif m_fail:
                failed += 1; callback(None)
        proc.wait()
    except Exception:
        pass

    if not times:
        return None
    avg     = sum(times) / len(times)
    mn, mx  = min(times), max(times)
    jitter  = mx - mn
    loss    = int(100 * failed / count)
    return avg, mn, mx, loss, jitter

# ── TRACEROUTE ────────────────────────────────────────────────────────────────
def run_traceroute(host, callback):
    """
    Run traceroute/tracert, yield parsed hop dicts via callback.
    callback receives list of {hop, ip, ms1, ms2, ms3} dicts (live, one per line).
    """
    system = platform.system()
    if system == "Windows":
        cmd = ["tracert", "-d", "-w", "2000", "-h", "30", host]
    else:
        cmd = ["traceroute", "-n", "-w", "2", "-m", "30", host]
    hops = []
    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, bufsize=1)
        for line in proc.stdout:
            hop = _parse_hop(line, system)
            if hop:
                hops.append(hop)
                callback(hops[:])
        proc.wait()
    except Exception as e:
        callback(hops[:], error=str(e))

def _parse_hop(line, system):
    if system == "Windows":
        # "  1    <1 ms    <1 ms    <1 ms  192.168.1.1"
        m = re.match(r"\s*(\d+)\s+(.+)", line)
        if not m: return None
        hop_n = int(m.group(1))
        rest  = m.group(2)
        ips   = re.findall(r"\d+\.\d+\.\d+\.\d+", rest)
        ms_   = re.findall(r"(?:<?\s*(\d+)\s*ms|(\*))", rest)
        times = []
        for a, b in ms_:
            times.append(float(a) if a else None)
        ip = ips[-1] if ips else "*"
        return {"hop":hop_n,"ip":ip,"times":times[:3]}
    else:
        # " 1  192.168.1.1  0.456 ms  0.412 ms  0.389 ms"
        m = re.match(r"\s*(\d+)\s+(\S+)\s+(.*)", line)
        if not m: return None
        hop_n = int(m.group(1))
        ip    = m.group(2)
        rest  = m.group(3)
        ms_   = re.findall(r"([\d.]+)\s*ms|\*", rest)
        times = []
        for x in ms_:
            times.append(float(x) if x and x != "*" else None)
        return {"hop":hop_n,"ip":ip,"times":times[:3]}

# ── SPEED TEST ────────────────────────────────────────────────────────────────
SPEED_URLS = {
    "Cloudflare (CDN)":   "https://speed.cloudflare.com/__down?bytes=10000000",
    "Mullvad CDN (10MB)": "https://am.i.mullvad.net/download/10000000",
    "Fast.com seed":      "https://api.fast.com/netflix/speedtest/v2?https=true&token=YXNkZmFzZGxmbnNkYWZoYXNk",
}
DEFAULT_SPEED_URL = "Cloudflare (CDN)"

def run_speed_test(url, progress_cb, done_cb):
    """
    Download url, measuring throughput. Calls progress_cb(pct, mbps) periodically.
    Calls done_cb(avg_mbps, peak_mbps, total_mb, elapsed_s) when done.
    """
    try:
        req   = urllib.request.Request(url, headers={"User-Agent":"MullvadPingTool/2.0"})
        start = time.time()
        downloaded = 0
        chunk_times = []
        with urllib.request.urlopen(req, timeout=20) as resp:
            total = int(resp.headers.get("Content-Length", 10_000_000))
            while True:
                t0    = time.time()
                chunk = resp.read(65536)
                if not chunk:
                    break
                dt = time.time() - t0
                downloaded += len(chunk)
                if dt > 0:
                    chunk_mbps = (len(chunk)*8) / (dt * 1_000_000)
                    chunk_times.append(chunk_mbps)
                elapsed = time.time() - start
                cur_mbps = (downloaded * 8) / (elapsed * 1_000_000) if elapsed > 0 else 0
                pct = min(100, int(downloaded * 100 / total))
                progress_cb(pct, cur_mbps)
        elapsed   = time.time() - start
        avg_mbps  = (downloaded * 8) / (elapsed * 1_000_000)
        peak_mbps = max(chunk_times) if chunk_times else avg_mbps
        total_mb  = downloaded / 1_000_000
        done_cb(avg_mbps, peak_mbps, total_mb, elapsed)
    except Exception as e:
        done_cb(0, 0, 0, 0, error=str(e))

# ── DATABASE ──────────────────────────────────────────────────────────────────
def init_db():
    con = sqlite3.connect(DB_PATH)
    con.execute("""
        CREATE TABLE IF NOT EXISTS runs (
            id        INTEGER PRIMARY KEY AUTOINCREMENT,
            ts        TEXT    NOT NULL,
            region    TEXT    NOT NULL,
            ping_count INTEGER NOT NULL DEFAULT 4
        )""")
    con.execute("""
        CREATE TABLE IF NOT EXISTS results (
            id      INTEGER PRIMARY KEY AUTOINCREMENT,
            run_id  INTEGER NOT NULL REFERENCES runs(id),
            server  TEXT    NOT NULL,
            grp     TEXT    NOT NULL,
            avg_ms  REAL,
            min_ms  REAL,
            max_ms  REAL,
            loss    INTEGER,
            jitter  REAL
        )""")
    con.commit()
    con.close()

def db_save_run(region, ping_count, results):
    """Save a completed run. results = list of dicts."""
    con = sqlite3.connect(DB_PATH)
    ts  = datetime.now().isoformat(timespec="seconds")
    cur = con.execute("INSERT INTO runs(ts,region,ping_count) VALUES(?,?,?)",
                      (ts, region, ping_count))
    run_id = cur.lastrowid
    for r in results:
        con.execute(
            "INSERT INTO results(run_id,server,grp,avg_ms,min_ms,max_ms,loss,jitter)"
            " VALUES(?,?,?,?,?,?,?,?)",
            (run_id, r["server"], r["grp"],
             r.get("avg"), r.get("min"), r.get("max"),
             r.get("loss",100), r.get("jitter",0)))
    con.commit()
    con.close()
    return run_id

def db_load_history(region, limit=50):
    """Return DataFrame of past results for a region."""
    con = sqlite3.connect(DB_PATH)
    df  = pd.read_sql_query("""
        SELECT r.ts, res.server, res.grp, res.avg_ms, res.min_ms,
               res.max_ms, res.loss, res.jitter
        FROM results res
        JOIN runs r ON res.run_id = r.id
        WHERE r.region = ?
        ORDER BY r.ts DESC
        LIMIT ?
    """, con, params=(region, limit*50))
    con.close()
    return df

def db_load_runs(region, limit=20):
    con = sqlite3.connect(DB_PATH)
    df  = pd.read_sql_query(
        "SELECT * FROM runs WHERE region=? ORDER BY ts DESC LIMIT ?",
        con, params=(region, limit))
    con.close()
    return df

# ── COLOUR HELPERS ────────────────────────────────────────────────────────────
def ping_color(avg):
    if avg is None: return T["fg_dim"]
    if avg < 30:   return T["green"]
    if avg < 70:   return T["accent"]
    if avg < 120:  return T["yellow"]
    return T["red"]

def ping_folium(avg):
    if avg is None: return "#8b949e"
    if avg < 30:   return "#7ee787"
    if avg < 70:   return "#00e5ff"
    if avg < 120:  return "#e3b341"
    return "#f85149"

def ms_tag(avg):
    if avg is None: return "dead"
    if avg < 30:   return "good"
    if avg < 70:   return "ok"
    if avg < 120:  return "slow"
    return "bad"


# ── LOCATION DIALOG ───────────────────────────────────────────────────────────
class LocationDialog(tk.Toplevel):
    def __init__(self, parent, prefill=""):
        super().__init__(parent)
        self.location = None
        self._results = []
        self._selected = None
        self.title("Set Your Location")
        self.configure(bg=T["bg"])
        self.resizable(False, False)
        self.grab_set(); self.transient(parent)
        self.geometry("540x560")
        self._build(prefill)
        self.update_idletasks()
        px = parent.winfo_x() + parent.winfo_width()  // 2
        py = parent.winfo_y() + parent.winfo_height() // 2
        w, h = self.winfo_width(), self.winfo_height()
        self.geometry(f"+{px-w//2}+{py-h//2}")

    def _build(self, prefill):
        outer = tk.Frame(self, bg=T["bg"], padx=26, pady=22)
        outer.pack(fill=tk.BOTH, expand=True)
        # Title
        tr = tk.Frame(outer, bg=T["bg"]); tr.pack(fill=tk.X, pady=(0,4))
        tk.Label(tr, text="◎", font=("Segoe UI",20), fg=T["accent"],
                 bg=T["bg"]).pack(side=tk.LEFT, padx=(0,10))
        tk.Label(tr, text="Set Your Location", font=("Segoe UI",13,"bold"),
                 fg=T["fg"], bg=T["bg"]).pack(side=tk.LEFT)
        tk.Frame(outer, bg=T["bg3"], height=1).pack(fill=tk.X, pady=(8,12))
        # Search
        tk.Label(outer, text="Address, neighbourhood, city, or zip code:",
                 font=("Segoe UI",10), fg=T["fg_dim"], bg=T["bg"]).pack(anchor="w")
        sr = tk.Frame(outer, bg=T["bg"]); sr.pack(fill=tk.X, pady=(5,0))
        self._sv = tk.StringVar(value=prefill)
        self._entry = tk.Entry(sr, textvariable=self._sv, bg=T["entry_bg"],
                               fg=T["fg"], insertbackground=T["fg"],
                               relief=tk.FLAT, font=("Segoe UI",11),
                               highlightbackground=T["entry_hl"], highlightthickness=1)
        self._entry.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=7)
        self._entry.bind("<Return>", lambda e: self._search())
        self._entry.focus_set()
        tk.Button(sr, text="Search", font=("Segoe UI",10,"bold"),
                  fg=T["bg"], bg=T["accent"], relief=tk.FLAT,
                  padx=12, pady=7, cursor="hand2",
                  command=self._search).pack(side=tk.LEFT, padx=(5,0))
        self._stv = tk.StringVar(value="Type an address and press Search.")
        tk.Label(outer, textvariable=self._stv, font=MONO,
                 fg=T["fg_dim"], bg=T["bg"], anchor="w").pack(fill=tk.X, pady=(5,3))
        # Listbox
        lf = tk.Frame(outer, bg=T["bg2"]); lf.pack(fill=tk.BOTH, expand=True)
        self._lb = tk.Listbox(lf, bg=T["bg2"], fg=T["fg"],
                              selectbackground=T["sel_bg"], selectforeground=T["sel_fg"],
                              activestyle="none", relief=tk.FLAT,
                              font=("Segoe UI",9), borderwidth=0, highlightthickness=0)
        sb = tk.Scrollbar(lf, orient=tk.VERTICAL, command=self._lb.yview,
                          bg=T["bg3"], troughcolor=T["bg3"], relief=tk.FLAT, width=8)
        self._lb.configure(yscrollcommand=sb.set)
        self._lb.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        self._lb.bind("<<ListboxSelect>>", self._sel)
        self._lb.bind("<Double-Button-1>", lambda e: self._confirm())
        # Preview
        self._pv = tk.Frame(outer, bg=T["bg2"], padx=12, pady=8)
        self._pv.pack(fill=tk.X, pady=(6,0))
        self._pt = tk.Label(self._pv, text="No result selected",
                            font=("Segoe UI",10,"bold"), fg=T["fg_dim"], bg=T["bg2"], anchor="w")
        self._pt.pack(fill=tk.X)
        self._pc = tk.Label(self._pv, text="", font=MONO, fg=T["fg_dim"], bg=T["bg2"], anchor="w")
        self._pc.pack(fill=tk.X)
        # Buttons
        tk.Frame(outer, bg=T["bg3"], height=1).pack(fill=tk.X, pady=(12,8))
        br = tk.Frame(outer, bg=T["bg"]); br.pack(fill=tk.X)
        tk.Button(br, text="Use IP Instead", font=("Segoe UI",9),
                  fg=T["fg_dim"], bg=T["bg3"], relief=tk.FLAT,
                  padx=10, pady=4, cursor="hand2",
                  command=self._use_ip).pack(side=tk.LEFT)
        tk.Button(br, text="Cancel", font=("Segoe UI",10),
                  fg=T["fg_dim"], bg=T["bg3"], relief=tk.FLAT,
                  padx=12, pady=5, cursor="hand2",
                  command=self.destroy).pack(side=tk.RIGHT, padx=(5,0))
        self._cbtn = tk.Button(br, text="Use This Location  ✓",
                               font=("Segoe UI",10,"bold"),
                               fg=T["bg"], bg=T["accent"], relief=tk.FLAT,
                               padx=12, pady=5, cursor="hand2",
                               state=tk.DISABLED, command=self._confirm)
        self._cbtn.pack(side=tk.RIGHT)

    def _search(self):
        q = self._sv.get().strip()
        if not q: return
        self._stv.set("Searching…")
        self._lb.delete(0, tk.END)
        self._results = []; self._selected = None
        self._cbtn.config(state=tk.DISABLED)
        threading.Thread(target=lambda: self.after(0, self._got,
            geocode_address(q)), daemon=True).start()

    def _got(self, results):
        self._results = results
        self._lb.delete(0, tk.END)
        if not results:
            self._stv.set("No results. Try a different query."); return
        self._stv.set(f"{len(results)} result(s) — click to select, double-click to confirm.")
        for r in results:
            n = r["display_name"]
            self._lb.insert(tk.END, f"  {n[:74]}{'…' if len(n)>74 else ''}")

    def _sel(self, _=None):
        sel = self._lb.curselection()
        if not sel: return
        self._selected = sel[0]
        r = self._results[self._selected]
        lbl = ", ".join(x for x in [r.get("city",""), r.get("region",""),
                                     r.get("country","")] if x)
        self._pt.config(text=lbl or r["display_name"][:60], fg=T["fg"])
        self._pc.config(text=f"  {r['lat']:.5f}, {r['lon']:.5f}")
        self._cbtn.config(state=tk.NORMAL)

    def _confirm(self):
        if self._selected is None: return
        self.location = self._results[self._selected]; self.destroy()

    def _use_ip(self):
        self._stv.set("Fetching IP location…")
        def _f():
            loc = fetch_location_ip()
            self.after(0, lambda: (setattr(self, "location", loc), self.destroy())
                       if loc else self._stv.set("IP lookup failed."))
        threading.Thread(target=_f, daemon=True).start()


# ── SYSTEM TRAY ───────────────────────────────────────────────────────────────
def make_tray_icon(color_hex="#00e5ff"):
    img  = Image.new("RGBA", (64,64), (0,0,0,0))
    draw = ImageDraw.Draw(img)
    r, g, b = tuple(int(color_hex.lstrip("#")[i:i+2], 16) for i in (0,2,4))
    draw.ellipse([4,4,60,60], fill=(r,g,b,220))
    draw.text((20,18), "M", fill=(0,0,0,255))
    return img

# ── MAIN APPLICATION ──────────────────────────────────────────────────────────
class MullvadApp(tk.Tk):
    def __init__(self):
        super().__init__()
        init_db()
        self.title("Mullvad WireGuard  |  Latency Monitor  v2.0")
        self.configure(bg=T["bg"])
        self.geometry("1380x940")
        self.minsize(1000, 720)

        # State
        self.current_region   = "Los Angeles"
        self.results          = {}     # server -> (avg,min,max,loss,jitter) or None
        self.compare_a        = {}     # saved run A
        self.compare_b        = {}     # saved run B
        self.running          = False
        self.schedule_job     = None
        self.ping_count       = tk.IntVar(value=4)
        self.threshold_ms     = tk.DoubleVar(value=100.0)
        self.threshold_on     = tk.BooleanVar(value=True)
        self.schedule_mins    = tk.DoubleVar(value=5.0)
        self.schedule_active  = tk.BooleanVar(value=False)
        self._user_loc        = None
        self._loc_allowed     = False
        self._map_tmp         = None
        self._stats_canvas    = None
        self._map_canvas      = None
        self._hist_canvas     = None
        self._trace_canvas    = None
        self._speed_canvas    = None
        self._dc_stat_labels  = {}
        self._row_ids         = {}      # server -> treeview iid
        self._row_dots        = {}      # server -> list of received ms values (animation)
        self._tray            = None

        self._apply_style()
        self._build_header()
        self._build_notebook()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(400, self._request_location)

    # ── THEME ─────────────────────────────────────────────────────────────────
    def _apply_style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        bg, bg2, bg3 = T["bg"], T["bg2"], T["bg3"]
        fg, fd       = T["fg"], T["fg_dim"]
        acc          = T["accent"]
        s.configure("TNotebook",       background=bg,  borderwidth=0)
        s.configure("TNotebook.Tab",   background=bg3, foreground=fd,
                    padding=[14,5], font=("Segoe UI",10))
        s.map("TNotebook.Tab",
              background=[("selected",bg2)], foreground=[("selected",acc)])
        s.configure("Treeview",
                    background=bg2, foreground=fg, fieldbackground=bg2,
                    rowheight=26, borderwidth=0, font=MONO)
        s.configure("Treeview.Heading",
                    background=bg3, foreground=fd,
                    font=("Segoe UI",9,"bold"), relief="flat")
        s.map("Treeview",
              background=[("selected",T["sel_bg"])],
              foreground=[("selected",T["sel_fg"])])
        s.configure("custom.Horizontal.TProgressbar",
                    troughcolor=bg3, background=acc,
                    darkcolor=acc, lightcolor=acc,
                    bordercolor=bg3, relief="flat")
        s.configure("TScale", background=bg2, troughcolor=bg3)
        s.configure("TCombobox", fieldbackground=T["entry_bg"],
                    background=bg3, foreground=fg, arrowcolor=fd)
        s.map("TCombobox", fieldbackground=[("readonly",T["entry_bg"])],
              foreground=[("readonly",fg)])

    def toggle_theme(self):
        target = LIGHT if T["name"] == "dark" else DARK
        T.update(target)
        self._apply_style()
        self._retheme_widget(self)
        # Redraw matplotlib canvases
        df = self._build_dataframe()
        self._draw_stats()
        self._draw_static_map(df if not df.empty else None)

    def _retheme_widget(self, w):
        cls = w.winfo_class()
        try:
            if cls in ("Frame","Toplevel","Tk"):
                w.configure(bg=T["bg"])
            elif cls == "Label":
                cur = w.cget("bg")
                # Map old bg shades to new
                shade_map = {DARK["bg"]:T["bg"], DARK["bg2"]:T["bg2"],
                             DARK["bg3"]:T["bg3"], LIGHT["bg"]:T["bg"],
                             LIGHT["bg2"]:T["bg2"], LIGHT["bg3"]:T["bg3"]}
                new_bg = shade_map.get(cur, T["bg"])
                cur_fg = w.cget("fg")
                fg_map = {DARK["fg"]:T["fg"], DARK["fg_dim"]:T["fg_dim"],
                          LIGHT["fg"]:T["fg"], LIGHT["fg_dim"]:T["fg_dim"]}
                new_fg = fg_map.get(cur_fg, cur_fg)
                w.configure(bg=new_bg, fg=new_fg)
            elif cls == "Button":
                if w.cget("bg") in (DARK["bg3"], LIGHT["bg3"]):
                    w.configure(bg=T["bg3"], fg=T["fg_dim"])
                elif w.cget("bg") in (DARK["bg2"], LIGHT["bg2"]):
                    w.configure(bg=T["bg2"])
            elif cls == "Text":
                w.configure(bg=T["bg2"], fg=T["fg_dim"])
            elif cls == "Listbox":
                w.configure(bg=T["bg2"], fg=T["fg"],
                            selectbackground=T["sel_bg"],
                            selectforeground=T["sel_fg"])
            elif cls == "Entry":
                w.configure(bg=T["entry_bg"], fg=T["fg"],
                            highlightbackground=T["entry_hl"])
        except tk.TclError:
            pass
        for child in w.winfo_children():
            self._retheme_widget(child)

    # ── HEADER ────────────────────────────────────────────────────────────────
    def _build_header(self):
        h = tk.Frame(self, bg=T["bg2"], pady=8)
        h.pack(fill=tk.X)

        tk.Label(h, text="  MULLVAD", font=("Courier New",15,"bold"),
                 fg=T["accent"], bg=T["bg2"]).pack(side=tk.LEFT, padx=14)

        # Region selector
        tk.Label(h, text="Region:", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT, padx=(8,3))
        self._region_cb = ttk.Combobox(h, values=list(REGIONS.keys()),
                                       state="readonly", width=13,
                                       font=("Segoe UI",9))
        self._region_cb.set(self.current_region)
        self._region_cb.pack(side=tk.LEFT)
        self._region_cb.bind("<<ComboboxSelected>>", self._on_region_change)

        # Ping count
        tk.Label(h, text="Pings:", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT, padx=(10,3))
        self._ping_lbl = tk.Label(h, text="4", font=("Courier New",9,"bold"),
                                  fg=T["accent"], bg=T["bg2"], width=2)
        self._ping_lbl.pack(side=tk.LEFT)
        pc_slider = ttk.Scale(h, from_=2, to=20, variable=self.ping_count,
                              orient=tk.HORIZONTAL, length=90,
                              command=lambda v: self._ping_lbl.config(
                                  text=str(int(float(v)))))
        pc_slider.pack(side=tk.LEFT, padx=(2,8))

        # Threshold
        tk.Label(h, text="Alert >", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT)
        self._thr_entry = tk.Entry(h, textvariable=self.threshold_ms,
                                   width=5, bg=T["entry_bg"], fg=T["fg"],
                                   relief=tk.FLAT, font=("Courier New",9),
                                   insertbackground=T["fg"],
                                   highlightbackground=T["entry_hl"],
                                   highlightthickness=1)
        self._thr_entry.pack(side=tk.LEFT, ipady=3)
        tk.Label(h, text="ms", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT, padx=(2,6))
        tk.Checkbutton(h, variable=self.threshold_on, text="on",
                       font=("Segoe UI",9), fg=T["fg_dim"], bg=T["bg2"],
                       selectcolor=T["bg3"], activebackground=T["bg2"],
                       relief=tk.FLAT, highlightthickness=0).pack(side=tk.LEFT)

        # Right-side controls
        tk.Button(h, text="☽" if T["name"]=="dark" else "☀",
                  font=("Segoe UI",12), fg=T["fg_dim"], bg=T["bg2"],
                  relief=tk.FLAT, padx=6, cursor="hand2",
                  command=self.toggle_theme).pack(side=tk.RIGHT, padx=4)

        tk.Button(h, text="⊟  Tray",
                  font=("Segoe UI",9), fg=T["fg_dim"], bg=T["bg3"],
                  relief=tk.FLAT, padx=8, pady=4, cursor="hand2",
                  command=self._minimize_to_tray).pack(side=tk.RIGHT, padx=(0,4))

        self.btn = tk.Button(h, text="▶  Run",
                             font=("Segoe UI",10,"bold"),
                             fg=T["bg"], bg=T["accent"],
                             activebackground="#00b8cc",
                             relief=tk.FLAT, padx=14, pady=4,
                             cursor="hand2", command=self.start_pinging)
        self.btn.pack(side=tk.RIGHT, padx=(0,14))

        # Auto-schedule row
        sh = tk.Frame(self, bg=T["bg2"], pady=4)
        sh.pack(fill=tk.X)
        tk.Checkbutton(sh, variable=self.schedule_active,
                       text="Auto-ping every", font=("Segoe UI",9),
                       fg=T["fg_dim"], bg=T["bg2"],
                       selectcolor=T["bg3"], activebackground=T["bg2"],
                       relief=tk.FLAT, highlightthickness=0,
                       command=self._toggle_schedule).pack(side=tk.LEFT, padx=(14,4))
        ttk.Scale(sh, from_=1, to=60, variable=self.schedule_mins,
                  orient=tk.HORIZONTAL, length=100).pack(side=tk.LEFT)
        self._sched_lbl = tk.Label(sh, text="5.0 min", font=("Courier New",9),
                                   fg=T["accent"], bg=T["bg2"], width=7)
        self._sched_lbl.pack(side=tk.LEFT, padx=(4,16))
        self.schedule_mins.trace_add("write", lambda *_: self._sched_lbl.config(
            text=f"{self.schedule_mins.get():.1f} min"))

        # Location badge
        self._loc_frame = tk.Frame(sh, bg=T["bg3"], padx=8, pady=2)
        self._loc_frame.pack(side=tk.LEFT, padx=(20,0))
        self._loc_dot  = tk.Label(self._loc_frame, text="◎",
                                  fg=T["fg_dim"], bg=T["bg3"], font=("Segoe UI",10))
        self._loc_dot.pack(side=tk.LEFT, padx=(0,5))
        self._loc_text = tk.Label(self._loc_frame, text="Location: not set",
                                  font=("Courier New",8), fg=T["fg_dim"], bg=T["bg3"])
        self._loc_text.pack(side=tk.LEFT)
        for w in (self._loc_frame, self._loc_dot, self._loc_text):
            w.bind("<Button-1>", lambda e: self._request_location(force=True))
            w.configure(cursor="hand2")

        # Progress + status
        pf = tk.Frame(self, bg=T["bg"], pady=3)
        pf.pack(fill=tk.X, padx=16)
        self.status_var = tk.StringVar(value="Ready.")
        tk.Label(pf, textvariable=self.status_var,
                 font=MONO, fg=T["fg_dim"], bg=T["bg"], anchor="w").pack(fill=tk.X)
        self.progress = ttk.Progressbar(pf, style="custom.Horizontal.TProgressbar")
        self.progress.pack(fill=tk.X, pady=(2,0))

        # Summary cards
        cf = tk.Frame(self, bg=T["bg"], pady=5)
        cf.pack(fill=tk.X, padx=16)
        self.cards = {}
        card_defs = [
            ("Best Server",  T["green"]),
            ("Worst Server", T["red"]),
            ("Avg Latency",  T["accent"]),
            ("Avg Jitter",   T["yellow"]),
            ("Reachable",    T["accent"]),
        ]
        for lbl, col in card_defs:
            c = tk.Frame(cf, bg=T["bg2"], padx=14, pady=7)
            c.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=(0,6))
            tk.Label(c, text=lbl.upper(), font=("Courier New",7),
                     fg=T["fg_dim"], bg=T["bg2"]).pack(anchor="w")
            v   = tk.Label(c, text="--", font=("Segoe UI",12,"bold"),
                           fg=col, bg=T["bg2"])
            v.pack(anchor="w")
            sub = tk.Label(c, text="", font=MONO, fg=T["fg_dim"], bg=T["bg2"])
            sub.pack(anchor="w")
            self.cards[lbl] = (v, sub)

        # Export + copy + compare + autoconnect row
        ar = tk.Frame(self, bg=T["bg"], pady=3)
        ar.pack(fill=tk.X, padx=16)
        for txt, cmd in [
            ("⎘  Copy Best",         self._copy_best),
            ("↓  Export CSV",        self._export_csv),
            ("↓  Export JSON",       self._export_json),
            ("⊞  Save as Run A",     self._save_run_a),
            ("⊞  Save as Run B",     self._save_run_b),
            ("⇄  Compare A vs B",    self._show_compare),
            ("⚡  Auto-Connect",      self._auto_connect),
        ]:
            tk.Button(ar, text=txt, font=("Segoe UI",8),
                      fg=T["fg_dim"], bg=T["bg3"],
                      activebackground=T["bg4"],
                      relief=tk.FLAT, padx=9, pady=3,
                      cursor="hand2", command=cmd).pack(side=tk.LEFT, padx=(0,4))


    # ── NOTEBOOK ──────────────────────────────────────────────────────────────
    def _build_notebook(self):
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill=tk.BOTH, expand=True, padx=16, pady=(0,12))
        self._build_results_tab()
        self._build_stats_tab()
        self._build_map_tab()
        self._build_history_tab()
        self._build_traceroute_tab()
        self._build_speedtest_tab()
        self._build_compare_tab()

    # ── TAB: RESULTS ──────────────────────────────────────────────────────────
    def _build_results_tab(self):
        f = tk.Frame(self.nb, bg=T["bg"]); self.nb.add(f, text="  Results  ")
        cols   = ("Server","Group","Avg ms","Min ms","Max ms",
                  "Jitter","Loss %","Live","Status")
        widths = [200, 100, 72, 72, 72, 72, 60, 120, 115]
        self.tree = ttk.Treeview(f, columns=cols, show="headings",
                                 selectmode="browse")
        for col, w in zip(cols, widths):
            anch = "w" if col in ("Server","Group","Live","Status") else "center"
            self.tree.heading(col, text=col,
                              command=lambda c=col: self._sort_tree(c))
            self.tree.column(col, width=w, anchor=anch)
        sb = ttk.Scrollbar(f, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        for tag, col in [("good",T["green"]),("ok",T["accent"]),
                         ("slow",T["yellow"]),("bad",T["red"]),
                         ("dead",T["fg_dim"]),("alert",T["red"])]:
            self.tree.tag_configure(tag, foreground=col)
        self.tree.tag_configure("alert", background="#2d0a0a")
        self._sort_col = None; self._sort_rev = False

    def _sort_tree(self, col):
        data = [(self.tree.set(iid, col), iid)
                for iid in self.tree.get_children()]
        rev = (self._sort_col == col) and not self._sort_rev
        try:
            data.sort(key=lambda x: float(x[0].replace("--","999").replace("%","")),
                      reverse=rev)
        except ValueError:
            data.sort(key=lambda x: x[0], reverse=rev)
        for idx, (_, iid) in enumerate(data):
            self.tree.move(iid, "", idx)
        self._sort_col = col; self._sort_rev = rev

    # ── TAB: STATISTICS ───────────────────────────────────────────────────────
    def _build_stats_tab(self):
        f = tk.Frame(self.nb, bg=T["bg"]); self.nb.add(f, text="  Statistics  ")
        self._stats_ph = tk.Label(f, text="Run a ping test to generate statistics.",
                                  font=("Segoe UI",13), fg=T["fg_dim"], bg=T["bg"])
        self._stats_ph.pack(expand=True)
        self._stats_frame = f

    # ── TAB: MAP ──────────────────────────────────────────────────────────────
    def _build_map_tab(self):
        f = tk.Frame(self.nb, bg=T["bg"]); self.nb.add(f, text="  Map  ")
        info = tk.Frame(f, bg=T["bg2"], pady=8, padx=14); info.pack(fill=tk.X)
        tk.Label(info, text="Datacenter Locations",
                 font=("Segoe UI",11,"bold"), fg=T["fg"], bg=T["bg2"]).pack(side=tk.LEFT)
        self.map_btn = tk.Button(info, text="  Open Interactive Map",
                                 font=("Segoe UI",9,"bold"),
                                 fg=T["bg"], bg=T["accent"],
                                 relief=tk.FLAT, padx=12, pady=4,
                                 cursor="hand2", state=tk.DISABLED,
                                 command=self._open_folium)
        self.map_btn.pack(side=tk.RIGHT)
        # DC legend cards
        dc_frame = tk.Frame(f, bg=T["bg"], pady=6, padx=14); dc_frame.pack(fill=tk.X)
        region = REGIONS[self.current_region]
        self._dc_stat_labels = {}
        for dc_name, dc in region["datacenters"].items():
            card = tk.Frame(dc_frame, bg=T["bg2"], padx=10, pady=6)
            card.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=(0,6))
            tk.Label(card, text="●", fg=dc["color"], bg=T["bg2"],
                     font=("Segoe UI",16)).pack(anchor="w")
            tk.Label(card, text=dc_name, font=("Segoe UI",8,"bold"),
                     fg=T["fg"], bg=T["bg2"]).pack(anchor="w")
            tk.Label(card, text=dc["location"], font=("Courier New",7),
                     fg=T["fg_dim"], bg=T["bg2"], wraplength=155, justify="left").pack(anchor="w")
            sl = tk.Label(card, text="", font=MONO, fg=dc["color"], bg=T["bg2"])
            sl.pack(anchor="w")
            self._dc_stat_labels[dc_name] = sl
        self._map_frame = tk.Frame(f, bg=T["bg"])
        self._map_frame.pack(fill=tk.BOTH, expand=True, padx=14, pady=(0,12))
        self._draw_static_map(None)

    # ── TAB: HISTORY ──────────────────────────────────────────────────────────
    def _build_history_tab(self):
        f = tk.Frame(self.nb, bg=T["bg"]); self.nb.add(f, text="  History  ")
        ctrl = tk.Frame(f, bg=T["bg2"], pady=8, padx=14); ctrl.pack(fill=tk.X)
        tk.Label(ctrl, text="Server filter:", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT)
        self._hist_sv = tk.StringVar()
        self._hist_entry = tk.Entry(ctrl, textvariable=self._hist_sv,
                                    bg=T["entry_bg"], fg=T["fg"],
                                    insertbackground=T["fg"], relief=tk.FLAT,
                                    font=("Courier New",9), width=22,
                                    highlightbackground=T["entry_hl"],
                                    highlightthickness=1)
        self._hist_entry.pack(side=tk.LEFT, padx=(5,8), ipady=4)
        tk.Label(ctrl, text="Runs:", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT)
        self._hist_runs = tk.IntVar(value=20)
        ttk.Scale(ctrl, from_=5, to=100, variable=self._hist_runs,
                  orient=tk.HORIZONTAL, length=90).pack(side=tk.LEFT, padx=(4,4))
        self._hist_rl = tk.Label(ctrl, text="20", font=("Courier New",9),
                                 fg=T["accent"], bg=T["bg2"], width=4)
        self._hist_rl.pack(side=tk.LEFT)
        self._hist_runs.trace_add("write", lambda *_: self._hist_rl.config(
            text=str(int(self._hist_runs.get()))))
        tk.Button(ctrl, text="Load History", font=("Segoe UI",9),
                  fg=T["bg"], bg=T["accent"], relief=tk.FLAT,
                  padx=10, pady=4, cursor="hand2",
                  command=self._draw_history).pack(side=tk.LEFT, padx=(10,0))
        tk.Button(ctrl, text="Clear DB", font=("Segoe UI",9),
                  fg=T["fg_dim"], bg=T["bg3"], relief=tk.FLAT,
                  padx=8, pady=4, cursor="hand2",
                  command=self._clear_history).pack(side=tk.LEFT, padx=(6,0))
        self._hist_ph = tk.Label(f, text="Click 'Load History' to view past runs.",
                                 font=("Segoe UI",12), fg=T["fg_dim"], bg=T["bg"])
        self._hist_ph.pack(expand=True)
        self._hist_frame = f

    # ── TAB: TRACEROUTE ───────────────────────────────────────────────────────
    def _build_traceroute_tab(self):
        f = tk.Frame(self.nb, bg=T["bg"]); self.nb.add(f, text="  Traceroute  ")
        ctrl = tk.Frame(f, bg=T["bg2"], pady=8, padx=14); ctrl.pack(fill=tk.X)
        tk.Label(ctrl, text="Target:", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT)
        self._trace_sv = tk.StringVar(value="us-lax-wg-001.mullvad.net")
        tk.Entry(ctrl, textvariable=self._trace_sv, width=30,
                 bg=T["entry_bg"], fg=T["fg"], insertbackground=T["fg"],
                 relief=tk.FLAT, font=("Courier New",9),
                 highlightbackground=T["entry_hl"],
                 highlightthickness=1).pack(side=tk.LEFT, padx=(5,8), ipady=4)
        tk.Button(ctrl, text="▶  Trace",
                  font=("Segoe UI",9,"bold"),
                  fg=T["bg"], bg=T["accent"], relief=tk.FLAT,
                  padx=10, pady=4, cursor="hand2",
                  command=self._start_traceroute).pack(side=tk.LEFT)
        tk.Button(ctrl, text="Use Best Server",
                  font=("Segoe UI",9), fg=T["fg_dim"], bg=T["bg3"],
                  relief=tk.FLAT, padx=8, pady=4, cursor="hand2",
                  command=self._trace_use_best).pack(side=tk.LEFT, padx=(6,0))
        # Split: text log left, plot right
        split = tk.Frame(f, bg=T["bg"]); split.pack(fill=tk.BOTH, expand=True, padx=14, pady=(4,12))
        self._trace_text = tk.Text(split, bg=T["bg2"], fg=T["fg_dim"],
                                   font=("Courier New",9), relief=tk.FLAT,
                                   state=tk.DISABLED, width=42)
        self._trace_text.pack(side=tk.LEFT, fill=tk.BOTH)
        self._trace_text.tag_configure("hop",  foreground=T["accent"])
        self._trace_text.tag_configure("good", foreground=T["green"])
        self._trace_text.tag_configure("slow", foreground=T["yellow"])
        self._trace_text.tag_configure("bad",  foreground=T["red"])
        self._trace_plot_frame = tk.Frame(split, bg=T["bg"])
        self._trace_plot_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

    # ── TAB: SPEED TEST ───────────────────────────────────────────────────────
    def _build_speedtest_tab(self):
        f = tk.Frame(self.nb, bg=T["bg"]); self.nb.add(f, text="  Speed Test  ")
        ctrl = tk.Frame(f, bg=T["bg2"], pady=8, padx=14); ctrl.pack(fill=tk.X)
        tk.Label(ctrl, text="Source:", font=("Segoe UI",9),
                 fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT)
        self._speed_src = tk.StringVar(value=DEFAULT_SPEED_URL)
        ttk.Combobox(ctrl, textvariable=self._speed_src,
                     values=list(SPEED_URLS.keys()),
                     state="readonly", width=22,
                     font=("Segoe UI",9)).pack(side=tk.LEFT, padx=(5,10))
        tk.Button(ctrl, text="▶  Run Speed Test",
                  font=("Segoe UI",9,"bold"),
                  fg=T["bg"], bg=T["accent"], relief=tk.FLAT,
                  padx=10, pady=4, cursor="hand2",
                  command=self._start_speedtest).pack(side=tk.LEFT)
        self._speed_status = tk.Label(ctrl, text="", font=("Courier New",9),
                                      fg=T["accent"], bg=T["bg2"])
        self._speed_status.pack(side=tk.LEFT, padx=(14,0))
        # Result cards
        sc = tk.Frame(f, bg=T["bg"], pady=6, padx=14); sc.pack(fill=tk.X)
        self._speed_cards = {}
        for lbl in ["Avg Speed","Peak Speed","Total Downloaded","Time"]:
            c = tk.Frame(sc, bg=T["bg2"], padx=14, pady=8)
            c.pack(side=tk.LEFT, expand=True, fill=tk.BOTH, padx=(0,6))
            tk.Label(c, text=lbl.upper(), font=("Courier New",7),
                     fg=T["fg_dim"], bg=T["bg2"]).pack(anchor="w")
            v = tk.Label(c, text="--", font=("Segoe UI",13,"bold"),
                         fg=T["accent"], bg=T["bg2"])
            v.pack(anchor="w")
            self._speed_cards[lbl] = v
        self._speed_prog = ttk.Progressbar(f, style="custom.Horizontal.TProgressbar",
                                           maximum=100)
        self._speed_prog.pack(fill=tk.X, padx=14, pady=(0,4))
        self._speed_ph = tk.Label(f, text="Run a speed test to see results.",
                                  font=("Segoe UI",12), fg=T["fg_dim"], bg=T["bg"])
        self._speed_ph.pack(expand=True)
        self._speed_frame = f

    # ── TAB: COMPARE ──────────────────────────────────────────────────────────
    def _build_compare_tab(self):
        f = tk.Frame(self.nb, bg=T["bg"]); self.nb.add(f, text="  Compare  ")
        ctrl = tk.Frame(f, bg=T["bg2"], pady=8, padx=14); ctrl.pack(fill=tk.X)
        tk.Label(ctrl, text="Side-by-side comparison of two saved runs.",
                 font=("Segoe UI",10), fg=T["fg_dim"], bg=T["bg2"]).pack(side=tk.LEFT)
        self._cmp_a_lbl = tk.Label(ctrl, text="Run A: (none)",
                                   font=("Courier New",9), fg=T["fg_dim"], bg=T["bg2"])
        self._cmp_a_lbl.pack(side=tk.LEFT, padx=(16,0))
        self._cmp_b_lbl = tk.Label(ctrl, text="Run B: (none)",
                                   font=("Courier New",9), fg=T["fg_dim"], bg=T["bg2"])
        self._cmp_b_lbl.pack(side=tk.LEFT, padx=(8,0))
        self._cmp_ph = tk.Label(f, text="Save two runs using 'Save as Run A' and 'Save as Run B', then click Compare.",
                                font=("Segoe UI",11), fg=T["fg_dim"], bg=T["bg"])
        self._cmp_ph.pack(expand=True)
        self._cmp_frame = f
        self._cmp_tree = None


    # ── LOCATION ──────────────────────────────────────────────────────────────
    def _request_location(self, force=False):
        prefill = ""
        if not self._loc_allowed:
            try:
                ip = fetch_location_ip()
                if ip: prefill = f"{ip['city']}, {ip.get('region','')}"
            except Exception: pass
        dlg = LocationDialog(self, prefill=prefill)
        self.wait_window(dlg)
        if dlg.location:
            self._loc_allowed = True
            self.after(50, self._on_loc, dlg.location)
        elif not self._loc_allowed:
            self._loc_text.config(text="Location: not set", fg=T["fg_dim"])
            self._loc_dot.config(fg=T["fg_dim"])

    def _on_loc(self, loc):
        if not loc:
            self._loc_text.config(text="Detection failed", fg=T["red"])
            self._loc_dot.config(fg=T["red"]); return
        self._user_loc = loc
        city   = loc.get("city",""); region = loc.get("region","")
        label  = ", ".join(x for x in [city, region] if x) or "Custom"
        src    = "address" if loc.get("source")=="address" else "IP"
        self._loc_text.config(text=f"  {label}", fg=T["green"])
        self._loc_dot.config(fg=T["green"])
        self.status_var.set(f"Location set ({src}): {label}  ({loc['lat']:.4f},{loc['lon']:.4f})")
        df = self._build_dataframe()
        self._draw_static_map(df if not df.empty else None)

    # ── REGION CHANGE ─────────────────────────────────────────────────────────
    def _on_region_change(self, _=None):
        new = self._region_cb.get()
        if new == self.current_region: return
        self.current_region = new
        self.results.clear()
        for iid in self.tree.get_children(): self.tree.delete(iid)
        self._row_ids.clear(); self._row_dots.clear()
        self._rebuild_dc_cards()
        self._draw_static_map(None)
        self.progress.configure(maximum=len(REGIONS[new]["servers"]), value=0)
        self.status_var.set(f"Region changed to {new}.")

    def _rebuild_dc_cards(self):
        # Re-render the DC legend cards for the new region
        for w in self._map_frame.master.winfo_children():
            if isinstance(w, tk.Frame) and w != self._map_frame:
                try: w.destroy()
                except: pass

    # ── PING ENGINE ───────────────────────────────────────────────────────────
    def start_pinging(self):
        if self.running: return
        self.running = True
        self.btn.config(state=tk.DISABLED, text="⏳")
        self.results.clear(); self._row_ids.clear(); self._row_dots.clear()
        self.progress.configure(maximum=len(REGIONS[self.current_region]["servers"]),
                                value=0)
        for iid in self.tree.get_children(): self.tree.delete(iid)
        for v, s in self.cards.values(): v.config(text="--"); s.config(text="")
        threading.Thread(target=self._ping_all, daemon=True).start()

    def _ping_all(self):
        servers = REGIONS[self.current_region]["servers"]
        for i, server in enumerate(servers, 1):
            self.after(0, self.status_var.set,
                       f"Pinging {server}  ({i}/{len(servers)})")
            # Insert placeholder row first
            self.after(0, self._insert_placeholder, server)
            count = int(self.ping_count.get())
            dots  = []

            def pkt_cb(ms, s=server, d=dots):
                d.append(ms)
                self.after(0, self._animate_row, s, d[:])

            result = ping_stream(server, count, pkt_cb)
            self.results[server] = result
            self.after(0, self._finalise_row, server, result)
            self.after(0, lambda v=i: self.progress.configure(value=v))

        self.after(0, self._finish)

    def _insert_placeholder(self, server):
        grp   = get_server_group(server, self.current_region)
        short = server.replace(".mullvad.net","")
        iid   = self.tree.insert("", tk.END,
                                 values=(short, grp,"…","…","…","…","…","","pinging…"),
                                 tags=("dead",))
        self._row_ids[server] = iid
        self._row_dots[server] = []

    def _animate_row(self, server, dots):
        iid = self._row_ids.get(server)
        if not iid: return
        # Build a mini sparkline string from received packet times
        bar_chars = " ▁▂▃▄▅▆▇█"
        anim = ""
        for ms in dots:
            if ms is None:
                anim += "✗"
            else:
                idx = min(8, max(1, int(ms / 20)))
                anim += bar_chars[idx]
        self.tree.set(iid, "Live", anim)
        if dots:
            valid = [x for x in dots if x is not None]
            if valid:
                cur_avg = sum(valid)/len(valid)
                self.tree.set(iid, "Avg ms", f"{cur_avg:.1f}")
                tag = ms_tag(cur_avg)
                self.tree.item(iid, tags=(tag,))

    def _finalise_row(self, server, result):
        iid   = self._row_ids.get(server)
        if not iid: return
        short = server.replace(".mullvad.net","")
        grp   = get_server_group(server, self.current_region)
        thr   = self.threshold_ms.get()
        if result is None:
            vals = (short,grp,"--","--","--","--","100%","","✗  UNREACHABLE")
            tag  = "dead"
        else:
            avg, mn, mx, loss, jitter = result
            tag = ms_tag(avg)
            # Threshold alert
            if self.threshold_on.get() and avg > thr:
                tag = "alert"
                self.status_var.set(f"⚠ {short} exceeds threshold: {avg:.1f}ms > {thr:.0f}ms")
            status_map = {"good":"● EXCELLENT","ok":"● GOOD",
                          "slow":"● SLOW","bad":"● HIGH LAT","alert":"⚠ ALERT"}
            vals = (short, grp, f"{avg:.1f}", f"{mn:.1f}", f"{mx:.1f}",
                    f"{jitter:.1f}", f"{loss}%", "", status_map.get(tag,"--"))
        self.tree.item(iid, values=vals, tags=(tag,))

    def _finish(self):
        self.running = False
        servers = REGIONS[self.current_region]["servers"]
        self.status_var.set(f"Done — {len(servers)} servers tested.")
        self.btn.config(state=tk.NORMAL, text="▶  Run")

        reach = {s:d for s,d in self.results.items() if d}
        if reach:
            best_s  = min(reach, key=lambda s: reach[s][0])
            worst_s = max(reach, key=lambda s: reach[s][0])
            overall = sum(d[0] for d in reach.values()) / len(reach)
            avg_jit = sum(d[4] for d in reach.values()) / len(reach)
            def sh(s): return s.replace(".mullvad.net","").replace(
                f"us-{REGIONS[self.current_region]['code']}-","")
            bv,bs = self.cards["Best Server"]
            bv.config(text=sh(best_s), fg=T["green"])
            bs.config(text=f"{reach[best_s][0]:.1f}ms avg")
            wv,ws = self.cards["Worst Server"]
            wv.config(text=sh(worst_s), fg=T["red"])
            ws.config(text=f"{reach[worst_s][0]:.1f}ms avg")
            av,as_ = self.cards["Avg Latency"]
            av.config(text=f"{overall:.1f}ms", fg=ping_color(overall))
            as_.config(text=f"{len(reach)} servers")
            jv,js = self.cards["Avg Jitter"]
            jv.config(text=f"{avg_jit:.1f}ms", fg=T["yellow"])
            js.config(text="max−min range")
            rv,rs = self.cards["Reachable"]
            rv.config(text=f"{len(reach)}/{len(servers)}", fg=T["accent"])
            rs.config(text=f"{len(servers)-len(reach)} unreachable")

        self._draw_stats()
        df = self._build_dataframe()
        self._draw_static_map(df if not df.empty else None)
        self.map_btn.config(state=tk.NORMAL)

        # Save to history
        rows = []
        for s, d in self.results.items():
            if d:
                avg,mn,mx,loss,jitter = d
                rows.append({"server":s,"grp":get_server_group(s,self.current_region),
                             "avg":avg,"min":mn,"max":mx,"loss":loss,"jitter":jitter})
        db_save_run(self.current_region, int(self.ping_count.get()), rows)

    # ── DATAFRAME ─────────────────────────────────────────────────────────────
    def _build_dataframe(self):
        rows = []
        for s, d in self.results.items():
            if d:
                avg,mn,mx,loss,jitter = d
                rows.append({"server":s,
                             "short": s.replace(".mullvad.net",""),
                             "Group": get_server_group(s, self.current_region),
                             "avg":avg,"min":mn,"max":mx,
                             "loss":loss,"jitter":jitter})
        return pd.DataFrame(rows)


    # ── STATISTICS ────────────────────────────────────────────────────────────
    def _draw_stats(self):
        df = self._build_dataframe()
        if df.empty: return
        if self._stats_canvas:
            self._stats_canvas.get_tk_widget().destroy()
        self._stats_ph.pack_forget()

        rc = {"axes.facecolor":T["bg2"],"figure.facecolor":T["bg"],
              "axes.edgecolor":T["bg3"],"axes.labelcolor":T["fg_dim"],
              "xtick.color":T["fg_dim"],"ytick.color":T["fg_dim"],
              "text.color":T["fg"],"grid.color":T["bg3"],
              "grid.linestyle":"--","grid.alpha":0.5}
        sns.set_theme(style="dark", rc=rc)
        grp_palette = {dc:v["color"] for dc,v in REGIONS[self.current_region]["datacenters"].items()}

        fig = plt.Figure(figsize=(16,9), facecolor=T["bg"])
        gs  = gridspec.GridSpec(2,3,figure=fig,hspace=0.52,wspace=0.40,
                                left=0.05,right=0.97,top=0.93,bottom=0.07)

        # 1 — Bar chart sorted by avg
        ax1 = fig.add_subplot(gs[0,:2])
        sdf = df.sort_values("avg").reset_index(drop=True)
        bar_cols = [grp_palette.get(g, T["accent"]) for g in sdf["Group"]]
        ax1.bar(range(len(sdf)), sdf["avg"], color=bar_cols, width=0.75, zorder=3)
        ax1.errorbar(range(len(sdf)), sdf["avg"],
                     yerr=[sdf["avg"]-sdf["min"], sdf["max"]-sdf["avg"]],
                     fmt="none", ecolor="#ffffff33", capsize=2, lw=0.8, zorder=4)
        # Threshold line
        thr = self.threshold_ms.get()
        if self.threshold_on.get():
            ax1.axhline(thr, color=T["red"], lw=1.2, ls="--", alpha=0.7,
                        label=f"Threshold {thr:.0f}ms")
            ax1.legend(fontsize=7, framealpha=0.15, labelcolor=T["fg"],
                       facecolor=T["bg3"], edgecolor=T["bg3"])
        ax1.set_xticks([]); ax1.set_facecolor(T["bg2"])
        ax1.set_title("Servers by Avg Latency", color=T["fg"], fontsize=11, pad=8)
        ax1.set_ylabel("ms", color=T["fg_dim"])
        handles = [mpatches.Patch(color=c,label=g) for g,c in grp_palette.items()
                   if g in df["Group"].values]
        ax1.legend(handles=handles, fontsize=7, framealpha=0.15,
                   labelcolor=T["fg"], facecolor=T["bg3"], edgecolor=T["bg3"])

        # 2 — KDE
        ax2 = fig.add_subplot(gs[0,2])
        for grp, gcol in grp_palette.items():
            sub = df[df["Group"]==grp]["avg"]
            if len(sub)>=2: sns.kdeplot(sub,ax=ax2,color=gcol,fill=True,alpha=0.3,lw=1.5,label=grp)
            elif len(sub)==1: ax2.axvline(sub.iloc[0],color=gcol,lw=1.5)
        ax2.set_title("Latency Distribution (KDE)",color=T["fg"],fontsize=11,pad=8)
        ax2.set_xlabel("ms",color=T["fg_dim"]); ax2.set_ylabel("",color=T["fg_dim"])
        ax2.set_facecolor(T["bg2"])

        # 3 — Jitter box plot
        ax3 = fig.add_subplot(gs[1,0])
        grp_order  = [g for g in grp_palette if g in df["Group"].values]
        grp_colors = [grp_palette[g] for g in grp_order]
        sns.boxplot(data=df,x="Group",y="jitter",ax=ax3,order=grp_order,
                    palette=grp_colors,linewidth=1.2,
                    flierprops={"marker":"o","markersize":3,"markerfacecolor":T["fg_dim"]})
        ax3.set_xticklabels([g.split(" ")[0] if " " in g else g for g in grp_order],fontsize=7)
        ax3.set_title("Jitter by Group",color=T["fg"],fontsize=11,pad=8)
        ax3.set_xlabel("",color=T["fg_dim"]); ax3.set_ylabel("Jitter ms",color=T["fg_dim"])
        ax3.set_facecolor(T["bg2"])

        # 4 — Min vs Max scatter
        ax4 = fig.add_subplot(gs[1,1])
        for grp, gcol in grp_palette.items():
            sub = df[df["Group"]==grp]
            if not sub.empty:
                ax4.scatter(sub["min"],sub["max"],color=gcol,s=55,alpha=0.85,zorder=3)
        mn_,mx_ = df["min"].min(), df["max"].max()
        ax4.plot([mn_,mx_],[mn_,mx_],color="#ffffff22",lw=1,ls="--")
        ax4.set_title("Min vs Max Latency",color=T["fg"],fontsize=11,pad=8)
        ax4.set_xlabel("Min ms",color=T["fg_dim"]); ax4.set_ylabel("Max ms",color=T["fg_dim"])
        ax4.set_facecolor(T["bg2"])

        # 5 — Loss heatmap
        ax5 = fig.add_subplot(gs[1,2])
        hm_df = df[["short","loss"]].set_index("short")
        n = len(hm_df); cols_n = 4; rows_n = -(-n//cols_n)
        grid = np.full((rows_n,cols_n),np.nan)
        annots = [[""]*cols_n for _ in range(rows_n)]
        code = REGIONS[self.current_region]["code"]
        for idx,(nm,row) in enumerate(hm_df.iterrows()):
            r,c = divmod(idx,cols_n)
            grid[r,c] = row["loss"]
            annots[r][c] = nm.replace(f"us-{code}-wg-","")
        im = sns.heatmap(grid,ax=ax5,cmap="YlOrRd",vmin=0,vmax=100,
                         linewidths=0.5,linecolor=T["bg"],
                         annot=annots,fmt="s",annot_kws={"size":6,"color":T["fg"]},
                         cbar_kws={"label":"Loss %","shrink":0.8})
        ax5.set_title("Packet Loss Heatmap",color=T["fg"],fontsize=11,pad=8)
        ax5.set_xticks([]); ax5.set_yticks([]); ax5.set_facecolor(T["bg2"])
        cbar = im.collections[0].colorbar
        cbar.ax.yaxis.label.set_color(T["fg_dim"])
        cbar.ax.tick_params(colors=T["fg_dim"])

        canvas = FigureCanvasTkAgg(fig, master=self._stats_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._stats_canvas = canvas
        plt.close(fig)

    # ── STATIC MAP ────────────────────────────────────────────────────────────
    def _draw_static_map(self, df):
        if self._map_canvas:
            self._map_canvas.get_tk_widget().destroy()
        region = REGIONS[self.current_region]
        loc    = self._user_loc
        dcs    = region["datacenters"]

        if loc:
            lats = [loc["lat"]] + [dc["lat"] for dc in dcs.values()]
            lons = [loc["lon"]] + [dc["lon"] for dc in dcs.values()]
            lp = max((max(lats)-min(lats))*0.25,0.5)
            lo = max((max(lons)-min(lons))*0.25,0.5)
            xlim = (min(lons)-lo, max(lons)+lo)
            ylim = (min(lats)-lp, max(lats)+lp)
        else:
            cx,cy = region["center"]
            xlim = (cx-1.2, cx+1.2) if "lon" not in region else (cx-0.8,cx+0.8)
            # derive from center
            xlim = (region["center"][1]-1.2, region["center"][1]+1.2)
            ylim = (region["center"][0]-0.8, region["center"][0]+0.8)

        fig, ax = plt.subplots(figsize=(14,5.5), facecolor=T["bg"])
        ax.set_facecolor(T["bg2"])
        ax.set_xlim(*xlim); ax.set_ylim(*ylim)
        title = f"{self.current_region} — Mullvad WireGuard Datacenters"
        if loc:
            city = loc.get("city","")
            title += f"  ·  You: {city}"
        ax.set_title(title, color=T["fg"], fontsize=11, pad=8)
        ax.set_xlabel("Longitude",color=T["fg_dim"]); ax.set_ylabel("Latitude",color=T["fg_dim"])
        ax.tick_params(colors=T["fg_dim"])
        for sp in ax.spines.values(): sp.set_edgecolor(T["bg3"])
        ax.grid(True, color=T["bg3"], ls="--", alpha=0.4)

        if loc:
            ulat, ulon = loc["lat"], loc["lon"]
            for dc in dcs.values():
                ax.plot([ulon,dc["lon"]],[ulat,dc["lat"]],
                        color="#ffffff10",lw=0.9,ls="--",zorder=3)
                dist = haversine_km(ulat,ulon,dc["lat"],dc["lon"])
                mx2 = (ulon+dc["lon"])/2; my2 = (ulat+dc["lat"])/2
                ax.text(mx2,my2,f"{dist:.0f}km",color="#ffffff35",fontsize=6,
                        ha="center",va="center",zorder=4,
                        bbox=dict(boxstyle="round,pad=0.2",facecolor=T["bg"],edgecolor="none",alpha=0.55))
            for r,a in [(0.06,0.1),(0.04,0.2),(0.02,0.5)]:
                ax.add_patch(plt.Circle((ulon,ulat),r,color=T["orange"],fill=False,alpha=a,lw=1.1,zorder=8))
            ax.scatter(ulon,ulat,s=130,color=T["orange"],zorder=9,edgecolors="#fff8",linewidths=1.4)
            ax.plot(ulon,ulat,"+",color="#fff",markersize=8,markeredgewidth=1.4,zorder=10)
            label = f"YOU\n{loc.get('city','')}"
            ax.annotate(label,(ulon,ulat),xytext=(12,-18),textcoords="offset points",
                        color=T["fg"],fontsize=7.5,fontweight="bold",
                        bbox=dict(boxstyle="round,pad=0.4",facecolor=T["bg3"],edgecolor=T["orange"],alpha=0.92,lw=1.4),zorder=11)

        grp_palette = {dc:v["color"] for dc,v in dcs.items()}
        for dc_name, dc in dcs.items():
            if df is not None and not df.empty:
                rows     = df[df["Group"]==dc_name]
                avg_ping = rows["avg"].mean() if not rows.empty else None
                reach    = len(rows)
            else:
                avg_ping = None
                lo_,hi_  = dc["ranges"][0]
                reach    = sum(hi-lo+1 for lo,hi in dc["ranges"])
            color = dc["color"] if avg_ping is None else ping_color(avg_ping)
            size  = 300 + reach*110
            label = f"{dc_name}\n{reach} srv"
            if avg_ping: label += f"\n{avg_ping:.1f}ms"
            if loc:
                dist = haversine_km(loc["lat"],loc["lon"],dc["lat"],dc["lon"])
                label += f"\n{dist:.0f}km"
            ax.scatter(dc["lon"],dc["lat"],s=size,color=color,alpha=0.7,zorder=5,
                       edgecolors="#ffffff44",linewidths=1.4)
            ax.plot(dc["lon"],dc["lat"],"+",color=color,markersize=8,zorder=6,markeredgewidth=2)
            ax.annotate(label,(dc["lon"],dc["lat"]),xytext=(12,12),textcoords="offset points",
                        color=T["fg"],fontsize=7,
                        bbox=dict(boxstyle="round,pad=0.35",facecolor=T["bg3"],edgecolor=color,alpha=0.9),zorder=7)

        legend_items = [mpatches.Patch(color=dc["color"],label=n) for n,dc in dcs.items()]
        if loc: legend_items.append(mpatches.Patch(color=T["orange"],label=f"You ({loc.get('city','')})"))
        ax.legend(handles=legend_items,fontsize=7,framealpha=0.2,
                  labelcolor=T["fg"],facecolor=T["bg3"],edgecolor=T["bg3"],loc="lower right")

        canvas = FigureCanvasTkAgg(fig, master=self._map_frame)
        canvas.draw(); canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._map_canvas = canvas; plt.close(fig)

        # Update DC legend cards
        if df is not None and not df.empty:
            for dc_name, lbl in self._dc_stat_labels.items():
                dc = dcs.get(dc_name)
                if not dc: continue
                rows = df[df["Group"]==dc_name]
                if not rows.empty:
                    lbl.config(text=f"{len(rows)} srv | {rows['avg'].mean():.1f}ms avg")
                else:
                    lbl.config(text="0 reachable")


    # ── FOLIUM MAP ────────────────────────────────────────────────────────────
    def _open_folium(self):
        df  = self._build_dataframe()
        loc = self._user_loc
        region = REGIONS[self.current_region]
        dcs    = region["datacenters"]

        if loc:
            center = [(loc["lat"]+region["center"][0])/2,
                      (loc["lon"]+region["center"][1])/2]
            zoom = 7 if abs(loc["lat"]-region["center"][0]) > 2 else 10
        else:
            center = region["center"]; zoom = region["zoom"]

        m = folium.Map(location=center, zoom_start=zoom, tiles="CartoDB dark_matter")

        if loc:
            ulat, ulon = loc["lat"], loc["lon"]
            src = "IP-based" if loc.get("source")=="ip" else "Address geocoded"
            popup_html = (f"<b style='color:{T['orange']}'>Your Location</b><br>"
                          f"{loc.get('city','')}, {loc.get('region','')}, {loc.get('country','')}<br>"
                          f"{ulat:.5f}, {ulon:.5f}<br>"
                          f"<i style='font-size:10px;color:#888'>{src}</i>")
            for dc in dcs.values():
                dist = haversine_km(ulat,ulon,dc["lat"],dc["lon"])
                rows = df[df["Group"]==list(dcs.keys())[list(dcs.values()).index(dc)]] if not df.empty else pd.DataFrame()
                avg  = rows["avg"].mean() if not rows.empty else None
                folium.PolyLine([[ulat,ulon],[dc["lat"],dc["lon"]]],
                                color=ping_folium(avg),weight=1.5,opacity=0.45,
                                dash_array="6 4",
                                tooltip=f"{dist:.0f}km" + (f" · {avg:.1f}ms" if avg else "")).add_to(m)
            for r,op in [(8000,0.12),(3500,0.25)]:
                folium.Circle([ulat,ulon],radius=r,color=T["orange"],
                              fill=True,fill_color=T["orange"],fill_opacity=op).add_to(m)
            folium.Marker([ulat,ulon],
                          popup=folium.Popup(popup_html,max_width=250),
                          tooltip=f"You — {loc.get('city','')}",
                          icon=folium.DivIcon(html=(
                              f"<div style='background:{T['orange']};color:#000;font-weight:bold;"
                              f"font-size:11px;padding:4px 9px;border-radius:50%;"
                              f"border:2px solid #fff'>YOU</div>"))).add_to(m)

        np.random.seed(42)
        for dc_name, dc in dcs.items():
            servers = [s for s in region["servers"]
                       if get_server_group(s,self.current_region)==dc_name]
            rows = df[df["Group"]==dc_name] if not df.empty else pd.DataFrame()
            avg  = rows["avg"].mean() if not rows.empty else None
            reach= len(rows)
            dist_str = ""
            if loc:
                d = haversine_km(loc["lat"],loc["lon"],dc["lat"],dc["lon"])
                dist_str = f"<br><b>{d:.0f}km</b> from you"
            tip = (f"<b style='color:{dc['color']}'>{dc_name}</b><br>{dc['location']}<br>"
                   f"Servers: {reach}/{len(servers)}<br>"
                   + (f"Avg: <b>{avg:.1f}ms</b>" if avg else "No data") + dist_str)
            folium.Circle([dc["lat"],dc["lon"]],radius=800+reach*280,
                          color=dc["color"],fill=True,fill_color=dc["color"],
                          fill_opacity=0.3,popup=folium.Popup(tip,max_width=240),
                          tooltip=dc_name).add_to(m)
            folium.Marker([dc["lat"],dc["lon"]],
                          popup=folium.Popup(tip,max_width=240),tooltip=dc_name,
                          icon=folium.DivIcon(html=(
                              f"<div style='background:{dc['color']};color:#000;"
                              f"font-weight:bold;font-size:10px;padding:3px 7px;"
                              f"border-radius:4px;white-space:nowrap'>"
                              f"{dc_name}" + (f" | {avg:.0f}ms" if avg else "") + "</div>"
                          ))).add_to(m)
            for s in servers:
                jlat = dc["lat"] + np.random.uniform(-0.013,0.013)
                jlon = dc["lon"] + np.random.uniform(-0.016,0.016)
                row  = df[df["server"]==s] if not df.empty else pd.DataFrame()
                a    = row["avg"].values[0] if not row.empty else None
                short = s.replace(".mullvad.net","").replace(f"us-{region['code']}-","")
                folium.CircleMarker([jlat,jlon],radius=5,color=ping_folium(a),
                                    fill=True,fill_color=ping_folium(a),fill_opacity=0.85,
                                    tooltip=f"{short}: {a:.1f}ms" if a else f"{short}: --").add_to(m)

        tmp = tempfile.NamedTemporaryFile(suffix=".html",delete=False,mode="w")
        self._map_tmp = tmp.name; tmp.close()
        m.save(self._map_tmp); webbrowser.open(f"file://{self._map_tmp}")

    # ── HISTORY ───────────────────────────────────────────────────────────────
    def _draw_history(self):
        df = db_load_history(self.current_region, limit=int(self._hist_runs.get()))
        if df.empty:
            self._hist_ph.config(text="No history yet for this region.")
            return
        filt = self._hist_sv.get().strip()
        if filt: df = df[df["server"].str.contains(filt, case=False)]
        if df.empty:
            self._hist_ph.config(text="No matching servers in history."); return

        if self._hist_canvas:
            self._hist_canvas.get_tk_widget().destroy()
        self._hist_ph.pack_forget()

        rc = {"axes.facecolor":T["bg2"],"figure.facecolor":T["bg"],
              "axes.edgecolor":T["bg3"],"axes.labelcolor":T["fg_dim"],
              "xtick.color":T["fg_dim"],"ytick.color":T["fg_dim"],
              "text.color":T["fg"],"grid.color":T["bg3"],"grid.linestyle":"--","grid.alpha":0.5}
        sns.set_theme(style="dark", rc=rc)

        top_servers = (df.groupby("server")["avg_ms"].mean()
                       .nsmallest(10).index.tolist())
        plot_df = df[df["server"].isin(top_servers)].copy()
        plot_df["ts"] = pd.to_datetime(plot_df["ts"])
        code = REGIONS[self.current_region]["code"]
        plot_df["short"] = plot_df["server"].str.replace(".mullvad.net","", regex=False)\
                                             .str.replace(f"us-{code}-","", regex=False)

        fig, axes = plt.subplots(1, 2, figsize=(14,5), facecolor=T["bg"])
        # Time-series
        ax1 = axes[0]
        ax1.set_facecolor(T["bg2"])
        for srv, grp in plot_df.groupby("short"):
            grp = grp.sort_values("ts")
            ax1.plot(grp["ts"], grp["avg_ms"], marker="o", markersize=3,
                     lw=1.4, label=srv, alpha=0.85)
        ax1.set_title("Latency Over Time (Top 10 servers)", color=T["fg"], fontsize=11, pad=8)
        ax1.set_xlabel("Time", color=T["fg_dim"]); ax1.set_ylabel("Avg ms", color=T["fg_dim"])
        ax1.legend(fontsize=7, framealpha=0.15, labelcolor=T["fg"],
                   facecolor=T["bg3"], edgecolor=T["bg3"])
        ax1.tick_params(axis="x", rotation=30)

        # Bar chart of overall averages
        ax2 = axes[1]
        ax2.set_facecolor(T["bg2"])
        means = df.groupby("server")["avg_ms"].mean().nsmallest(15)
        short_labels = [s.replace(".mullvad.net","").replace(f"us-{code}-","") for s in means.index]
        colors = [ping_color(v) for v in means.values]
        ax2.barh(short_labels[::-1], means.values[::-1], color=colors[::-1], zorder=3)
        ax2.set_title("Best 15 Servers (all-time avg)", color=T["fg"], fontsize=11, pad=8)
        ax2.set_xlabel("Avg ms", color=T["fg_dim"])

        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self._hist_frame)
        canvas.draw(); canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._hist_canvas = canvas; plt.close(fig)

    def _clear_history(self):
        if messagebox.askyesno("Clear History",
                               f"Delete all history for {self.current_region}?"):
            con = sqlite3.connect(DB_PATH)
            con.execute("DELETE FROM results WHERE run_id IN "
                        "(SELECT id FROM runs WHERE region=?)", (self.current_region,))
            con.execute("DELETE FROM runs WHERE region=?", (self.current_region,))
            con.commit(); con.close()
            self._hist_ph.config(text="History cleared.")
            self._hist_ph.pack(expand=True)
            if self._hist_canvas:
                self._hist_canvas.get_tk_widget().destroy()
                self._hist_canvas = None


    # ── STATISTICS ────────────────────────────────────────────────────────────
    def _draw_stats(self):
        df = self._build_dataframe()
        if df.empty: return
        if self._stats_ph.winfo_exists():
            self._stats_ph.pack_forget()
        if self._stats_canvas:
            self._stats_canvas.get_tk_widget().destroy()

        bg = T["bg"]; bg2 = T["bg2"]
        plt.style.use("dark_background" if T["name"]=="dark" else "default")
        fig  = plt.Figure(figsize=(13,8), facecolor=bg)
        gs   = gridspec.GridSpec(2,3, figure=fig, hspace=0.45, wspace=0.36)

        def ax_theme(ax, title):
            ax.set_facecolor(bg2)
            ax.set_title(title, color=T["fg"], fontsize=9, pad=6)
            ax.tick_params(colors=T["fg_dim"], labelsize=7)
            for sp in ax.spines.values(): sp.set_edgecolor(T["bg2"])

        acc = T["accent"]
        grp_colors = {g: dc["color"]
                      for dc_name, dc in REGIONS[self.current_region]["datacenters"].items()
                      for g in [dc_name]}

        # 1. Sorted bar chart
        ax1 = fig.add_subplot(gs[0,0])
        d   = df.sort_values("avg")
        cols_bar = [grp_colors.get(g, acc) for g in d["Group"]]
        ax1.barh(range(len(d)), d["avg"], color=cols_bar, height=0.7)
        ax1.set_xlabel("Avg ms", color=T["fg_dim"], fontsize=7)
        ax1.set_yticks(range(len(d)))
        lbs = [s.replace(".mullvad.net","").split("-wg-")[-1] for s in d["server"]]
        ax1.set_yticklabels(lbs, fontsize=6)
        ax1.axvline(df["avg"].mean(), color=T["yellow"], lw=1, ls="--", label="mean")
        ax_theme(ax1, "Servers by Avg Latency")

        # 2. KDE density
        ax2 = fig.add_subplot(gs[0,1])
        try:
            sns.kdeplot(data=df["avg"], ax=ax2, fill=True, color=acc, alpha=0.4)
            ax2.set_xlabel("ms", color=T["fg_dim"], fontsize=7)
        except Exception: pass
        ax_theme(ax2, "Latency Distribution")

        # 3. Box plot per group
        ax3 = fig.add_subplot(gs[0,2])
        grps = df.groupby("Group")["avg"].apply(list)
        bp   = ax3.boxplot(grps.values, patch_artist=True, medianprops=dict(color=T["bg"]))
        for i, patch in enumerate(bp["boxes"]):
            g = list(grps.index)[i]
            patch.set_facecolor(grp_colors.get(g, acc))
        ax3.set_xticklabels(list(grps.index), rotation=30, fontsize=6)
        ax_theme(ax3, "Latency by Datacenter")

        # 4. Jitter scatter
        ax4 = fig.add_subplot(gs[1,0])
        sc = ax4.scatter(df["avg"], df["jitter"], c=df["avg"],
                         cmap="RdYlGn_r", alpha=0.8, s=30)
        ax4.set_xlabel("Avg ms", color=T["fg_dim"], fontsize=7)
        ax4.set_ylabel("Jitter ms", color=T["fg_dim"], fontsize=7)
        ax_theme(ax4, "Avg Latency vs Jitter")

        # 5. Packet loss heatmap
        ax5 = fig.add_subplot(gs[1,1])
        heat = df.pivot_table(index="Group", values=["avg","loss"],
                              aggfunc="mean")
        sns.heatmap(heat, ax=ax5, cmap="coolwarm", annot=True, fmt=".1f",
                    linewidths=0.5, linecolor=T["bg3"], cbar=False,
                    annot_kws={"fontsize":7})
        ax5.set_xlabel(""); ax5.set_ylabel("")
        ax_theme(ax5, "Avg ms & Loss % by DC")

        # 6. Min/max error bars
        ax6 = fig.add_subplot(gs[1,2])
        d2  = df.sort_values("avg")
        x   = range(len(d2))
        ax6.bar(x, d2["avg"], color=acc, alpha=0.6, label="avg")
        ax6.errorbar(x, d2["avg"],
                     yerr=[d2["avg"]-d2["min"], d2["max"]-d2["avg"]],
                     fmt="none", color=T["yellow"], capsize=2, elinewidth=0.8)
        ax6.set_xticks(list(x)); ax6.set_xticklabels(
            [s.split("-")[-1] for s in d2["server"].str.replace(".mullvad.net","")],
            rotation=90, fontsize=5)
        ax_theme(ax6, "Min / Avg / Max per Server")

        fig.tight_layout(rect=[0,0,1,1])
        canvas = FigureCanvasTkAgg(fig, master=self._stats_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._stats_canvas = canvas

    # ── STATIC MAP ────────────────────────────────────────────────────────────
    def _draw_static_map(self, df=None):
        if self._map_canvas:
            self._map_canvas.get_tk_widget().destroy()
        region = REGIONS[self.current_region]
        dcs    = region["datacenters"]

        bg = T["bg"]; bg2 = T["bg2"]
        plt.style.use("dark_background" if T["name"]=="dark" else "default")
        fig, ax = plt.subplots(figsize=(9,6), facecolor=bg)
        ax.set_facecolor(bg)
        ax.tick_params(colors=T["fg_dim"], labelsize=7)
        for sp in ax.spines.values(): sp.set_edgecolor(T["bg3"])

        lats = [dc["lat"] for dc in dcs.values()]
        lons = [dc["lon"] for dc in dcs.values()]

        for dc_name, dc in dcs.items():
            avg_ms = None
            if df is not None and not df.empty:
                grp_df = df[df["Group"]==dc_name]
                if not grp_df.empty: avg_ms = grp_df["avg"].mean()
            color = ping_folium(avg_ms) if df is not None else dc["color"]
            ax.scatter(dc["lon"], dc["lat"], c=color, s=160, zorder=5,
                       edgecolors=T["bg"], linewidths=1.5)
            lbl = f"{dc_name}" + (f"\n{avg_ms:.1f}ms" if avg_ms else "")
            ax.annotate(lbl, (dc["lon"], dc["lat"]),
                        textcoords="offset points", xytext=(8,5),
                        fontsize=7, color=color)
            # Update card label
            sl = self._dc_stat_labels.get(dc_name)
            if sl:
                sl.config(text=f"{avg_ms:.1f}ms avg" if avg_ms else "")

        if self._user_loc:
            ulat = self._user_loc["lat"]; ulon = self._user_loc["lon"]
            lats.append(ulat); lons.append(ulon)
            city = self._user_loc.get("city","You")
            ax.scatter(ulon, ulat, c=T["orange"], s=100, zorder=6,
                       edgecolors="white", linewidths=1.5)
            ax.annotate(f"YOU\n{city}", (ulon, ulat),
                        textcoords="offset points", xytext=(-40,5),
                        fontsize=7, color=T["orange"])
            for dc in dcs.values():
                km = haversine_km(ulat, ulon, dc["lat"], dc["lon"])
                ax.plot([ulon, dc["lon"]], [ulat, dc["lat"]],
                        color=T["orange"], lw=0.7, ls="--", alpha=0.5, zorder=3)

        pad  = 0.4
        lat_mn,lat_mx = min(lats)-pad, max(lats)+pad
        lon_mn,lon_mx = min(lons)-pad*1.6, max(lons)+pad*1.6
        ax.set_xlim(lon_mn, lon_mx); ax.set_ylim(lat_mn, lat_mx)
        ax.set_xlabel("Longitude", color=T["fg_dim"], fontsize=7)
        ax.set_ylabel("Latitude",  color=T["fg_dim"], fontsize=7)
        ax.set_title(f"{self.current_region} — Datacenter Locations",
                     color=T["fg"], fontsize=9, pad=8)
        ax.grid(color=T["bg3"], lw=0.5)
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self._map_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._map_canvas = canvas
        plt.close(fig)

    # ── FOLIUM MAP ────────────────────────────────────────────────────────────
    def _open_folium(self):
        df     = self._build_dataframe()
        region = REGIONS[self.current_region]
        dcs    = region["datacenters"]
        c      = region["center"]
        m      = folium.Map(location=c, zoom_start=region["zoom"],
                            tiles="CartoDB dark_matter" if T["name"]=="dark"
                                   else "CartoDB positron")
        for dc_name, dc in dcs.items():
            grp_df = df[df["Group"]==dc_name] if not df.empty else pd.DataFrame()
            avg_ms = float(grp_df["avg"].mean()) if not grp_df.empty else None
            col    = ping_folium(avg_ms)
            rad    = 700
            folium.CircleMarker(
                location=[dc["lat"], dc["lon"]],
                radius=18, fill=True, fill_color=col,
                color="white", fill_opacity=0.8, weight=2,
                popup=folium.Popup(
                    f"<b>{dc_name}</b><br>{dc['location']}"
                    + (f"<br>Avg {avg_ms:.1f}ms" if avg_ms else ""), max_width=220),
                tooltip=dc_name).add_to(m)
            if not grp_df.empty:
                for _, row in grp_df.iterrows():
                    jitter_lat = dc["lat"] + (hash(row["server"]) % 100)/3000.0
                    jitter_lon = dc["lon"] + (hash(row["short"])  % 100)/3000.0
                    svcol = ping_folium(row["avg"])
                    folium.CircleMarker(
                        location=[jitter_lat, jitter_lon],
                        radius=5, fill=True, fill_color=svcol,
                        color="white", fill_opacity=0.9, weight=0.5,
                        tooltip=f"{row['short']}: {row['avg']:.1f}ms").add_to(m)
        if self._user_loc:
            ulat = self._user_loc["lat"]; ulon = self._user_loc["lon"]
            folium.CircleMarker(
                location=[ulat, ulon], radius=14,
                fill=True, fill_color=T["orange"],
                color="white", fill_opacity=0.9, weight=2,
                popup="YOU", tooltip="Your Location").add_to(m)
            for dc in dcs.values():
                km  = haversine_km(ulat, ulon, dc["lat"], dc["lon"])
                col = ping_folium(df[df["Group"]==dc_name]["avg"].mean()
                                  if not df.empty else None)
                folium.PolyLine(
                    [[ulat,ulon],[dc["lat"],dc["lon"]]],
                    color="#ff9500", weight=1.5,
                    dash_array="6 4", opacity=0.5,
                    tooltip=f"{km:.0f} km").add_to(m)
        tmp = tempfile.NamedTemporaryFile(suffix=".html", delete=False)
        m.save(tmp.name)
        self._map_tmp = tmp.name
        webbrowser.open(f"file://{tmp.name}")


    # ── TRACEROUTE ────────────────────────────────────────────────────────────
    def _start_traceroute(self):
        host = self._trace_sv.get().strip()
        if not host: return
        self._trace_text.config(state=tk.NORMAL)
        self._trace_text.delete("1.0",tk.END)
        self._trace_text.config(state=tk.DISABLED)
        if self._trace_canvas:
            self._trace_canvas.get_tk_widget().destroy()
            self._trace_canvas = None
        threading.Thread(target=lambda: run_traceroute(
            host, lambda hops, **kw: self.after(0, self._on_trace_update, hops)),
            daemon=True).start()

    def _trace_use_best(self):
        if self.results:
            reach = {s:d for s,d in self.results.items() if d}
            if reach:
                best = min(reach, key=lambda s: reach[s][0])
                self._trace_sv.set(best)

    def _on_trace_update(self, hops):
        self._trace_text.config(state=tk.NORMAL)
        self._trace_text.delete("1.0", tk.END)
        for h in hops:
            times = h.get("times",[])
            def fmt(t): return f"{t:.1f}ms" if t is not None else "  *  "
            ts_str = "  ".join(fmt(t) for t in times)
            avg_t  = [t for t in times if t is not None]
            avg    = sum(avg_t)/len(avg_t) if avg_t else None
            tag    = "good" if avg and avg<30 else ("slow" if avg and avg<100 else "bad")
            line   = f"  {h['hop']:>2}  {h['ip']:<16}  {ts_str}\n"
            self._trace_text.insert(tk.END, f"  {h['hop']:>2}  ", "hop")
            self._trace_text.insert(tk.END, f"{h['ip']:<18}", ())
            self._trace_text.insert(tk.END, f"{ts_str}\n", tag)
        self._trace_text.config(state=tk.DISABLED)
        # Draw bar chart of hop latencies
        self._draw_trace_chart(hops)

    def _draw_trace_chart(self, hops):
        if self._trace_canvas:
            self._trace_canvas.get_tk_widget().destroy()
        avgs = []
        labels = []
        for h in hops:
            ts = [t for t in h.get("times",[]) if t is not None]
            avgs.append(sum(ts)/len(ts) if ts else 0)
            labels.append(f"{h['hop']} {h['ip']}")

        fig, ax = plt.subplots(figsize=(7,5), facecolor=T["bg"])
        ax.set_facecolor(T["bg2"])
        colors = [ping_color(v) for v in avgs]
        ax.barh(labels[::-1], avgs[::-1], color=colors[::-1], zorder=3)
        ax.set_xlabel("Avg ms", color=T["fg_dim"])
        ax.set_title("Traceroute Hop Latency", color=T["fg"], fontsize=11, pad=8)
        ax.tick_params(colors=T["fg_dim"])
        for sp in ax.spines.values(): sp.set_edgecolor(T["bg3"])
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self._trace_plot_frame)
        canvas.draw(); canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._trace_canvas = canvas; plt.close(fig)

    # ── SPEED TEST ────────────────────────────────────────────────────────────
    def _start_speedtest(self):
        url_key = self._speed_src.get()
        url     = SPEED_URLS.get(url_key, list(SPEED_URLS.values())[0])
        self._speed_prog.configure(value=0)
        self._speed_status.config(text="Running…")
        for lbl in self._speed_cards.values():
            lbl.config(text="--")
        def progress(pct, mbps):
            self.after(0, lambda: (
                self._speed_prog.configure(value=pct),
                self._speed_status.config(text=f"{mbps:.1f} Mbps  {pct}%")
            ))
        def done(avg, peak, total_mb, elapsed, error=None):
            self.after(0, self._on_speed_done, avg, peak, total_mb, elapsed, error)
        threading.Thread(target=run_speed_test,
                         args=(url, progress, done), daemon=True).start()

    def _on_speed_done(self, avg, peak, total_mb, elapsed, error=None):
        self._speed_prog.configure(value=100)
        if error:
            self._speed_status.config(text=f"Error: {error}", fg=T["red"]); return
        self._speed_status.config(text="Done", fg=T["green"])
        self._speed_cards["Avg Speed"].config(
            text=f"{avg:.1f} Mbps", fg=ping_color(200/max(avg,0.01)))
        self._speed_cards["Peak Speed"].config(text=f"{peak:.1f} Mbps", fg=T["green"])
        self._speed_cards["Total Downloaded"].config(text=f"{total_mb:.2f} MB", fg=T["accent"])
        self._speed_cards["Time"].config(text=f"{elapsed:.1f}s", fg=T["fg_dim"])
        self._speed_ph.pack_forget()
        self._draw_speed_gauge(avg, peak)

    def _draw_speed_gauge(self, avg, peak):
        if self._speed_canvas:
            self._speed_canvas.get_tk_widget().destroy()
        fig, axes = plt.subplots(1, 2, figsize=(10,4), facecolor=T["bg"])
        fig.suptitle("Speed Test Results", color=T["fg"], fontsize=12)
        for ax, val, title, col in [
            (axes[0], avg, "Avg Throughput (Mbps)", ping_color(200/max(avg,0.01))),
            (axes[1], peak,"Peak Throughput (Mbps)", T["green"]),
        ]:
            ax.set_facecolor(T["bg2"])
            wedge_val = min(val, 500)
            ax.pie([wedge_val, max(0,500-wedge_val)],
                   colors=[col, T["bg3"]],
                   startangle=90, counterclock=False,
                   wedgeprops={"width":0.38})
            ax.text(0, 0, f"{val:.1f}", ha="center", va="center",
                    color=T["fg"], fontsize=18, fontweight="bold")
            ax.text(0, -0.55, "Mbps", ha="center", color=T["fg_dim"], fontsize=9)
            ax.set_title(title, color=T["fg"], fontsize=10)
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self._speed_frame)
        canvas.draw(); canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._speed_canvas = canvas; plt.close(fig)

    # ── COMPARE ───────────────────────────────────────────────────────────────
    def _save_run_a(self):
        self.compare_a = copy.deepcopy(self.results)
        ts = datetime.now().strftime("%H:%M:%S")
        self._cmp_a_lbl.config(text=f"Run A: {ts}", fg=T["green"])

    def _save_run_b(self):
        self.compare_b = copy.deepcopy(self.results)
        ts = datetime.now().strftime("%H:%M:%S")
        self._cmp_b_lbl.config(text=f"Run B: {ts}", fg=T["accent"])

    def _show_compare(self):
        if not self.compare_a or not self.compare_b:
            messagebox.showinfo("Compare", "Save two runs first (Run A and Run B).")
            return
        self._cmp_ph.pack_forget()
        if self._cmp_tree:
            self._cmp_tree.destroy()
        cols = ("Server","Run A avg","Run B avg","Delta","Δ Jitter","Winner")
        widths = [200,90,90,90,90,120]
        f = self._cmp_frame
        self._cmp_tree = ttk.Treeview(f, columns=cols, show="headings")
        for col, w in zip(cols, widths):
            self._cmp_tree.heading(col, text=col)
            self._cmp_tree.column(col, width=w, anchor="center")
        all_servers = sorted(set(list(self.compare_a)+list(self.compare_b)))
        for s in all_servers:
            a = self.compare_a.get(s); b = self.compare_b.get(s)
            a_avg = f"{a[0]:.1f}" if a else "--"
            b_avg = f"{b[0]:.1f}" if b else "--"
            if a and b:
                delta = b[0] - a[0]
                dj    = b[4] - a[4]
                delta_str = f"{delta:+.1f}"
                dj_str    = f"{dj:+.1f}"
                winner = "A" if a[0] < b[0] else ("B" if b[0] < a[0] else "Tie")
                tag = "good" if delta < 0 else ("bad" if delta > 5 else "ok")
            else:
                delta_str = "--"; dj_str = "--"; winner = "--"; tag = "dead"
            short = s.replace(".mullvad.net","")
            self._cmp_tree.insert("", tk.END,
                                  values=(short, a_avg, b_avg, delta_str, dj_str, winner),
                                  tags=(tag,))
        for tag, col in [("good",T["green"]),("ok",T["accent"]),
                         ("bad",T["red"]),("dead",T["fg_dim"])]:
            self._cmp_tree.tag_configure(tag, foreground=col)
        sb = ttk.Scrollbar(f, orient=tk.VERTICAL, command=self._cmp_tree.yview)
        self._cmp_tree.configure(yscrollcommand=sb.set)
        self._cmp_tree.pack(fill=tk.BOTH, expand=True, side=tk.LEFT)
        sb.pack(fill=tk.Y, side=tk.RIGHT)
        self.nb.select(6)  # switch to compare tab


    # ── HISTORY ───────────────────────────────────────────────────────────────
    def _draw_history(self):
        server_filter = self._hist_sv.get().strip()
        limit = int(self._hist_runs.get())
        df = db_load_history(self.current_region, limit)
        if df.empty:
            messagebox.showinfo("History", "No history found for this region."); return
        if server_filter:
            df = df[df["server"].str.contains(server_filter, case=False)]
            if df.empty:
                messagebox.showinfo("History", f"No results for '{server_filter}'."); return
        if self._hist_ph.winfo_exists():
            self._hist_ph.pack_forget()
        if self._hist_canvas:
            self._hist_canvas.get_tk_widget().destroy()
        bg = T["bg"]; bg2 = T["bg2"]
        plt.style.use("dark_background" if T["name"]=="dark" else "default")
        fig, axes = plt.subplots(1, 2, figsize=(13,5), facecolor=bg)
        for ax in axes:
            ax.set_facecolor(bg2)
            ax.tick_params(colors=T["fg_dim"], labelsize=7)
            for sp in ax.spines.values(): sp.set_edgecolor(T["bg3"])
        df["ts"] = pd.to_datetime(df["ts"])
        # Top 8 servers by frequency
        top = df.groupby("server")["avg_ms"].mean().sort_values().head(8).index
        for sv in top:
            sv_df = df[df["server"]==sv].sort_values("ts")
            short = sv.replace(".mullvad.net","").split("-wg-")[-1]
            axes[0].plot(sv_df["ts"], sv_df["avg_ms"],
                         marker="o", markersize=3, linewidth=1.2,
                         label=short)
        axes[0].set_xlabel("Time", color=T["fg_dim"], fontsize=7)
        axes[0].set_ylabel("Avg ms", color=T["fg_dim"], fontsize=7)
        axes[0].set_title("Latency Over Time (top 8 servers)",
                          color=T["fg"], fontsize=9)
        axes[0].legend(fontsize=6, facecolor=bg2, labelcolor=T["fg_dim"])
        axes[0].tick_params(axis="x", rotation=30)
        # Per-run averages
        runs_df = db_load_runs(self.current_region, limit)
        if not runs_df.empty:
            run_avgs = []
            con = sqlite3.connect(DB_PATH)
            for _, row in runs_df.iterrows():
                r_df = pd.read_sql_query(
                    "SELECT avg_ms FROM results WHERE run_id=?",
                    con, params=(row["id"],))
                run_avgs.append({"ts":row["ts"],"overall":r_df["avg_ms"].mean()})
            con.close()
            ra = pd.DataFrame(run_avgs)
            if not ra.empty:
                ra["ts"] = pd.to_datetime(ra["ts"])
                ra = ra.sort_values("ts")
                axes[1].plot(ra["ts"], ra["overall"], color=T["accent"],
                             marker="o", markersize=4, linewidth=1.5)
                axes[1].fill_between(ra["ts"], ra["overall"],
                                     alpha=0.2, color=T["accent"])
                axes[1].set_title("Overall Avg per Run", color=T["fg"], fontsize=9)
                axes[1].set_xlabel("Time", color=T["fg_dim"], fontsize=7)
                axes[1].set_ylabel("Avg ms", color=T["fg_dim"], fontsize=7)
                axes[1].tick_params(axis="x", rotation=30)
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self._hist_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._hist_canvas = canvas
        plt.close(fig)

    def _clear_history(self):
        if messagebox.askyesno("Clear History",
                               f"Delete all history for {self.current_region}?"):
            con = sqlite3.connect(DB_PATH)
            runs = pd.read_sql_query(
                "SELECT id FROM runs WHERE region=?", con,
                params=(self.current_region,))
            for rid in runs["id"]:
                con.execute("DELETE FROM results WHERE run_id=?", (rid,))
                con.execute("DELETE FROM runs WHERE id=?", (rid,))
            con.commit(); con.close()
            messagebox.showinfo("Done","History cleared.")

    # ── TRACEROUTE ────────────────────────────────────────────────────────────
    def _trace_use_best(self):
        reach = {s:d for s,d in self.results.items() if d}
        if not reach:
            messagebox.showinfo("No data","Run a ping test first."); return
        best = min(reach, key=lambda s: reach[s][0])
        self._trace_sv.set(best)

    def _start_traceroute(self):
        host = self._trace_sv.get().strip()
        if not host: return
        self._trace_text.config(state=tk.NORMAL)
        self._trace_text.delete("1.0", tk.END)
        self._trace_text.insert(tk.END, f"traceroute to {host}\n\n")
        self._trace_text.config(state=tk.DISABLED)
        if self._trace_canvas:
            self._trace_canvas.get_tk_widget().destroy()
            self._trace_canvas = None
        threading.Thread(target=lambda: run_traceroute(host, self._on_trace_update),
                         daemon=True).start()

    def _on_trace_update(self, hops, error=None):
        self.after(0, self._render_trace, hops, error)

    def _render_trace(self, hops, error=None):
        t = self._trace_text
        t.config(state=tk.NORMAL)
        t.delete("1.0", tk.END)
        for h in hops:
            hop_n = h["hop"]; ip = h["ip"]
            times = h.get("times", [])
            valid = [x for x in times if x is not None]
            avg   = sum(valid)/len(valid) if valid else None
            tag   = ms_tag(avg) if avg is not None else "dead"
            times_str = "  ".join(
                (f"{x:.1f}ms" if x is not None else "  *  ") for x in times)
            t.insert(tk.END, f"{hop_n:>3}  ", "hop")
            t.insert(tk.END, f"{ip:<18}  ", tag)
            t.insert(tk.END, f"{times_str}\n", tag)
        if error:
            t.insert(tk.END, f"\nError: {error}\n", "bad")
        t.config(state=tk.DISABLED)
        # Draw hop bar chart
        if not hops: return
        if self._trace_canvas:
            self._trace_canvas.get_tk_widget().destroy()
        bg = T["bg"]; bg2 = T["bg2"]
        plt.style.use("dark_background" if T["name"]=="dark" else "default")
        fig, ax = plt.subplots(figsize=(6,max(3,len(hops)*0.28+1)), facecolor=bg)
        ax.set_facecolor(bg2)
        ax.tick_params(colors=T["fg_dim"], labelsize=7)
        for sp in ax.spines.values(): sp.set_edgecolor(T["bg3"])
        y   = [h["hop"] for h in hops]
        avgs= []
        for h in hops:
            valid = [x for x in h.get("times",[]) if x is not None]
            avgs.append(sum(valid)/len(valid) if valid else 0)
        bar_cols = [ping_folium(a if a else None) for a in avgs]
        ax.barh(y, avgs, color=bar_cols, height=0.7)
        ax.set_xlabel("Avg ms", color=T["fg_dim"], fontsize=7)
        ax.set_ylabel("Hop",    color=T["fg_dim"], fontsize=7)
        ax.set_title("Traceroute Hop Latency", color=T["fg"], fontsize=9)
        ax.invert_yaxis()
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self._trace_plot_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._trace_canvas = canvas
        plt.close(fig)

    # ── SPEED TEST ────────────────────────────────────────────────────────────
    def _start_speedtest(self):
        src = self._speed_src.get()
        url = SPEED_URLS.get(src, SPEED_URLS[DEFAULT_SPEED_URL])
        self._speed_status.config(text="Testing…")
        self._speed_prog.configure(value=0)
        if self._speed_ph.winfo_exists(): self._speed_ph.pack_forget()

        def prog(pct, mbps):
            self.after(0, self._speed_prog.configure, {"value":pct})
            self.after(0, self._speed_status.config, {"text":f"{mbps:.1f} Mbps"})

        def done(avg, peak, total_mb, elapsed, error=None):
            self.after(0, self._on_speed_done, avg, peak, total_mb, elapsed, error)

        threading.Thread(target=lambda: run_speed_test(url, prog, done),
                         daemon=True).start()

    def _on_speed_done(self, avg, peak, total_mb, elapsed, error=None):
        self._speed_prog.configure(value=100)
        if error:
            self._speed_status.config(text=f"Error: {error}", fg=T["red"]); return
        self._speed_status.config(text="Complete.", fg=T["green"])
        self._speed_cards["Avg Speed"].config(text=f"{avg:.1f} Mbps")
        self._speed_cards["Peak Speed"].config(text=f"{peak:.1f} Mbps")
        self._speed_cards["Total Downloaded"].config(text=f"{total_mb:.1f} MB")
        self._speed_cards["Time"].config(text=f"{elapsed:.1f} s")
        # Mini chart
        if self._speed_canvas:
            self._speed_canvas.get_tk_widget().destroy()
        bg = T["bg"]; bg2 = T["bg2"]
        plt.style.use("dark_background" if T["name"]=="dark" else "default")
        fig, ax = plt.subplots(figsize=(8,3), facecolor=bg)
        ax.set_facecolor(bg2)
        ax.tick_params(colors=T["fg_dim"], labelsize=7)
        for sp in ax.spines.values(): sp.set_edgecolor(T["bg3"])
        bar_data = {"Avg":avg,"Peak":peak}
        bars = ax.bar(list(bar_data.keys()), list(bar_data.values()),
                      color=[T["accent"], T["green"]], width=0.4)
        for b in bars:
            ax.text(b.get_x()+b.get_width()/2, b.get_height()+0.3,
                    f"{b.get_height():.1f}", ha="center", fontsize=8,
                    color=T["fg"])
        ax.set_ylabel("Mbps", color=T["fg_dim"], fontsize=8)
        ax.set_title("Speed Test Results", color=T["fg"], fontsize=9)
        fig.tight_layout()
        canvas = FigureCanvasTkAgg(fig, master=self._speed_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self._speed_canvas = canvas
        plt.close(fig)


    # ── EXPORT ────────────────────────────────────────────────────────────────
    def _export_csv(self):
        df = self._build_dataframe()
        if df.empty: messagebox.showinfo("Export","No results to export."); return
        path = filedialog.asksaveasfilename(
            defaultextension=".csv", filetypes=[("CSV","*.csv"),("All","*.*")],
            initialfile=f"mullvad_{self.current_region.lower().replace(' ','_')}_{datetime.now():%Y%m%d_%H%M}.csv")
        if path:
            df.to_csv(path, index=False)
            messagebox.showinfo("Export",f"Saved to {path}")

    def _export_json(self):
        df = self._build_dataframe()
        if df.empty: messagebox.showinfo("Export","No results to export."); return
        path = filedialog.asksaveasfilename(
            defaultextension=".json", filetypes=[("JSON","*.json"),("All","*.*")],
            initialfile=f"mullvad_{self.current_region.lower().replace(' ','_')}_{datetime.now():%Y%m%d_%H%M}.json")
        if path:
            df.to_json(path, orient="records", indent=2)
            messagebox.showinfo("Export",f"Saved to {path}")

    # ── COPY BEST ─────────────────────────────────────────────────────────────
    def _copy_best(self):
        reach = {s:d for s,d in self.results.items() if d}
        if not reach: messagebox.showinfo("Copy","Run a ping test first."); return
        best = min(reach, key=lambda s: reach[s][0])
        # Strip .mullvad.net for cleaner clipboard value
        short = best.replace(".mullvad.net","")
        self.clipboard_clear(); self.clipboard_append(short)
        messagebox.showinfo("Copied",f"Copied to clipboard:\n{short}\n({reach[best][0]:.1f}ms avg)")

    # ── AUTO-CONNECT ──────────────────────────────────────────────────────────
    def _auto_connect(self):
        reach = {s:d for s,d in self.results.items() if d}
        if not reach:
            messagebox.showinfo("Auto-Connect","Run a ping test first."); return
        best  = min(reach, key=lambda s: reach[s][0])
        # Mullvad CLI: mullvad relay set location <country> <city> <hostname>
        # hostname is e.g. "us-lax-wg-001"
        hostname = best.replace(".mullvad.net","")
        parts = hostname.split("-")  # ['us','lax','wg','001']
        country = parts[0] if len(parts) >= 1 else "us"
        city    = parts[1] if len(parts) >= 2 else "lax"
        cmd = ["mullvad","relay","set","hostname", hostname]
        try:
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                messagebox.showinfo("Auto-Connect",
                                    f"Connected to {hostname}\n({reach[best][0]:.1f}ms avg)")
            else:
                raise RuntimeError(result.stderr or "Non-zero exit")
        except FileNotFoundError:
            messagebox.showerror("Auto-Connect",
                                 "Mullvad CLI not found.\n"
                                 "Install from: https://mullvad.net/download\n\n"
                                 f"Best server was: {hostname}")
        except Exception as e:
            messagebox.showerror("Auto-Connect", f"Failed: {e}\n\nBest server: {hostname}")

    # ── SCHEDULE ──────────────────────────────────────────────────────────────
    def _toggle_schedule(self):
        if self.schedule_active.get():
            self._schedule_next()
        else:
            if self.schedule_job:
                self.after_cancel(self.schedule_job)
                self.schedule_job = None
            self.status_var.set("Auto-ping disabled.")

    def _schedule_next(self):
        if not self.schedule_active.get(): return
        mins = max(0.5, self.schedule_mins.get())
        ms   = int(mins * 60 * 1000)
        self.status_var.set(f"Next auto-ping in {mins:.1f} min.")
        self.schedule_job = self.after(ms, self._scheduled_run)

    def _scheduled_run(self):
        if not self.running:
            self.start_pinging()
        self._schedule_next()

    # ── TRAY ──────────────────────────────────────────────────────────────────
    def _minimize_to_tray(self):
        if not TRAY_AVAILABLE:
            messagebox.showinfo("Tray",
                                "pystray and Pillow are required for tray mode.\n"
                                "pip install pystray pillow")
            return
        self.withdraw()
        icon_img = make_tray_icon(T["accent"])

        def on_show(icon, item):
            icon.stop(); self._tray = None
            self.after(0, self.deiconify)

        def on_run(icon, item):
            self.after(0, self.start_pinging)

        def on_quit(icon, item):
            icon.stop(); self.after(0, self.destroy)

        menu = pystray.Menu(
            pystray.MenuItem("Show Window", on_show, default=True),
            pystray.MenuItem("Run Ping Now", on_run),
            pystray.MenuItem("Quit", on_quit),
        )
        self._tray = pystray.Icon("MullvadPing", icon_img,
                                  "Mullvad Ping", menu)
        threading.Thread(target=self._tray.run, daemon=True).start()

    # ── CLOSE ─────────────────────────────────────────────────────────────────
    def _on_close(self):
        if self._tray:
            self._tray.stop()
        self.destroy()


if __name__ == "__main__":
    app = MullvadApp()
    app.mainloop()

    # ── EXPORT ────────────────────────────────────────────────────────────────
    def _export_csv(self):
        df = self._build_dataframe()
        if df.empty: messagebox.showinfo("Export","No data to export."); return
        path = filedialog.asksaveasfilename(
            defaultextension=".csv", filetypes=[("CSV","*.csv"),("All","*.*")],
            initialfile=f"mullvad_{self.current_region.lower().replace(' ','_')}_"
                        f"{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv")
        if not path: return
        df.to_csv(path, index=False)
        messagebox.showinfo("Exported", f"Saved to:\n{path}")

    def _export_json(self):
        df = self._build_dataframe()
        if df.empty: messagebox.showinfo("Export","No data to export."); return
        path = filedialog.asksaveasfilename(
            defaultextension=".json", filetypes=[("JSON","*.json"),("All","*.*")],
            initialfile=f"mullvad_{self.current_region.lower().replace(' ','_')}_"
                        f"{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
        if not path: return
        out = {"region":self.current_region,
               "timestamp":datetime.now().isoformat(),
               "ping_count":int(self.ping_count.get()),
               "results":df.to_dict(orient="records")}
        with open(path,"w") as f:
            json.dump(out, f, indent=2)
        messagebox.showinfo("Exported", f"Saved to:\n{path}")

    # ── COPY BEST ─────────────────────────────────────────────────────────────
    def _copy_best(self):
        reach = {s:d for s,d in self.results.items() if d}
        if not reach: messagebox.showinfo("No data","Run a ping test first."); return
        best = min(reach, key=lambda s: reach[s][0])
        self.clipboard_clear(); self.clipboard_append(best)
        messagebox.showinfo("Copied",
                            f"Copied to clipboard:\n{best}\n"
                            f"(Avg: {reach[best][0]:.1f}ms)")

    # ── AUTO-CONNECT ──────────────────────────────────────────────────────────
    def _auto_connect(self):
        reach = {s:d for s,d in self.results.items() if d}
        if not reach: messagebox.showinfo("No data","Run a ping test first."); return
        best = min(reach, key=lambda s: reach[s][0])
        host = best.replace(".mullvad.net","")
        try:
            result = subprocess.run(["mullvad","relay","set","hostname",host],
                                    capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                messagebox.showinfo("Connected",
                                    f"Mullvad connected to:\n{host}\n"
                                    f"(Avg: {reach[best][0]:.1f}ms)")
            else:
                raise RuntimeError(result.stderr.strip() or "Unknown error")
        except FileNotFoundError:
            messagebox.showerror("Mullvad CLI not found",
                                 "The 'mullvad' command was not found.\n"
                                 "Install the Mullvad CLI app and make sure it's in PATH.")
        except Exception as e:
            messagebox.showerror("Error", str(e))

    # ── COMPARE A / B ─────────────────────────────────────────────────────────
    def _save_run_a(self):
        if not self.results:
            messagebox.showinfo("No data","Run a ping test first."); return
        self.compare_a = dict(self.results)
        ts = datetime.now().strftime("%H:%M:%S")
        self._cmp_a_lbl.config(text=f"Run A: {ts} — {len(self.compare_a)} servers",
                                fg=T["green"])

    def _save_run_b(self):
        if not self.results:
            messagebox.showinfo("No data","Run a ping test first."); return
        self.compare_b = dict(self.results)
        ts = datetime.now().strftime("%H:%M:%S")
        self._cmp_b_lbl.config(text=f"Run B: {ts} — {len(self.compare_b)} servers",
                                fg=T["accent"])

    def _show_compare(self):
        if not self.compare_a or not self.compare_b:
            messagebox.showinfo("Compare","Save Run A and Run B first."); return
        if self._cmp_ph.winfo_exists():
            self._cmp_ph.pack_forget()
        if self._cmp_tree:
            self._cmp_tree.destroy()
        cols   = ("Server","A avg","B avg","Delta","A jitter","B jitter")
        widths = [220, 80, 80, 90, 90, 90]
        self._cmp_tree = ttk.Treeview(self._cmp_frame, columns=cols,
                                      show="headings")
        for col, w in zip(cols, widths):
            self._cmp_tree.heading(col, text=col)
            self._cmp_tree.column(col, width=w, anchor="center")
        all_servers = sorted(
            set(self.compare_a.keys()) | set(self.compare_b.keys()))
        for sv in all_servers:
            da = self.compare_a.get(sv)
            db = self.compare_b.get(sv)
            short = sv.replace(".mullvad.net","")
            a_avg = f"{da[0]:.1f}" if da else "--"
            b_avg = f"{db[0]:.1f}" if db else "--"
            a_jit = f"{da[4]:.1f}" if da else "--"
            b_jit = f"{db[4]:.1f}" if db else "--"
            delta = "--"
            tag   = "dead"
            if da and db:
                d = db[0] - da[0]
                delta = f"{d:+.1f}ms"
                tag   = "good" if d < -5 else ("bad" if d > 5 else "ok")
            self._cmp_tree.insert("", tk.END,
                                  values=(short,a_avg,b_avg,delta,a_jit,b_jit),
                                  tags=(tag,))
        self._cmp_tree.pack(fill=tk.BOTH, expand=True, padx=14, pady=(4,12))

    # ── SCHEDULE ──────────────────────────────────────────────────────────────
    def _toggle_schedule(self):
        if self.schedule_active.get():
            self._run_scheduled()
        else:
            if self.schedule_job:
                self.after_cancel(self.schedule_job)
                self.schedule_job = None

    def _run_scheduled(self):
        if not self.schedule_active.get(): return
        self.start_pinging()
        mins = max(0.5, self.schedule_mins.get())
        ms   = int(mins * 60 * 1000)
        self.schedule_job = self.after(ms, self._run_scheduled)

    # ── TRAY ──────────────────────────────────────────────────────────────────
    def _minimize_to_tray(self):
        if not TRAY_AVAILABLE:
            messagebox.showinfo("Tray",
                "System tray requires pystray and Pillow.\n"
                "pip install pystray Pillow"); return
        self.withdraw()
        reach = {s:d for s,d in self.results.items() if d}
        if reach:
            best_avg = min(d[0] for d in reach.values())
            col = ("#7ee787" if best_avg<30 else
                   "#00e5ff" if best_avg<70 else
                   "#e3b341" if best_avg<120 else "#f85149")
        else:
            col = "#8b949e"
        icon_img = make_tray_icon(col)

        def show(_ico, _item):
            self.after(0, self.deiconify)
            if self._tray: self._tray.stop()
            self._tray = None

        def quit_app(_ico, _item):
            if self._tray: self._tray.stop()
            self.after(0, self.destroy)

        menu = pystray.Menu(
            pystray.MenuItem("Show", show, default=True),
            pystray.MenuItem("Quit", quit_app))
        self._tray = pystray.Icon("MullvadPing", icon_img,
                                   "Mullvad Ping Monitor", menu)
        threading.Thread(target=self._tray.run, daemon=True).start()

    # ── CLOSE ─────────────────────────────────────────────────────────────────
    def _on_close(self):
        if self._tray: self._tray.stop()
        if self.schedule_job: self.after_cancel(self.schedule_job)
        plt.close("all")
        self.destroy()

# ── ENTRY POINT ───────────────────────────────────────────────────────────────
if __name__ == "__main__":
    app = MullvadApp()
    app.mainloop()
