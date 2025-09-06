from flask import Flask, render_template, request, jsonify, send_from_directory, Response
import re
import math
from math import log
import heapq
from typing import List, Tuple, Dict, Set, Optional
from collections import defaultdict, deque
from statistics import median
import string
import xml.etree.ElementTree as ET
import os
import time
import threading
import typing as t


app = Flask(__name__)

# Title Challenge
@app.route("/trivia", methods=["GET"])
def trivia():
    return {
        "answers": [
            3,
            1,
            2,
            2,
            3,
            4,
            4,
            5,
            4
        ]
    }

# Ticketing Agent
def calculate_points(customer, concert, priority):
    points = 0

    # Factor 1: VIP
    if customer.get("vip_status"):
        points += 100

    # Factor 2: Credit card
    credit_card = customer.get("credit_card")
    if credit_card in priority and priority[credit_card] == concert["name"]:
        points += 50

    # Factor 3: Latency (distance)
    cx, cy = customer["location"]
    bx, by = concert["booking_center_location"]
    distance = math.sqrt((cx - bx) ** 2 + (cy - by) ** 2)
    latency_points = max(0, 30 - distance)  # simple linear scale
    points += latency_points

    return points

@app.route("/ticketing-agent", methods=["POST", "OPTIONS"])
def ticketing_agent():
    if request.method == "OPTIONS":
        return ("", 204)
    
    data = request.get_json(silent=True)
    if data is None:
        return jsonify(error="Expected JSON body with Content-Type: application/json"), 400

    customers = data.get("customers", [])
    concerts = data.get("concerts", [])
    priority = data.get("priority", {})

    result = {}

    for customer in customers:
        best_concert = None
        best_score = -1
        for concert in concerts:
            score = calculate_points(customer, concert, priority)
            if score > best_score:
                best_score = score
                best_concert = concert["name"]

        result[customer["name"]] = best_concert

    return jsonify(result)

# Princess Diaries
def dijkstra(graph: Dict[int, List[Tuple[int, int]]], start: int) -> Dict[int, int]:
    """
    Find shortest paths from start to all other nodes using Dijkstra's algorithm.
    """
    distances = {start: 0}
    pq = [(0, start)]
    visited = set()
    
    while pq:
        curr_dist, curr_node = heapq.heappop(pq)
        
        if curr_node in visited:
            continue
        visited.add(curr_node)
        
        if curr_node in graph:
            for neighbor, weight in graph[curr_node]:
                if neighbor not in visited:
                    new_dist = curr_dist + weight
                    if neighbor not in distances or new_dist < distances[neighbor]:
                        distances[neighbor] = new_dist
                        heapq.heappush(pq, (new_dist, neighbor))
    
    return distances

def build_graph(subway: List[Dict]) -> Dict[int, List[Tuple[int, int]]]:
    """
    Build adjacency list representation of the subway graph.
    """
    graph = {}
    for route in subway:
        u, v = route['connection']
        fee = route['fee']
        
        if u not in graph:
            graph[u] = []
        if v not in graph:
            graph[v] = []
        
        graph[u].append((v, fee))
        graph[v].append((u, fee))
    
    return graph

def compute_all_distances(graph: Dict[int, List[Tuple[int, int]]], stations: Set[int]) -> Dict[Tuple[int, int], int]:
    """
    Compute shortest distances between all pairs of stations we care about.
    """
    distances = {}
    for station in stations:
        dist_from_station = dijkstra(graph, station)
        for target in stations:
            if target in dist_from_station:
                distances[(station, target)] = dist_from_station[target]
    
    return distances

def find_max_score_schedule(tasks: List[Dict], subway: List[Dict], starting_station: int) -> Dict:
    """
    Find the schedule with maximum score and minimum transportation cost.
    Uses weighted interval scheduling DP for max score, then backtracks to
    consider all optimal-score schedules and selects the one with min fee.
    """
    if not tasks:
        return {"max_score": 0, "min_fee": 0, "schedule": []}

    # --- Step 1: Build graph + all-pairs shortest paths ---
    graph = build_graph(subway)
    stations = {starting_station} | {t["station"] for t in tasks}
    distances = compute_all_distances(graph, stations)

    # --- Step 2: Sort tasks by end time ---
    tasks = sorted(tasks, key=lambda t: t["end"])
    n = len(tasks)
    ends = [t["end"] for t in tasks]

    # --- Step 3: Precompute p[i] = last non-overlapping task ---
    import bisect
    p = [bisect.bisect_right(ends, tasks[i]["start"]) - 1 for i in range(n)]

    # --- Step 4: Weighted interval scheduling DP ---
    dp = [0] * (n + 1)
    for i in range(1, n + 1):
        without = dp[i - 1]
        with_curr = tasks[i - 1]["score"] + dp[p[i - 1] + 1]
        dp[i] = max(without, with_curr)
    max_score = dp[n]

    # --- Step 5: Backtrack to collect all optimal-score schedules ---
    schedules = []

    def backtrack(i, current):
        if i == 0:
            schedules.append(list(reversed(current)))
            return
        # Option 1: skip task i-1
        if dp[i] == dp[i - 1]:
            backtrack(i - 1, current)
        # Option 2: take task i-1
        if tasks[i - 1]["score"] + dp[p[i - 1] + 1] == dp[i]:
            backtrack(p[i - 1] + 1, current + [i - 1])

    backtrack(n, [])

    # --- Step 6: Among schedules with max_score, compute min fee ---
    best_fee = float("inf")
    best_schedule = []

    for sched in schedules:
        fee = 0
        if sched:
            # from start to first
            fee += distances[(starting_station, tasks[sched[0]]["station"])]
            # between consecutive
            for a, b in zip(sched, sched[1:]):
                fee += distances[(tasks[a]["station"], tasks[b]["station"])]
            # last back to start
            fee += distances[(tasks[sched[-1]]["station"], starting_station)]
        if fee < best_fee:
            best_fee = fee
            best_schedule = sched

    # --- Step 7: Format output ---
    schedule_names = [tasks[i]["name"] for i in best_schedule]

    return {
        "max_score": max_score,
        "min_fee": best_fee if best_schedule else 0,
        "schedule": schedule_names,
    }


@app.route("/princess-diaries", methods=["POST"])
def princess_diaries():
    """
    Handle the princess diaries challenge endpoint.
    """
    try:
        data = request.json
        
        tasks = data['tasks']
        subway = data['subway']
        starting_station = data['starting_station']
        
        result = find_max_score_schedule(tasks, subway, starting_station)
        
        return jsonify(result)
    
    except Exception as e:
        return jsonify({'error': str(e)}), 500


# Operation Safeguard
# ----------------------------
# Challenge 1: Transform funcs
# ----------------------------
VOWELS = set("aeiouAEIOU")

def mirror_words(x: str) -> str:
    return " ".join(word[::-1] for word in x.split(" "))

def encode_mirror_alphabet(x: str) -> str:
    # map a<->z, b<->y, ... preserve case
    def mirror_char(c):
        if c.isalpha():
            alpha = string.ascii_lowercase
            idx = alpha.index(c.lower())
            mirrored = alpha[-1 - idx]
            return mirrored.upper() if c.isupper() else mirrored
        return c
    return "".join(mirror_char(c) for c in x)

def toggle_case(x: str) -> str:
    return "".join(c.lower() if c.isupper() else c.upper() for c in x)

def swap_pairs(x: str) -> str:
    def swap_word(w):
        lst = list(w)
        for i in range(0, len(lst) - 1, 2):
            lst[i], lst[i+1] = lst[i+1], lst[i]
        return "".join(lst)
    return " ".join(swap_word(w) for w in x.split(" "))

def encode_index_parity(x: str) -> str:
    # for each word: even indices then odd indices
    def enc_word(w):
        evens = [w[i] for i in range(0, len(w), 2)]
        odds = [w[i] for i in range(1, len(w), 2)]
        return "".join(evens + odds)
    return " ".join(enc_word(w) for w in x.split(" "))

def double_consonants(x: str) -> str:
    def proc(w):
        out = []
        for c in w:
            out.append(c)
            if c.isalpha() and c not in VOWELS:
                out.append(c)
        return "".join(out)
    return " ".join(proc(w) for w in x.split(" "))

# Inverses
# Many of these are self-inverse (apply same function again) except double_consonants and encode_index_parity

def inv_mirror_words(x: str) -> str:
    return mirror_words(x)

def inv_encode_mirror_alphabet(x: str) -> str:
    return encode_mirror_alphabet(x)

def inv_toggle_case(x: str) -> str:
    return toggle_case(x)

def inv_swap_pairs(x: str) -> str:
    return swap_pairs(x)

def inv_encode_index_parity(x: str) -> str:
    # Given transformed word: first part = evens, second = odds (evens_len = ceil(n/2))
    def dec_word(w):
        n = len(w)
        evens_len = (n + 1) // 2
        evens = list(w[:evens_len])
        odds = list(w[evens_len:])
        res = []
        e_i = 0
        o_i = 0
        for i in range(n):
            if i % 2 == 0:
                res.append(evens[e_i]); e_i += 1
            else:
                res.append(odds[o_i]); o_i += 1
        return "".join(res)
    return " ".join(dec_word(w) for w in x.split(" "))

def inv_double_consonants(x: str) -> str:
    # compress doubled consonants back to single (assumes original didn't have repeated consonants)
    def dec_word(w):
        out = []
        i = 0
        while i < len(w):
            c = w[i]
            out.append(c)
            if c.isalpha() and c not in VOWELS:
                # if next char same, skip it
                if i + 1 < len(w) and w[i+1] == c:
                    i += 2
                    continue
            i += 1
        return "".join(out)
    return " ".join(dec_word(w) for w in x.split(" "))

INVERSE_MAP = {
    "mirror_words": inv_mirror_words,
    "encode_mirror_alphabet": inv_encode_mirror_alphabet,
    "toggle_case": inv_toggle_case,
    "swap_pairs": inv_swap_pairs,
    "encode_index_parity": inv_encode_index_parity,
    "double_consonants": inv_double_consonants,
}

def parse_transformation_list(s: str):
    # input like: "[encode_mirror_alphabet(x), double_consonants(x), mirror_words(x), swap_pairs(x), encode_index_parity(x)]"
    names = re.findall(r'([a-zA-Z_]+)\s*\(x\)', s)
    return names

def reverse_transform(trans_list, transformed_word):
    # Apply inverses in reverse order
    value = transformed_word
    for func_name in reversed(trans_list):
        if func_name not in INVERSE_MAP:
            raise ValueError(f"No inverse implemented for {func_name}")
        value = INVERSE_MAP[func_name](value)
    return value

# ----------------------------
# Challenge 2: Coordinates
# ----------------------------
def parse_coordinate_pair(pair):
    # pair like ["<LAT>", "<LONG>"] where strings may have commas
    try:
        lat = float(str(pair[0]).strip())
        lon = float(str(pair[1]).strip())
        return (lat, lon)
    except Exception:
        # try to extract floats from strings
        nums = re.findall(r'[-+]?[0-9]*\.?[0-9]+', " ".join(pair))
        if len(nums) >= 2:
            return (float(nums[0]), float(nums[1]))
        raise

def mad_outlier_filter(points, threshold=3.5):
    # points: list of (x,y). compute distances to centroid and remove outliers via MAD
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    cx = median(xs)
    cy = median(ys)
    dists = [math.hypot(p[0]-cx, p[1]-cy) for p in points]
    med = median(dists)
    abs_devs = [abs(d - med) for d in dists]
    mad = median(abs_devs) if abs_devs else 0.0
    if mad == 0:
        # fallback simple filter: keep all
        return points
    filtered = []
    for p, d in zip(points, dists):
        if abs(d - med) / mad <= threshold:
            filtered.append(p)
    return filtered

# convex hull (Monotone chain)
def convex_hull(points):
    pts = sorted(set(points))
    if len(pts) <= 1:
        return pts
    def cross(o, a, b):
        return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lower = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    hull = lower[:-1] + upper[:-1]
    return hull

def analyze_coordinates(coord_list):
    # 1) parse floats and remove outliers (MAD)
    pts = []
    for pair in coord_list:
        try:
            pts.append(parse_coordinate_pair(pair))
        except Exception:
            continue
    if not pts:
        return None
    filtered = mad_outlier_filter(pts)
    if len(filtered) < 3:
        return str(len(filtered))

    # 2) normalize to 28x28 grid
    xs = [p[0] for p in filtered]
    ys = [p[1] for p in filtered]
    minx, maxx = min(xs), max(xs)
    miny, maxy = min(ys), max(ys)
    # avoid degenerate ranges
    dx = maxx - minx or 1.0
    dy = maxy - miny or 1.0

    GRID = 28
    grid = [[0]*GRID for _ in range(GRID)]
    for (x,y) in filtered:
        gx = int(((x - minx) / dx) * (GRID-1))
        gy = int(((y - miny) / dy) * (GRID-1))
        # flip y so origin is at top-left for consistency
        gy = GRID - 1 - gy
        grid[gy][gx] = 1

    # 3) simple dilation to thicken points
    def dilate(g):
        new = [row[:] for row in g]
        for r in range(GRID):
            for c in range(GRID):
                if g[r][c]:
                    for dr in (-1,0,1):
                        for dc in (-1,0,1):
                            rr, cc = r+dr, c+dc
                            if 0 <= rr < GRID and 0 <= cc < GRID:
                                new[rr][cc] = 1
        return new
    grid = dilate(grid)
    grid = dilate(grid)

    # 4) digit templates (simple stylized 28x28 binary masks).
    # These are minimal, hand-coded shapes — not perfect fonts, but adequate for puzzle digits.
    # To keep answer concise, create templates programmatically by drawing rough strokes.
    def make_empty():
        return [[0]*GRID for _ in range(GRID)]
    templates = {}
    # 0: ring
    t = make_empty()
    for r in range(6,22):
        for c in range(8,20):
            # approximate ellipse: border
            if (r-14)**2/64 + (c-14)**2/36 >= 1 and (r-14)**2/64 + (c-14)**2/36 <= 1.8:
                t[r][c]=1
    templates['0']=t
    # 1: vertical
    t = make_empty()
    for r in range(6,22):
        for c in range(12,16):
            t[r][c]=1
    templates['1']=t
    # 2: top, diag, bottom
    t = make_empty()
    for c in range(6,22):
        t[6][c]=1
        t[14][c]=1
        t[22][c]=1
    for i in range(0,9):
        t[7+i][16+i]=1
    for i in range(0,9):
        t[15+i][8+i]=1
    templates['2']=t
    # 3: two bumps
    t = make_empty()
    for c in range(8,20):
        t[6][c]=1; t[14][c]=1; t[22][c]=1
    for i in range(0,9):
        t[6+i][20 - (i//3)] = 1
        t[14+i][20 - (i//3)] = 1
    templates['3']=t
    # 4: left vertical top, right vertical full
    t = make_empty()
    for r in range(6,15):
        t[r][8]=1
    for r in range(6,23):
        t[r][18]=1
    for c in range(8,19):
        t[14][c]=1
    templates['4']=t
    # 5: mirror of 2
    t = make_empty()
    for c in range(8,20):
        t[6][c]=1; t[14][c]=1; t[22][c]=1
    for i in range(0,9):
        t[7+i][8+i]=1
    for i in range(0,7):
        t[15+i][16-i]=1
    templates['5']=t
    # 6: ring with left vertical
    t = make_empty()
    for r in range(6,22):
        for c in range(8,20):
            if (r-14)**2/64 + (c-14)**2/36 >= 1 and (r-14)**2/64 + (c-14)**2/36 <= 1.8:
                t[r][c]=1
    for r in range(11,23):
        t[r][8]=1
    t[14][12]=1
    templates['6']=t
    # 7: top bar and diagonal down right
    t = make_empty()
    for c in range(8,22):
        t[6][c]=1
    for i in range(0,16):
        r = 7 + i
        c = 20 - (i//1.2)
        if 0<=r<GRID and 0<=c<GRID:
            t[int(r)][int(c)]=1
    templates['7']=t
    # 8: two rings
    t = make_empty()
    for center in (10,18):
        for r in range(6,22):
            for c in range(8,20):
                if (r-center)**2/36 + (c-14)**2/36 >= 0.8 and (r-center)**2/36 + (c-14)**2/36 <= 1.6:
                    t[r][c]=1
    templates['8']=t
    # 9: ring with right vertical
    t = make_empty()
    for r in range(6,22):
        for c in range(8,20):
            if (r-12)**2/64 + (c-14)**2/36 >= 1 and (r-12)**2/64 + (c-14)**2/36 <= 1.8:
                t[r][c]=1
    for r in range(6,13):
        t[r][20]=1
    templates['9']=t

    # 5) compare: compute Jaccard similarity
    def jaccard(a, b):
        inter = 0
        uni = 0
        for r in range(GRID):
            for c in range(GRID):
                if a[r][c] or b[r][c]:
                    uni += 1
                    if a[r][c] and b[r][c]:
                        inter += 1
        return inter / uni if uni else 0.0

    best_digit = None
    best_score = 0.0
    for d, t in templates.items():
        score = jaccard(grid, t)
        if score > best_score:
            best_score = score
            best_digit = d

    # threshold: require decent overlap, otherwise fallback to hull vertex count
    if best_score >= 0.25:
        return str(int(best_digit))
    # fallback: hull vertex count
    hull = convex_hull(filtered)
    return str(len(hull))

# ----------------------------
# Challenge 3: Log parsing & ciphers
# ----------------------------
def parse_log_entry(log_str):
    # Split by '|' then each field 'KEY: VALUE'
    fields = {}
    parts = [p.strip() for p in log_str.split("|")]
    for p in parts:
        if ":" in p:
            k, v = p.split(":", 1)
            fields[k.strip().upper()] = v.strip()
    return fields

# Rail fence decrypt (3 rails)
def rail_fence_decrypt(ciphertext, rails=3):
    if rails <= 1:
        return ciphertext
    n = len(ciphertext)
    # determine pattern of positions
    rail_lens = [0]*rails
    rail = 0
    step = 1
    pattern = []
    for i in range(n):
        pattern.append(rail)
        rail_lens[rail] += 1
        rail += step
        if rail == 0 or rail == rails-1:
            step *= -1
    # now slice ciphertext into rails
    idx = 0
    rails_chars = []
    for rlen in rail_lens:
        rails_chars.append(list(ciphertext[idx:idx+rlen]))
        idx += rlen
    # reconstruct
    res = []
    rail_ptrs = [0]*rails
    for p in pattern:
        res.append(rails_chars[p][rail_ptrs[p]])
        rail_ptrs[p] += 1
    return "".join(res)

# Keyword substitution cipher using keyword "SHADOW"
def build_keyword_alphabet(keyword="SHADOW"):
    keyword = "".join(ch.upper() for ch in keyword if ch.isalpha())
    seen = []
    for ch in keyword:
        if ch not in seen:
            seen.append(ch)
    for ch in string.ascii_uppercase:
        if ch not in seen:
            seen.append(ch)
    # return mapping: plaintext A..Z -> cipher alphabet
    plain = list(string.ascii_uppercase)
    cipher = seen
    return dict(zip(plain, cipher)), dict(zip(cipher, plain))

def keyword_decrypt(ciphertext, keyword="SHADOW"):
    _, inv_map = build_keyword_alphabet(keyword)
    out = []
    for ch in ciphertext:
        if ch.upper() in inv_map:
            plain = inv_map[ch.upper()]
            out.append(plain if ch.isupper() else plain.lower())
        else:
            out.append(ch)
    return "".join(out)

# Polybius square decrypt (I/J combined) - expects ciphertext letters or digit pairs
def polybius_decrypt(ciphertext):
    # If ciphertext contains only digits, treat as pairs, else if letters treat as letters encoded with grid coordinates?
    # Standard Polybius uses coordinates 1-5 for rows/cols:
    square = [
        ['A','B','C','D','E'],
        ['F','G','H','I','K'],
        ['L','M','N','O','P'],
        ['Q','R','S','T','U'],
        ['V','W','X','Y','Z']
    ]
    txt = re.sub(r'\s+', '', ciphertext)
    digits = re.findall(r'\d+', txt)
    # If the string is plain digits like '112131', parse pairs
    if txt.isdigit() and len(txt) % 2 == 0:
        pairs = [txt[i:i+2] for i in range(0, len(txt), 2)]
        out = []
        for pair in pairs:
            r = int(pair[0]) - 1
            c = int(pair[1]) - 1
            if 0 <= r < 5 and 0 <= c < 5:
                out.append(square[r][c])
            else:
                out.append('?')
        return "".join(out)
    # Else if ciphertext are pairs of letters (like '11' encoded letters) we attempt fallback:
    # Attempt mapping letters -> coordinates by A=11,B=12... with I/J combined mapping is ambiguous,
    # fallback: try to map letters by position of letter in square
    out = []
    for ch in ciphertext:
        if not ch.isalpha():
            out.append(ch)
            continue
        # find ch in square (I/J combined -> treat J as I)
        target = ch.upper()
        if target == 'J': target = 'I'
        found = False
        for r in range(5):
            for c in range(5):
                if square[r][c] == target:
                    out.append(square[r][c])
                    found = True
                    break
            if found: break
        if not found:
            out.append('?')
    return "".join(out)

# ROT13
def rot13(s):
    trans = str.maketrans(
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
        "NOPQRSTUVWXYZABCDEFGHIJKLMnopqrstuvwxyzabcdefghijklm")
    return s.translate(trans)

def decrypt_payload(cipher_type, payload):
    # flexible wrapper for cipher types and synonyms
    ctype = (cipher_type or "").strip().upper()
    if ctype in ("RAILFENCE", "RAIL FENCE", "RAIL-FENCE"):
        return rail_fence_decrypt(payload, rails=3)
    if ctype in ("KEYWORD", "KEYWORD_SUB", "KEYWORD_CIPHER"):
        # Try both mapping directions: cipher->plain and plain->cipher; choose the one producing readable text
        dec1 = keyword_decrypt(payload, keyword="SHADOW")  # map cipher->plain using our inv_map
        # also attempt reverse mapping if needed (apply substitution in other direction)
        # build forward mapping
        forward_map, inv_map = build_keyword_alphabet("SHADOW")
        # apply forward map as if payload were plaintext -> cipher; to reverse, we invert map
        # But we already have 'keyword_decrypt' as cipher->plain. If result looks like english, return.
        # Heuristic: contains vowels and letters
        if sum(ch.lower() in 'aeiou' for ch in dec1) >= max(1, len(dec1)//10):
            return dec1
        # else try brute-force reverse mapping (treat payload as if mapping was opposite)
        reverse_map = {v:k for k,v in build_keyword_alphabet("SHADOW")[0].items()}
        out=[]
        for ch in payload:
            if ch.upper() in reverse_map:
                p = reverse_map[ch.upper()]
                out.append(p if ch.isupper() else p.lower())
            else:
                out.append(ch)
        return "".join(out)

    if ctype in ("POLYBIUS", "POLYBIUS_SQUARE"):
        return polybius_decrypt(payload)
    if ctype in ("ROTATION_CIPHER","ROTATION","ROT13","ROT"):
        return rot13(payload)
    # fallback attempts:
    res = rot13(payload)
    if any(ch.isalpha() for ch in res):
        return res
    return rail_fence_decrypt(payload, rails=3)

# ----------------------------
# Challenge 4: Final decryption helper (heuristic)
# ----------------------------
def vigenere_decrypt(ciphertext, key):
    # key repeated. Only letters handled
    out = []
    key_up = [k.upper() for k in key if k.isalpha()]
    if not key_up:
        return ciphertext
    ki = 0
    for ch in ciphertext:
        if ch.isalpha():
            a = ord('A') if ch.isupper() else ord('a')
            kch = key_up[ki % len(key_up)]
            shift = ord(kch) - ord('A')
            dec_ord = (ord(ch.upper()) - ord('A') - shift) % 26 + ord('A')
            out_ch = chr(dec_ord)
            out.append(out_ch if ch.isupper() else out_ch.lower())
            ki += 1
        else:
            out.append(ch)
    return "".join(out)

def caesar_decrypt(ciphertext, shift):
    out = []
    for ch in ciphertext:
        if ch.isalpha():
            base = ord('A') if ch.isupper() else ord('a')
            out.append(chr((ord(ch) - base - shift) % 26 + base))
        else:
            out.append(ch)
    return "".join(out)

# ----------------------------
# Flask endpoint
# ----------------------------
@app.route("/operation-safeguard", methods=["POST"])
def operation_safeguard():
    data = request.get_json(force=True)
    result = {}

    # --- Challenge 1 ---
    try:
        c1 = data.get("challenge_one", {})
        trans_str = c1.get("transformations", "")
        transformed_word = c1.get("transformed_encrypted_word", "")
        trans_list = parse_transformation_list(trans_str)
        recovered = reverse_transform(trans_list, transformed_word)
        result["challenge_one"] = str(recovered)
    except Exception as e:
        result["challenge_one"] = f"ERROR: {str(e)}"

    # --- Challenge 2 ---
    try:
        c2 = data.get("challenge_two", [])
        numeric_param = analyze_coordinates(c2)
        result["challenge_two"] = str(numeric_param)
    except Exception as e:
        result["challenge_two"] = f"ERROR: {str(e)}"

    # --- Challenge 3 ---
    try:
        log_str = data.get("challenge_three", "")
        if not log_str:
            result["challenge_three"] = "NO_LOG_PROVIDED"
        else:
            fields = parse_log_entry(log_str)
            cipher_type = fields.get("CIPHER_TYPE") or fields.get("CIPHER")
            encrypted_payload = fields.get("ENCRYPTED_PAYLOAD") or fields.get("PAYLOAD") or ""
            if not cipher_type:
                decrypted_guess = rot13(encrypted_payload)
                result["challenge_three"] = str(decrypted_guess)
            else:
                decrypted = decrypt_payload(cipher_type, encrypted_payload)
                result["challenge_three"] = str(decrypted)
    except Exception as e:
        result["challenge_three"] = f"ERROR: {str(e)}"

    # --- Challenge 4 ---
    try:
        final_ct = data.get("final_ciphertext", None)
        final_method = data.get("final_method", "").upper() if data.get("final_method") else ""
        c1_val = result["challenge_one"]
        c2_val = result["challenge_two"]

        if final_ct:
            final_plain = None
            if final_method == "VIGENERE":
                final_plain = vigenere_decrypt(final_ct, c1_val)
            elif final_method == "CAESAR":
                try:
                    shift = int(c2_val)
                    final_plain = caesar_decrypt(final_ct, shift)
                except Exception:
                    final_plain = None
            if final_plain is None:
                # fallback attempts
                try:
                    final_plain = vigenere_decrypt(final_ct, c1_val)
                except Exception:
                    pass
            if final_plain is None and c2_val.isdigit():
                final_plain = caesar_decrypt(final_ct, int(c2_val))
            if final_plain is None:
                final_plain = rot13(final_ct)
            result["challenge_four"] = str(final_plain)
        else:
            result["challenge_four"] = (
                f"No final_ciphertext provided. "
                f"Recovered key: {c1_val}, "
                f"numeric param: {c2_val}, "
                f"payload: {result['challenge_three']}"
            )
    except Exception as e:
        result["challenge_four"] = f"ERROR: {str(e)}"

    return jsonify(result)


# TRADING FORMULA

SAFE = {
    "max": max, "min": min, "abs": abs,
    "log": math.log, "ln": math.log, "exp": math.exp, "sqrt": math.sqrt,
    "pi": math.pi, "e": math.e,
}

def _balanced_slice(s, start, open_char, close_char):
    """Return (end_index, inner_string) for the balanced region starting at s[start] == open_char."""
    assert s[start] == open_char
    k, depth = start + 1, 0
    while k < len(s):
        c = s[k]
        if c == open_char:
            depth += 1
        elif c == close_char:
            if depth == 0:
                return k, s[start+1:k]
            depth -= 1
        k += 1
    raise ValueError("Unbalanced delimiters")

def _replace_frac(s: str) -> str:
    # Replace every \frac{A}{B} with ((A)/(B))
    out = []
    i = 0
    while i < len(s):
        if s.startswith(r"\frac", i):
            i += len(r"\frac")
            if i >= len(s) or s[i] != "{":  # malformed, just leave
                out.append(r"\frac")
                continue
            r1, A = _balanced_slice(s, i, "{", "}")
            i = r1 + 1
            if i >= len(s) or s[i] != "{":
                out.append(f"({A})")  # best-effort
                continue
            r2, B = _balanced_slice(s, i, "{", "}")
            i = r2 + 1
            out.append(f"(({A})/({B}))")
        else:
            out.append(s[i])
            i += 1
    return "".join(out)

def _replace_exp_e(s: str) -> str:
    # e^{...} -> exp(...); e^x -> exp(x)
    s = re.sub(r"e\^\{([^{}]+)\}", r"exp(\1)", s)
    s = re.sub(r"e\^([A-Za-z0-9_\.]+)", r"exp(\1)", s)
    return s

def _replace_pow_braced(s: str) -> str:
    # x^{y} -> x**(y). Handle any token before ^.
    return re.sub(r"\^\{([^{}]+)\}", r"**(\1)", s)

def _replace_pow_simple(s: str) -> str:
    # a^b -> a**b (for remaining cases, after braced handled)
    return s.replace("^", "**")

def _replace_log_base(s: str) -> str:
    # \log_{b}(x) -> log(x, b)
    i = 0
    out = []
    while i < len(s):
        if s.startswith(r"\log_", i):
            i += len(r"\log_")
            # optional {base} or immediate token
            if i < len(s) and s[i] == "{":
                j, base = _balanced_slice(s, i, "{", "}")
                i = j + 1
            else:
                # read bare token for base
                m = re.match(r"[A-Za-z0-9_\.]+", s[i:])
                base = m.group(0) if m else ""
                i += len(base)
            # next must be (args)
            if i < len(s) and s[i] == "(":
                j, arg = _balanced_slice(s, i, "(", ")")
                i = j + 1
                out.append(f"log({arg},{base})")
            else:
                out.append("log("); out.append(base); out.append(")")
        else:
            out.append(s[i]); i += 1
    return "".join(out)

def _replace_abs_bars(s: str) -> str:
    # Replace |...| with abs(...), supports multiple pairs.
    res, open_flag = [], False
    for ch in s:
        if ch == "|":
            if not open_flag:
                res.append("abs(")
            else:
                res.append(")")
            open_flag = not open_flag
        else:
            res.append(ch)
    return "".join(res)

def _replace_sum(s: str) -> str:
    # \sum_{i=a}^{b} body  -> __SUM__(i,a,b,(body))
    # body may be {...} or (...) or next token
    patt = re.compile(r"\\sum_\{([^}=]+)=([^}]+)\}\^\{([^}]+)\}")
    while True:
        m = patt.search(s)
        if not m:
            return s
        var, lo, hi = m.group(1).strip(), m.group(2).strip(), m.group(3).strip()
        body_start = m.end()
        if body_start < len(s) and s[body_start] == "{":
            end, body = _balanced_slice(s, body_start, "{", "}")
            repl = f"__SUM__({var},{lo},{hi},({body}))"
            s = s[:m.start()] + repl + s[end+1:]
        elif body_start < len(s) and s[body_start] == "(":
            end, body = _balanced_slice(s, body_start, "(", ")")
            repl = f"__SUM__({var},{lo},{hi},({body}))"
            s = s[:m.start()] + repl + s[end+1:]
        else:
            # consume next token
            m2 = re.match(r"[A-Za-z0-9_\.]+", s[body_start:])
            body = m2.group(0) if m2 else ""
            repl = f"__SUM__({var},{lo},{hi},({body}))"
            s = s[:m.start()] + repl + s[body_start+len(body):]
    # never reached

def _latex_to_python(s: str) -> str:
    s = s.strip()
    # strip wrappers
    s = s.replace("$$", "").replace("$", "").replace(r"\(", "").replace(r"\)", "")
    s = s.replace(r"\left", "").replace(r"\right", "")

    # keep RHS if there's '='
    if "=" in s:
        s = s.split("=", 1)[1]

    # do the structured transforms first
    s = _replace_frac(s)
    s = _replace_exp_e(s)
    s = _replace_pow_braced(s)   # before generic ^
    s = _replace_log_base(s)
    s = _replace_sum(s)
    s = _replace_abs_bars(s)

    # \text{Var} -> Var
    s = re.sub(r"\\text\{([^}]*)\}", r"\1", s)
    # common functions/operators
    s = s.replace(r"\times", "*").replace(r"\cdot", "*").replace("·", "*")
    s = s.replace("−", "-")
    s = s.replace(r"\max", "max").replace(r"\min", "min")
    s = s.replace(r"\log", "log").replace(r"\ln", "ln")
    # greek/latex names: \alpha -> alpha, \sigma -> sigma, etc.
    s = re.sub(r"\\([A-Za-z]+)", r"\1", s)
    # bracketed variables E[R_m] -> E_R_m
    s = s.replace("[", "_").replace("]", "")
    s = s.replace(r"\_", "_")

    # remaining powers a^b -> a**b
    s = _replace_pow_simple(s)

    # convert any remaining braces to parentheses (for max{a,b}, etc.)
    s = s.replace("{", "(").replace("}", ")")

    # collapse whitespace
    s = re.sub(r"\s+", "", s)
    return s

def _eval_sum(body, var, lo, hi, scope):
    # inclusive bounds; allow expressions for lo/hi
    lo_v = int(round(eval(str(lo), {"__builtins__": None, **SAFE}, scope)))
    hi_v = int(round(eval(str(hi), {"__builtins__": None, **SAFE}, scope)))
    total = 0.0
    for _i in range(lo_v, hi_v + 1):
        scope[var] = _i
        total += eval(str(body), {"__builtins__": None, **SAFE}, scope)
    scope.pop(var, None)
    return total

def _evaluate(latex: str, vars_map: dict) -> float:
    expr = _latex_to_python(latex)
    scope = {k: float(v) for k, v in vars_map.items()}

    # support __SUM__(i, lo, hi, (body))
    def __SUM__(var, lo, hi, body):
        return _eval_sum(body, var, lo, hi, scope)

    val = eval(expr, {"__builtins__": None, **SAFE, "__SUM__": __SUM__}, scope)
    return float(f"{float(val):.4f}")

@app.route("/trading-formula", methods=["POST", "OPTIONS"], strict_slashes=False)
def trading_formula():
    if request.method == "OPTIONS":
        return ("", 204)
    payload = request.get_json(silent=True)
    if payload is None:
        try:
            payload = json.loads((request.data or b"").decode("utf-8"))
        except Exception:
            return jsonify(error="Expected JSON array body"), 400
    if not isinstance(payload, list):
        return jsonify(error="Body must be a JSON array of testcases"), 400

    out = []
    for t in payload:
        try:
            out.append({"result": _evaluate(t["formula"], t.get("variables", {}))})
        except Exception as e:
            # log and return 0.0 for robustness (you can switch to 400 if desired)
            app.logger.exception("formula failed: %r", t.get("formula"))
            out.append({"result": 0.0})
    return jsonify(out), 200

## FOG OF WALL

## SNAKES AND LADDERS


SQUARE = 32  # each square is 32x32 per spec


# -------- SVG parsing --------
def _parse_viewbox(vb: str) -> Tuple[float, float, float, float]:
    parts = [float(x) for x in vb.strip().split()]
    if len(parts) != 4:
        raise ValueError("Invalid viewBox")
    return parts[0], parts[1], parts[2], parts[3]  # minx, miny, width, height


def _iter_svg_elems(root):
    # namespace-agnostic iteration (tags may be '{ns}line')
    for elem in root.iter():
        tag = elem.tag
        if isinstance(tag, str) and tag.startswith("{"):
            tag = tag.split("}", 1)[1]
        yield tag, elem


def _round_int(x: float) -> int:
    # robust banker's rounding avoidance
    return int(round(x))


def _coord_to_cell(x: float, y: float, minx: float, miny: float) -> Tuple[int, int]:
    """
    Convert SVG coordinate (center of a square) to zero-based (col_from_left, row_from_top)
    """
    col = _round_int((x - (minx + SQUARE / 2.0)) / SQUARE)
    row = _round_int((y - (miny + SQUARE / 2.0)) / SQUARE)
    return col, row


def _cell_to_square(col: int, row_from_top: int, W: int, H: int) -> int:
    """
    Boustrophedon numbering:
      - Square 1 starts at bottom-left (row_from_bottom = 0, col_left = 0)
      - Next row alternates direction; end on top-left.
    """
    r_bot = (H - 1) - row_from_top
    if r_bot % 2 == 0:
        # left -> right
        sq = r_bot * W + (col + 1)
    else:
        # right -> left
        sq = r_bot * W + (W - col)
    return sq


def parse_board(svg_text: str) -> Tuple[int, int, int, Dict[int, int]]:
    """
    Returns (W, H, N, jumps) where jumps maps start_square -> end_square.
    """
    try:
        root = ET.fromstring(svg_text)
    except ET.ParseError as e:
        raise ValueError(f"Invalid SVG: {e}")

    # get viewBox
    vb = root.attrib.get("viewBox")
    if not vb:
        # sometimes width/height present; if so, synthesize a viewBox
        width = float(root.attrib.get("width", "0").replace("px", "") or 0)
        height = float(root.attrib.get("height", "0").replace("px", "") or 0)
        if width <= 0 or height <= 0:
            raise ValueError("SVG missing viewBox and width/height")
        minx = miny = 0.0
        vw = width
        vh = height
    else:
        minx, miny, vw, vh = _parse_viewbox(vb)

    # board W,H in squares (guaranteed 16..32; H even)
    Wf = vw / SQUARE
    Hf = vh / SQUARE
    W = _round_int(Wf)
    H = _round_int(Hf)
    if W <= 0 or H <= 0:
        raise ValueError("Bad board dimensions")

    # find all <line> elements as jumps
    jumps: Dict[int, int] = {}
    for tag, elem in _iter_svg_elems(root):
        if tag != "line":
            continue
        try:
            x1 = float(elem.attrib["x1"])
            y1 = float(elem.attrib["y1"])
            x2 = float(elem.attrib["x2"])
            y2 = float(elem.attrib["y2"])
        except KeyError:
            continue  # ignore malformed lines

        c1 = _coord_to_cell(x1, y1, minx, miny)
        c2 = _coord_to_cell(x2, y2, minx, miny)
        if not (0 <= c1[0] < W and 0 <= c1[1] < H and 0 <= c2[0] < W and 0 <= c2[1] < H):
            # if any line endpoint falls outside grid, ignore (robustness)
            continue

        s = _cell_to_square(c1[0], c1[1], W, H)
        e = _cell_to_square(c2[0], c2[1], W, H)
        if s == e:
            continue
        # per spec, green ladders, red snakes; we can just map start->end regardless of direction
        # as inputs won't have conflicts.
        jumps[s] = e

    N = W * H
    return W, H, N, jumps


# -------- Game mechanics --------
REGULAR = 0
POWER2 = 1


def apply_move(pos: int, mode: int, roll: int, N: int, jumps: Dict[int, int]) -> Tuple[int, int]:
    """
    Given current pos (0..N), die mode, and face (1..6), return (new_pos, new_mode).
    - Overshoot bounces back.
    - Apply jump if landing square is a jump start.
    - Mode switching rules:
        REGULAR: roll==6 -> switch to POWER2
        POWER2 : roll==1 -> switch to REGULAR
    """
    assert 1 <= roll <= 6
    step = roll if mode == REGULAR else (1 << roll)  # 2,4,8,16,32,64
    new_pos = pos + step
    if new_pos > N:
        new_pos = 2 * N - new_pos  # bounce back

    # jump
    new_pos = jumps.get(new_pos, new_pos)

    # mode switch
    if mode == REGULAR and roll == 6:
        new_mode = POWER2
    elif mode == POWER2 and roll == 1:
        new_mode = REGULAR
    else:
        new_mode = mode

    return new_pos, new_mode


def build_transitions(N: int, jumps: Dict[int, int]) -> List[List[List[Tuple[int, int]]]]:
    """
    transitions[mode][pos][roll-1] -> (npos, nmode)
    pos 0..N inclusive
    """
    transitions = [[[None] * 6 for _ in range(N + 1)] for _ in range(2)]
    for mode in (REGULAR, POWER2):
        for pos in range(N + 1):
            for r in range(1, 7):
                transitions[mode][pos][r - 1] = apply_move(pos, mode, r, N, jumps)
    return transitions


# -------- Solver (BFS with helpful roll ordering) --------
State = Tuple[int, int, int, int, int]
# (p1pos, p2pos, p1mode, p2mode, turn) where turn=0 (P1 to move) or 1 (P2 to move)


def _roll_order_for_player(pos: int, mode: int, N: int, transitions, favor_forward: bool) -> List[int]:
    """
    Produce 1..6 ordered so we enqueue promising moves first:
      - On P2's turn (favor_forward=True), try rolls that lead to largest new position first.
      - On P1's turn (favor_forward=False), try rolls that lead to smallest new position first.
    """
    candidates = []
    for r in range(1, 7):
        npos, _ = transitions[mode][pos][r - 1]
        candidates.append((npos, r))
    candidates.sort(key=lambda t: (t[0], t[1]), reverse=favor_forward)
    return [r for _, r in candidates]


def solve_rolls(N: int, jumps: Dict[int, int], time_limit_s: Optional[float] = None) -> str:
    """
    Find a global die-face sequence so that the *second* player (last player) wins first.
    Returns a string like '123456'.
    """
    transitions = build_transitions(N, jumps)

    start: State = (0, 0, REGULAR, REGULAR, 0)  # P1 starts, both in regular mode
    if N == 1:
        # trivial one-square board (won't happen per constraints but keep it safe)
        return ""

    q = deque([start])
    visited = set([start])
    parent: Dict[State, Tuple[Optional[State], Optional[int]]] = {start: (None, None)}

    t0 = time.time()

    while q:
        if time_limit_s is not None and (time.time() - t0) > time_limit_s:
            break  # give up within time budget

        p1pos, p2pos, m1, m2, turn = q.popleft()

        # establish whose turn and their current state
        if turn == 0:
            pos = p1pos
            mode = m1
            favor_forward = False  # try to stall P1
        else:
            pos = p2pos
            mode = m2
            favor_forward = True  # push P2 forward

        # choose roll exploration order
        for r in _roll_order_for_player(pos, mode, N, transitions, favor_forward):
            npos, nmode = transitions[mode][pos][r - 1]

            if turn == 0:
                # P1 moves
                if npos == N:
                    # P1 would win here; reject this path (game ends with P1, not allowed)
                    continue
                next_state: State = (npos, p2pos, nmode, m2, 1)  # switch to P2
            else:
                # P2 moves
                if npos == N:
                    # SUCCESS: P2 (last player) wins first
                    # reconstruct path
                    rolls: List[int] = [r]
                    cur = (p1pos, p2pos, m1, m2, turn)
                    while True:
                        prev, prev_roll = parent[cur]
                        if prev is None:
                            break
                        if prev_roll is not None:
                            rolls.append(prev_roll)
                        cur = prev
                    rolls.reverse()
                    return "".join(str(d) for d in rolls)
                next_state = (p1pos, npos, m1, nmode, 0)  # switch back to P1

            if next_state not in visited:
                visited.add(next_state)
                parent[next_state] = ((p1pos, p2pos, m1, m2, turn), r)
                q.append(next_state)

    # If we get here, BFS failed within time budget (or no solution found, which is unlikely given constraints).
    # Fallback: produce a harmless small sequence so the judge at least parses it (score 0 but valid SVG).
    return "1" * 32  # minimal, but well-formed


# -------- Flask endpoint --------
def _solve_svg(svg_text: str) -> str:
    W, H, N, jumps = parse_board(svg_text)
    # BFS without a hard time limit by default (adjustable via env var)
    tl = os.environ.get("SLPU_TIME_LIMIT_S")
    time_limit_s = float(tl) if tl else None
    rolls = solve_rolls(N, jumps, time_limit_s=time_limit_s)
    # Must respond with a single <text> element containing the digits
    return f'<svg xmlns="http://www.w3.org/2000/svg"><text>{rolls}</text></svg>'


@app.post("/slpu")
def slpu():
    try:
        svg_in = request.get_data(as_text=True)
        out_svg = _solve_svg(svg_in)
        return Response(out_svg, mimetype="image/svg+xml")
    except Exception as e:
        # Always return a parseable SVG (judge will score 0 if invalid or losing).
        fallback = f'<svg xmlns="http://www.w3.org/2000/svg"><text>111111</text></svg>'
        # You can log e for debugging in your infra
        return Response(fallback, mimetype="image/svg+xml")


@app.get("/")
def health():
    return "OK", 200

## FOG OF WALL

GAMES: dict[tuple[str, str], dict] = {}

def game_key(payload: dict) -> tuple[str, str]:
    return (str(payload.get("challenger_id")), str(payload.get("game_id")))

# ------------------------------ Helpers ------------------------------

DIRS: dict[str, tuple[int, int]] = {
    "N": (0, -1),
    "S": (0,  1),
    "E": (1,  0),
    "W": (-1, 0),
}
DIR_ORDER = ["N", "E", "S", "W"]  # tie-breaking for path shape

def in_bounds(x: int, y: int, L: int) -> bool:
    return 0 <= x < L and 0 <= y < L

def bfs_next_step(start: tuple[int,int], goal: tuple[int,int], L: int, is_wall: t.Callable[[int,int], bool]) -> tuple[str|None, list[tuple[int,int]]|None]:
    """Return (dir, path) where dir is first step direction toward goal avoiding known walls.
       Unknown cells are treated as traversable (optimistic); 'is_wall(x,y)' says if currently known as wall.
       If already at goal -> (None, []).
    """
    if start == goal:
        return None, []

    sx, sy = start
    gx, gy = goal
    q = deque([(sx, sy)])
    parent: dict[tuple[int,int], tuple[int,int]|None] = {(sx, sy): None}

    while q:
        x, y = q.popleft()
        for d in DIR_ORDER:
            dx, dy = DIRS[d]
            nx, ny = x + dx, y + dy
            if not in_bounds(nx, ny, L):
                continue
            if is_wall(nx, ny):
                continue
            if (nx, ny) in parent:
                continue
            parent[(nx, ny)] = (x, y)
            if (nx, ny) == (gx, gy):
                # reconstruct
                path = [(gx, gy)]
                cur = (x, y)
                while cur is not None:
                    path.append(cur)
                    cur = parent[cur]
                path.reverse()  # start -> ... -> goal
                first = path[1]  # first move from start
                fx, fy = first
                ddx, ddy = fx - sx, fy - sy
                for d2, (vx, vy) in DIRS.items():
                    if (ddx, ddy) == (vx, vy):
                        return d2, path
                return None, path
            q.append((nx, ny))

    # no path found under current knowledge (rare unless boxed in)
    return None, None

def centers_mod5(L: int) -> list[int]:
    """All indices k in [0..L-1] such that k ≡ 2 (mod 5). Ensure at least one fallback center exists."""
    cs = [k for k in range(L) if (k - 2) % 5 == 0]
    if not cs:
        # tiny boards fallback: pick middle
        cs = [L // 2]
    return cs

def build_scan_centers(L: int) -> set[tuple[int,int]]:
    xs = centers_mod5(L)
    ys = centers_mod5(L)
    return {(x, y) for x in xs for y in ys}

def format_submission(walls_set: set[tuple[int,int]]) -> list[str]:
    return [f"{x}-{y}" for (x, y) in sorted(walls_set, key=lambda p: (p[0], p[1]))]

# --------------------------- Game lifecycle --------------------------

def init_game(payload: dict):
    """Initialize state for a new test case."""
    tc = payload["test_case"]
    L = int(tc["length_of_grid"])
    N = int(tc["num_of_walls"])
    crows = { str(c["id"]): (int(c["x"]), int(c["y"])) for c in tc["crows"] }

    centers = build_scan_centers(L)

    # Map legend: '?' unknown, '.' empty, 'W' wall
    grid: list[list[str]] = [["?" for _ in range(L)] for _ in range(L)]
    for _, (cx, cy) in crows.items():
        if in_bounds(cx, cy, L):
            grid[cy][cx] = "."  # we stand on a free cell

    GAMES[game_key(payload)] = {
        "L": L,                       # grid size
        "N": N,                       # number of walls to discover
        "grid": grid,                 # discovered map
        "walls": set(),               # {(x,y)}
        "scanned": set(),             # {(x,y)} positions we've scanned from
        "centers": set(centers),      # planned tiling scan positions
        "crows": dict(crows),         # id -> (x,y)
        "assignments": {},            # id -> target (x,y)
        "turn_idx": 0,                # for fair fallback turns
        "crow_list": list(crows.keys()),
    }

def state_for(payload: dict):
    return GAMES.get(game_key(payload))

# ----------------------------- Learning ------------------------------

def mark_cell(st: dict, x: int, y: int, val: str):
    """val in {'.','W'}; keep 'W' dominating, otherwise prefer known over unknown."""
    if not in_bounds(x, y, st["L"]):
        return
    prev = st["grid"][y][x]
    if val == "W":
        st["grid"][y][x] = "W"
        st["walls"].add((x, y))
    elif prev == "?":
        st["grid"][y][x] = "."

def integrate_scan(st: dict, crow_id: str, scan_result: list[list[str]]):
    cx, cy = st["crows"][crow_id]
    L = st["L"]
    # scan_result is 5x5, row-major, [0][0] = (cx-2, cy-2)
    for r in range(5):
        row = scan_result[r] if r < len(scan_result) else []
        for c in range(5):
            ch = row[c] if c < len(row) else "_"
            ax = cx + (c - 2)
            ay = cy + (r - 2)
            if ch == "X":
                continue
            if not in_bounds(ax, ay, L):
                continue
            if ch == "W":
                mark_cell(st, ax, ay, "W")
            else:
                # '_' or 'C' => free
                mark_cell(st, ax, ay, ".")
    st["scanned"].add((cx, cy))

def _parse_xy(value) -> tuple[int, int] | None:
    """Accepts [x, y], (x, y), or dict forms like {'x':1,'y':2} or {'position':[x,y]}.
       Returns (x, y) as ints or None if unparseable.
    """
    if value is None:
        return None
    # list/tuple
    if isinstance(value, (list, tuple)) and len(value) >= 2:
        try:
            return int(value[0]), int(value[1])
        except Exception:
            return None
    # dict variants
    if isinstance(value, dict):
        if "x" in value and "y" in value:
            try:
                return int(value["x"]), int(value["y"])
            except Exception:
                return None
        for k in ("position", "pos", "coord", "coords", "coordinate", "coordinates", "xy"):
            if k in value:
                inner = value[k]
                if isinstance(inner, (list, tuple)) and len(inner) >= 2:
                    try:
                        return int(inner[0]), int(inner[1])
                    except Exception:
                        return None
                if isinstance(inner, dict) and "x" in inner and "y" in inner:
                    try:
                        return int(inner["x"]), int(inner["y"])
                    except Exception:
                        return None
    return None

def learn_from_move(st: dict, crow_id: str, direction: str | None, move_result_xy):
    old_x, old_y = st["crows"][crow_id]
    parsed = _parse_xy(move_result_xy)
    if parsed is None:
        # Can't interpret the server payload; ensure current cell marked free and stop.
        mark_cell(st, old_x, old_y, ".")
        return

    nx, ny = parsed

    # If we didn't move, we likely hit a wall in the attempted direction (if provided).
    if (nx, ny) == (old_x, old_y):
        if direction in DIRS:
            dx, dy = DIRS[direction]
            wx, wy = old_x + dx, old_y + dy
            if in_bounds(wx, wy, st["L"]):
                mark_cell(st, wx, wy, "W")
        # Keep current position marked as free.
        mark_cell(st, old_x, old_y, ".")
        return

    # Successful move; mark new cell free and update crow position.
    mark_cell(st, nx, ny, ".")
    st["crows"][crow_id] = (nx, ny)

# ----------------------------- Planning ------------------------------

def assign_targets(st: dict):
    """Greedy nearest-center assignment for each crow to an UNscanned center not already scanned or assigned."""
    unscanned_centers = [p for p in st["centers"] if p not in st["scanned"]]
    # Remove centers we already learned to be walls (can't stand there)
    unscanned_centers = [p for p in unscanned_centers if st["grid"][p[1]][p[0]] != "W"]
    taken: set[tuple[int,int]] = set()
    new_assign: dict[str, tuple[int,int] | None] = {}
    for cid, (cx, cy) in st["crows"].items():
        # if already on an unscanned center, keep that target
        if (cx, cy) in unscanned_centers:
            new_assign[cid] = (cx, cy)
            taken.add((cx, cy))
            continue
        # choose nearest available center
        best = None
        best_d = 10**9
        for p in unscanned_centers:
            if p in taken:
                continue
            d = abs(p[0] - cx) + abs(p[1] - cy)
            if d < best_d:
                best_d, best = d, p
        new_assign[cid] = best
        if best is not None:
            taken.add(best)
    st["assignments"] = new_assign

def any_on_unscanned_center(st: dict) -> str|None:
    for cid, (cx, cy) in st["crows"].items():
        if (cx, cy) in st["centers"] and (cx, cy) not in st["scanned"]:
            return cid
    return None

def pick_move(st: dict) -> tuple[str, str]:
    """Pick a crow and a 1-step move toward its assigned target.
       Returns (crow_id, direction|'SCAN_IN_PLACE')
    """
    L = st["L"]

    # Ensure we have assignments
    assign_targets(st)

    # Prefer the crow with the shortest planned path
    best: tuple[str, str] | None = None
    best_len = 10**9
    for cid, target in st["assignments"].items():
        if target is None:
            continue
        cur = st["crows"][cid]

        # if standing on target, scanning will be handled elsewhere
        if cur == target:
            continue

        def is_wall(x, y):
            return st["grid"][y][x] == "W"

        d, path = bfs_next_step(cur, target, L, is_wall)
        if d is not None and path is not None:
            plen = len(path)
            if plen < best_len:
                best_len = plen
                best = (cid, d)

    if best is not None:
        return best[0], best[1]

    # Fallback 1: If boxed / no path, scan in place for any crow not yet scanned from its current cell
    for cid, (cx, cy) in st["crows"].items():
        if (cx, cy) not in st["scanned"]:
            return cid, "SCAN_IN_PLACE"

    # Fallback 2: Find any unknown cell and steer a crow to a scan point that covers it.
    unknowns = []
    for y in range(L):
        for x in range(L):
            if st["grid"][y][x] == "?":
                unknowns.append((x, y))
    if unknowns:
        ux, uy = unknowns[0]
        # pick a scan position whose 5x5 includes (ux,uy)
        tx = min(max(ux, 2), L - 3)
        ty = min(max(uy, 2), L - 3)
        best_cid, best_d, best_dir = None, 10**9, None
        for cid, (cx, cy) in st["crows"].items():
            def is_wall(x, y):
                return st["grid"][y][x] == "W"
            d, path = bfs_next_step((cx, cy), (tx, ty), L, is_wall)
            if d is not None and path is not None:
                plen = len(path)
                if plen < best_d:
                    best_cid, best_d, best_dir = cid, plen, d
        if best_cid is not None and best_dir is not None:
            return best_cid, best_dir

    # Fallback 3: round-robin a scan to shake loose info
    idx = st["turn_idx"] % max(1, len(st["crow_list"]))
    st["turn_idx"] += 1
    cid = st["crow_list"][idx]
    return cid, "SCAN_IN_PLACE"

# ------------------------------ Endpoint -----------------------------

@app.route("/fog-of-wall", methods=["POST"])
def fog_of_wall():
    payload = request.get_json(force=True)

    # Start new test case
    if "test_case" in payload and payload.get("previous_action") is None:
        init_game(payload)

    st = state_for(payload)
    if st is None:
        # Defensive: initialize if missing
        init_game(payload)
        st = state_for(payload)

    # Integrate result of previous action (if any)
    prev = payload.get("previous_action")
    if prev:
        crow_id = str(prev.get("crow_id"))
        act = prev.get("your_action")
        if act == "move":
            direction = prev.get("direction")  # may be None on some servers
            move_res = prev.get("move_result")
            # if crow_id might be missing or unknown, skip safely
            if crow_id in st["crows"]:
                learn_from_move(st, crow_id, direction, move_res)
        elif act == "scan":
            scan_res = prev.get("scan_result", [])
            if crow_id in st["crows"]:
                integrate_scan(st, crow_id, scan_res)

    # Submit if we've found all walls
    if len(st["walls"]) >= st["N"]:
        return jsonify({
            "challenger_id": payload.get("challenger_id"),
            "game_id": payload.get("game_id"),
            "action_type": "submit",
            "submission": format_submission(st["walls"]),
        })

    # If any crow is standing on an unscanned tiling center, scan now (best value)
    cid_scan = any_on_unscanned_center(st)
    if cid_scan is not None:
        return jsonify({
            "challenger_id": payload.get("challenger_id"),
            "game_id": payload.get("game_id"),
            "crow_id": cid_scan,
            "action_type": "scan",
        })

    # Otherwise move one step toward assigned centers; fallbacks handle boxed situations
    cid, decision = pick_move(st)
    if decision == "SCAN_IN_PLACE":
        return jsonify({
            "challenger_id": payload.get("challenger_id"),
            "game_id": payload.get("game_id"),
            "crow_id": cid,
            "action_type": "scan",
        })
    else:
        return jsonify({
            "challenger_id": payload.get("challenger_id"),
            "game_id": payload.get("game_id"),
            "crow_id": cid,
            "action_type": "move",
            "direction": decision,
        })
    

#Blankety Blanks
@app.route("/blankety", methods=["POST"])
def blankety():
    """
    Impute missing values in 100 time series using pure Python.
    Each series has 1000 elements with some null values.
    """
    try:
        data = request.get_json()
        series_list = data.get("series", [])
        
        if not series_list:
            return jsonify({"error": "No series provided"}), 400
        
        imputed_series = []
        
        for series in series_list:
            # Impute the series
            imputed = impute_series_advanced(series)
            imputed_series.append(imputed)
        
        return jsonify({"answer": imputed_series})
    
    except Exception as e:
        return jsonify({"error": str(e)}), 500

def impute_series_advanced(series: List) -> List[float]:
    """
    Advanced imputation using pure Python with multiple strategies.
    """
    n = len(series)
    result = [None] * n
    
    # Extract valid points
    valid_points = []
    for i, val in enumerate(series):
        if val is not None:
            valid_points.append((i, float(val)))
            result[i] = float(val)
    
    # Handle edge cases
    if not valid_points:
        return [0.0] * n
    if len(valid_points) == n:
        return [float(v) for v in series]
    
    # Sort valid points
    valid_points.sort()
    
    # Calculate statistics for adaptive strategy
    missing_ratio = 1 - len(valid_points) / n
    values = [v for _, v in valid_points]
    
    # Detect signal characteristics
    is_periodic = detect_periodicity(valid_points)
    has_trend = detect_trend(valid_points)
    noise_level = estimate_noise(valid_points)
    
    # Choose and apply imputation strategy
    if missing_ratio < 0.3 and len(valid_points) >= 4:
        # Use cubic spline for dense data
        impute_cubic_segments(result, valid_points)
    elif is_periodic and len(valid_points) >= 10:
        # Use periodic interpolation
        impute_periodic(result, valid_points)
    elif has_trend:
        # Use polynomial fitting
        impute_polynomial(result, valid_points, degree=2)
    else:
        # Use piecewise linear
        impute_linear(result, valid_points)
    
    # Apply adaptive smoothing
    if noise_level > 0.1:
        result = apply_adaptive_smoothing(result, series, valid_points)
    
    # Final cleanup
    for i in range(n):
        if result[i] is None or math.isnan(result[i]) or math.isinf(result[i]):
            result[i] = get_safe_value(result, i, valid_points)
    
    return result

def detect_periodicity(valid_points: List[Tuple[int, float]]) -> bool:
    """
    Detect if the signal appears to be periodic.
    """
    if len(valid_points) < 10:
        return False
    
    values = [v for _, v in valid_points]
    n = len(values)
    
    # Simple autocorrelation check
    for lag in range(2, min(n // 2, 50)):
        correlation = 0
        count = 0
        for i in range(n - lag):
            correlation += values[i] * values[i + lag]
            count += 1
        if count > 0:
            correlation /= count
            if correlation > 0.7 * sum(v*v for v in values) / n:
                return True
    
    return False

def detect_trend(valid_points: List[Tuple[int, float]]) -> bool:
    """
    Detect if there's a significant trend in the data.
    """
    if len(valid_points) < 3:
        return False
    
    indices = [i for i, _ in valid_points]
    values = [v for _, v in valid_points]
    
    # Calculate linear regression slope
    n = len(indices)
    sum_x = sum(indices)
    sum_y = sum(values)
    sum_xy = sum(x * y for x, y in zip(indices, values))
    sum_x2 = sum(x * x for x in indices)
    
    if n * sum_x2 - sum_x * sum_x == 0:
        return False
    
    slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x)
    
    # Check if slope is significant relative to data range
    value_range = max(values) - min(values)
    if value_range == 0:
        return False
    
    expected_change = abs(slope) * (indices[-1] - indices[0])
    return expected_change > 0.3 * value_range

def estimate_noise(valid_points: List[Tuple[int, float]]) -> float:
    """
    Estimate noise level in the signal.
    """
    if len(valid_points) < 3:
        return 0.0
    
    values = [v for _, v in valid_points]
    
    # Calculate differences between consecutive values
    diffs = []
    for i in range(1, len(values)):
        diffs.append(abs(values[i] - values[i-1]))
    
    if not diffs:
        return 0.0
    
    # Noise estimate based on median absolute difference
    med_diff = median(diffs)
    value_range = max(values) - min(values)
    
    if value_range == 0:
        return 0.0
    
    return min(1.0, med_diff / value_range)

def impute_cubic_segments(result: List, valid_points: List[Tuple[int, float]]):
    """
    Impute using piecewise cubic interpolation.
    """
    n = len(result)
    
    for i in range(n):
        if result[i] is None:
            # Find 4 nearest valid points for cubic interpolation
            nearby = find_nearest_points(i, valid_points, 4)
            
            if len(nearby) >= 2:
                if len(nearby) >= 4:
                    # Cubic interpolation
                    result[i] = lagrange_interpolate(i, nearby[:4])
                elif len(nearby) >= 3:
                    # Quadratic interpolation
                    result[i] = lagrange_interpolate(i, nearby[:3])
                else:
                    # Linear interpolation
                    result[i] = linear_interp(i, nearby[0], nearby[1])

def impute_periodic(result: List, valid_points: List[Tuple[int, float]]):
    """
    Impute assuming periodic signal.
    """
    n = len(result)
    
    # Estimate period
    period = estimate_period(valid_points)
    
    for i in range(n):
        if result[i] is None:
            # Look for values at similar phase
            phase_values = []
            for idx, val in valid_points:
                phase_diff = abs((i - idx) % period)
                if phase_diff < period * 0.1:
                    phase_values.append(val)
            
            if phase_values:
                result[i] = sum(phase_values) / len(phase_values)
            else:
                # Fallback to linear
                nearby = find_nearest_points(i, valid_points, 2)
                if len(nearby) >= 2:
                    result[i] = linear_interp(i, nearby[0], nearby[1])
                elif nearby:
                    result[i] = nearby[0][1]
                else:
                    result[i] = 0.0

def impute_polynomial(result: List, valid_points: List[Tuple[int, float]], degree: int = 2):
    """
    Impute using polynomial fitting.
    """
    n = len(result)
    
    # Fit polynomial to valid points
    if len(valid_points) > degree:
        coeffs = fit_polynomial(valid_points, degree)
        
        for i in range(n):
            if result[i] is None:
                result[i] = evaluate_polynomial(coeffs, i)
    else:
        # Fallback to linear
        impute_linear(result, valid_points)

def impute_linear(result: List, valid_points: List[Tuple[int, float]]):
    """
    Simple linear interpolation between valid points.
    """
    n = len(result)
    
    for i in range(n):
        if result[i] is None:
            # Find surrounding valid points
            left = None
            right = None
            
            for idx, val in valid_points:
                if idx < i:
                    left = (idx, val)
                elif idx > i and right is None:
                    right = (idx, val)
                    break
            
            if left and right:
                # Linear interpolation
                result[i] = linear_interp(i, left, right)
            elif left:
                # Extrapolate from left
                if len(valid_points) >= 2:
                    # Use last two points for extrapolation
                    second_last = valid_points[-2] if valid_points[-1] == left else None
                    if second_last:
                        slope = (left[1] - second_last[1]) / (left[0] - second_last[0])
                        result[i] = left[1] + slope * (i - left[0])
                    else:
                        result[i] = left[1]
                else:
                    result[i] = left[1]
            elif right:
                # Extrapolate from right
                if len(valid_points) >= 2:
                    second = valid_points[1] if valid_points[0] == right else None
                    if second:
                        slope = (second[1] - right[1]) / (second[0] - right[0])
                        result[i] = right[1] + slope * (i - right[0])
                    else:
                        result[i] = right[1]
                else:
                    result[i] = right[1]
            else:
                result[i] = 0.0

def apply_adaptive_smoothing(result: List[float], original: List, valid_points: List[Tuple[int, float]]) -> List[float]:
    """
    Apply adaptive smoothing to reduce noise while preserving structure.
    """
    n = len(result)
    smoothed = result.copy()
    
    # Calculate local variance for adaptive smoothing
    for i in range(n):
        if original[i] is None:  # Only smooth imputed values
            # Determine window size based on local density
            window = get_adaptive_window(i, valid_points, n)
            
            # Apply weighted average
            weights = []
            values = []
            
            for j in range(max(0, i - window), min(n, i + window + 1)):
                weight = math.exp(-0.5 * ((j - i) / (window * 0.5)) ** 2)
                weights.append(weight)
                values.append(result[j])
            
            if weights:
                total_weight = sum(weights)
                smoothed[i] = sum(w * v for w, v in zip(weights, values)) / total_weight
    
    return smoothed

def find_nearest_points(index: int, valid_points: List[Tuple[int, float]], k: int) -> List[Tuple[int, float]]:
    """
    Find k nearest valid points to given index.
    """
    distances = [(abs(idx - index), idx, val) for idx, val in valid_points]
    distances.sort()
    return [(idx, val) for _, idx, val in distances[:k]]

def lagrange_interpolate(x: int, points: List[Tuple[int, float]]) -> float:
    """
    Lagrange polynomial interpolation.
    """
    result = 0.0
    n = len(points)
    
    for i in range(n):
        xi, yi = points[i]
        term = yi
        
        for j in range(n):
            if i != j:
                xj, _ = points[j]
                term *= (x - xj) / (xi - xj)
        
        result += term
    
    return result

def linear_interp(x: int, p1: Tuple[int, float], p2: Tuple[int, float]) -> float:
    """
    Linear interpolation between two points.
    """
    x1, y1 = p1
    x2, y2 = p2
    
    if x2 == x1:
        return (y1 + y2) / 2
    
    return y1 + (y2 - y1) * (x - x1) / (x2 - x1)

def estimate_period(valid_points: List[Tuple[int, float]]) -> int:
    """
    Estimate period of a potentially periodic signal.
    """
    if len(valid_points) < 10:
        return 50  # Default guess
    
    values = [v for _, v in valid_points]
    n = len(values)
    
    # Try different period lengths
    best_period = 50
    best_score = 0
    
    for period in range(10, min(n // 2, 200), 5):
        score = 0
        count = 0
        
        for i in range(n - period):
            score += values[i] * values[i + period]
            count += 1
        
        if count > 0 and score > best_score:
            best_score = score
            best_period = period
    
    return best_period

def fit_polynomial(valid_points: List[Tuple[int, float]], degree: int) -> List[float]:
    """
    Fit polynomial of given degree using least squares.
    """
    n = len(valid_points)
    
    # Build matrices for least squares
    A = []
    b = []
    
    for idx, val in valid_points:
        row = [idx ** i for i in range(degree + 1)]
        A.append(row)
        b.append(val)
    
    # Solve using Gaussian elimination (simplified)
    # For simplicity, just use linear regression for degree <= 2
    if degree == 1:
        # Linear regression
        sum_x = sum(idx for idx, _ in valid_points)
        sum_y = sum(val for _, val in valid_points)
        sum_xy = sum(idx * val for idx, val in valid_points)
        sum_x2 = sum(idx * idx for idx, _ in valid_points)
        
        if n * sum_x2 - sum_x * sum_x != 0:
            slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x)
            intercept = (sum_y - slope * sum_x) / n
            return [intercept, slope]
    elif degree == 2:
        # Quadratic regression (simplified)
        # Use three points if available
        if len(valid_points) >= 3:
            p1, p2, p3 = valid_points[0], valid_points[len(valid_points)//2], valid_points[-1]
            return fit_quadratic_three_points(p1, p2, p3)
    
    # Default to mean value
    mean_val = sum(val for _, val in valid_points) / n
    return [mean_val]

def fit_quadratic_three_points(p1: Tuple[int, float], p2: Tuple[int, float], p3: Tuple[int, float]) -> List[float]:
    """
    Fit quadratic through three points.
    """
    x1, y1 = p1
    x2, y2 = p2
    x3, y3 = p3
    
    # Solve system of equations for ax^2 + bx + c
    denom = (x1 - x2) * (x1 - x3) * (x2 - x3)
    
    if denom == 0:
        # Points are collinear, use linear
        if x3 != x1:
            slope = (y3 - y1) / (x3 - x1)
            intercept = y1 - slope * x1
            return [intercept, slope, 0]
        else:
            return [y1, 0, 0]
    
    a = (x3 * (y2 - y1) + x2 * (y1 - y3) + x1 * (y3 - y2)) / denom
    b = (x3*x3 * (y1 - y2) + x2*x2 * (y3 - y1) + x1*x1 * (y2 - y3)) / denom
    c = (x2 * x3 * (x2 - x3) * y1 + x3 * x1 * (x3 - x1) * y2 + x1 * x2 * (x1 - x2) * y3) / denom
    
    return [c, b, a]

def evaluate_polynomial(coeffs: List[float], x: int) -> float:
    """
    Evaluate polynomial at given point.
    """
    result = 0.0
    for i, coeff in enumerate(coeffs):
        result += coeff * (x ** i)
    return result

def get_adaptive_window(index: int, valid_points: List[Tuple[int, float]], n: int) -> int:
    """
    Determine adaptive window size based on local data density.
    """
    # Count nearby valid points
    nearby_count = sum(1 for idx, _ in valid_points if abs(idx - index) <= 50)
    
    if nearby_count >= 20:
        return 3  # Dense data, small window
    elif nearby_count >= 10:
        return 5  # Medium density
    else:
        return 10  # Sparse data, larger window

def get_safe_value(result: List, index: int, valid_points: List[Tuple[int, float]]) -> float:
    """
    Get a safe fallback value for failed imputation.
    """
    # Try local average
    window = 20
    local_values = []
    
    for i in range(max(0, index - window), min(len(result), index + window + 1)):
        if result[i] is not None and not math.isnan(result[i]) and not math.isinf(result[i]):
            local_values.append(result[i])
    
    if local_values:
        return sum(local_values) / len(local_values)
    
    # Use global average of valid points
    if valid_points:
        return sum(val for _, val in valid_points) / len(valid_points)
    
    return 0.0


## INK ARCHIVES
EPS = 1e-15

def _build_graph(goods, rates):
    """
    goods: list of strings
    rates: list of [src_index, dst_index, rate] entries

    Returns:
        n: number of goods
        edges: list of (u, v, rate)
        rate_map: dict[(u, v)] -> rate
    """
    n = len(goods)
    edges = []
    rate_map = {}
    for triplet in rates:
        if len(triplet) != 3:
            continue
        u, v, r = triplet
        if not (0 <= u < n and 0 <= v < n):
            continue
        if r is None:
            continue
        r = float(r)
        if r <= 0.0:
            continue
        edges.append((u, v, r))
        rate_map[(u, v)] = r  # last one wins if duplicates
    return n, edges, rate_map


def _bellman_ford_find_negative_cycle(n, edges, start):
    """
    Run Bellman-Ford from 'start' using weights w = -log(rate).
    If a negative cycle is detected, returns a list of vertex indices for one cycle (in order).
    Otherwise returns None.

    Implementation details:
    - parent[v] records predecessor when relaxing.
    - On the nth relaxation pass, any vertex updated implies a negative cycle reachable from 'start'.
    - To extract the actual cycle, follow parent pointers n times to land inside the cycle,
      then walk until you revisit the same node.
    """
    INF = float("inf")
    dist = [INF] * n
    parent = [-1] * n
    dist[start] = 0.0

    # Relax edges n-1 times
    for _ in range(n - 1):
        changed = False
        for u, v, r in edges:
            w = -log(r)
            if dist[u] < INF and dist[u] + w < dist[v] - EPS:
                dist[v] = dist[u] + w
                parent[v] = u
                changed = True
        if not changed:
            break

    # One more pass to check for negative cycle
    updated_vertex = -1
    for u, v, r in edges:
        w = -log(r)
        if dist[u] < INF and dist[u] + w < dist[v] - EPS:
            parent[v] = u
            updated_vertex = v
            break

    if updated_vertex == -1:
        return None

    # Ensure we are inside the cycle
    y = updated_vertex
    for _ in range(n):
        y = parent[y]

    # Extract the cycle
    cycle = []
    cur = y
    while True:
        cycle.append(cur)
        cur = parent[cur]
        if cur == y or cur == -1:
            break

    if cur == -1:
        # Shouldn't normally happen, but guard anyway
        return None

    cycle.reverse()  # order the cycle in the forward trading direction (parent -> child)
    return cycle


def _cycle_product(cycle, rate_map):
    """
    Given a cycle as a list of node indices [a, b, c, ..., a],
    compute product of rates along edges.
    Note: input 'cycle' here is just node order; we will close it when computing.
    """
    prod = 1.0
    L = len(cycle)
    for i in range(L):
        u = cycle[i]
        v = cycle[(i + 1) % L]
        r = rate_map.get((u, v))
        if r is None or r <= 0:
            return 0.0
        prod *= r
    return prod


def _best_arbitrage_cycle(goods, rates):
    """
    Returns dict with:
      - 'path': list of good names representing a closed cycle (includes final return to start)
      - 'gain': percent gain = (product - 1) * 100  (rounded to 6 decimals)
    If no profitable cycle, returns empty path and gain 0.
    """
    n, edges, rate_map = _build_graph(goods, rates)
    if n == 0 or not edges:
        return {"path": [], "gain": 0}

    best_prod = 1.0
    best_cycle_nodes = None

    # Try starting Bellman-Ford from each node to collect/compare cycles
    for s in range(n):
        cyc = _bellman_ford_find_negative_cycle(n, edges, s)
        if cyc is None:
            continue
        prod = _cycle_product(cyc, rate_map)
        if prod > best_prod + 1e-12:
            best_prod = prod
            best_cycle_nodes = cyc

    if best_cycle_nodes is None or best_prod <= 1.0 + 1e-12:
        return {"path": [], "gain": 0}

    # Build named path, explicitly closing the loop
    named = [goods[i] for i in best_cycle_nodes] + [goods[best_cycle_nodes[0]]]
    percent_gain = round((best_prod - 1.0) * 100.0, 6)
    return {"path": named, "gain": percent_gain}


def _solve_single(payload_obj):
    """
    Solve one challenge block of the form:
      {"goods": [...], "rates": [[u,v,rate], ...]}

    Returns the standard result dict.
    """
    goods = payload_obj.get("goods", [])
    rates = payload_obj.get("rates", [])
    return _best_arbitrage_cycle(goods, rates)


@app.route("/The-Ink-Archive", methods=["POST"])
def the_ink_archive():
    """
    Accepts either:
      1) A single JSON object: {"goods": [...], "rates": [...]}
      2) A JSON array of such objects: [ {...}, {...} ]
         - Convention: first is Part I; second is Part II

    Responds with:
      - For single object input: {"path":[...], "gain": number}
      - For array input: [ {"path":[...], "gain": number}, {"path":[...], "gain": number} ]
    """
    try:
        payload = request.get_json(force=True, silent=False)
    except Exception:
        return jsonify({"error": "Invalid JSON"}), 400

    if payload is None:
        return jsonify({"error": "Missing JSON body"}), 400

    # If it's a list, solve each entry
    if isinstance(payload, list):
        results = [_solve_single(obj) for obj in payload if isinstance(obj, dict)]
        return jsonify(results), 200

    # If it's a single object
    if isinstance(payload, dict):
        result = _solve_single(payload)
        return jsonify(result), 200

    return jsonify({"error": "Unexpected JSON structure"}), 400


# Miscellaneous
@app.route("/")
def testing():
    return "Hello UBS Global Coding Challenge 2025 Singapore"

if __name__ == '__main__':
    app.run()
