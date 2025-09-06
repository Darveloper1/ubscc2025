from flask import Flask, render_template, request, jsonify, send_from_directory, Response
import re
import math
from math import log
import heapq
from typing import Optional, Tuple, List, Dict, Set, Callable, Any
from collections import defaultdict, deque
from statistics import median
import string
import xml.etree.ElementTree as ET
import os
import time
import threading
import typing as t
import json
from werkzeug.exceptions import HTTPException, BadRequest
from dataclasses import dataclass

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
            4, #1-9 DONE (36 points)
            3,
            3,
            3,
            4,
            1,
            2,
            1,
            1,  #10-17 DONE (68 points)
            2,
            1,
            1,
            5,
            2,
            2,
            4,
            1  #18-25 (84 points)
        ]
    }



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


## INK ARCHIVES

def find_best_cycle(goods, ratios):
    n = len(goods)
    edges = [(u, v, rate) for u, v, rate in ratios]

    best_cycle = None
    best_gain = 1.0

    # Try starting from each node
    for start in range(n):
        # Bellman-Ford initialization
        dist = [float("inf")] * n
        parent = [-1] * n
        dist[start] = 0

        # Relax edges n-1 times
        for _ in range(n - 1):
            for u, v, rate in edges:
                w = -math.log(rate)
                if dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    parent[v] = u

        # Try to detect cycle
        for u, v, rate in edges:
            w = -math.log(rate)
            if dist[u] + w < dist[v]:
                # Cycle detected, reconstruct path
                cycle = []
                visited = set()
                x = v
                for _ in range(n):  # walk back up to n steps
                    x = parent[x]

                # Now collect the cycle
                cur = x
                while cur not in visited:
                    visited.add(cur)
                    cur = parent[cur]
                cycle_start = cur

                # Rebuild cycle path
                cycle_path = [cycle_start]
                cur = parent[cycle_start]
                while cur != cycle_start:
                    cycle_path.append(cur)
                    cur = parent[cur]
                cycle_path.reverse()
                cycle_path.append(cycle_start)

                # Calculate gain
                gain = 1.0
                for i in range(len(cycle_path) - 1):
                    u, v = cycle_path[i], cycle_path[i + 1]
                    for x, y, r in edges:
                        if x == u and y == v:
                            gain *= r
                            break

                if gain > best_gain:
                    best_gain = gain
                    best_cycle = [goods[i] for i in cycle_path]

    return {"path": best_cycle, "gain": (best_gain - 1) * 100 if best_cycle else 0}


@app.route("/The-Ink-Archive", methods=["POST"])
def the_ink_archive():
    try:
        data = request.get_json(force=True)
        results = []

        for dataset in data:
            goods = dataset.get("goods", [])
            ratios = dataset.get("ratios", [])
            result = find_best_cycle(goods, ratios)

            # Ensure safe JSON response
            if result["path"] is None:
                result["path"] = []
            result["gain"] = float(result["gain"])
            results.append(result)

        return jsonify(results)

    except Exception as e:
        # Print error in logs (visible in Render logs)
        print("Error:", str(e))
        return jsonify({"error": str(e)}), 500


# EPS = 1e-15

# def _build_graph(goods, rates):
#     """
#     goods: list[str]
#     rates: list[[u, v, rate]]

#     Returns:
#       n, adj (list[dict[v->rate]]), rate_map
#       - adj keeps the MAX rate for duplicate (u,v)
#       - rate_map[(u,v)] = chosen rate (max)
#     """
#     n = len(goods)
#     adj = [dict() for _ in range(n)]
#     rate_map = {}

#     for idx, t in enumerate(rates):
#         if not (isinstance(t, list) or isinstance(t, tuple)) or len(t) != 3:
#             continue
#         u, v, r = t
#         if not (isinstance(u, int) and isinstance(v, int)) or not (0 <= u < n and 0 <= v < n):
#             continue
#         try:
#             r = float(r)
#         except Exception:
#             continue
#         if r <= 0:
#             continue

#         # keep the best (max) rate for (u,v)
#         if v not in adj[u] or r > adj[u][v]:
#             adj[u][v] = r
#             rate_map[(u, v)] = r

#     return n, adj, rate_map


# def _canonical_rotate(cycle_nodes, goods):
#     """
#     Given an open cycle [n0, n1, ..., nL-1] (directed),
#     choose the rotation that starts with the lexicographically smallest good name.
#     """
#     L = len(cycle_nodes)
#     if L <= 1:
#         return cycle_nodes[:]
    
#     # Find all rotations and their corresponding good names
#     rotations = []
#     for i in range(L):
#         rot = cycle_nodes[i:] + cycle_nodes[:i]
#         # Get the sequence of good names for this rotation
#         names = [goods[node] for node in rot]
#         rotations.append((names, rot))
    
#     # Sort by the lexicographical order of good names
#     rotations.sort(key=lambda x: x[0])
    
#     # Return the rotation with the lexicographically smallest sequence
#     return rotations[0][1]


# def _best_cycle_max_product(goods, rates):
#     """
#     Finds the maximum-product directed cycle (length 2..n).
#     Returns:
#       {"path": [names..., names[0]], "gain": (prod-1)*100}  or  {"path": [], "gain": 0}
#     """
#     n, adj, rate_map = _build_graph(goods, rates)
#     if n == 0:
#         return {"path": [], "gain": 0}

#     best_prod = 1.0
#     best_closed_path_nodes = None  # full closed path [s, ..., s] in forward order

#     # Try each start node; DP over exact steps
#     for s in range(n):
#         dp = [[0.0] * n for _ in range(n + 1)]   # dp[k][v] = best product to v from s in exactly k steps
#         pred = [[-1] * n for _ in range(n + 1)]  # predecessor for reconstruction
#         dp[0][s] = 1.0

#         for k in range(1, n + 1):
#             for u in range(n):
#                 pu = dp[k - 1][u]
#                 if pu <= 0:
#                     continue
#                 for v, r in adj[u].items():
#                     cand = pu * r
#                     if cand > dp[k][v] + EPS:
#                         dp[k][v] = cand
#                         pred[k][v] = u

#             # if we are back at s with k>=2, we have a directed cycle of length k
#             if k >= 2 and dp[k][s] > 1.0 + EPS:
#                 prod = dp[k][s]
#                 if prod > best_prod + EPS:
#                     # reconstruct exact closed walk of length k from s to s
#                     nodes_rev = [s]
#                     cur = s
#                     kk = k
#                     ok = True
#                     while kk > 0:
#                         p = pred[kk][cur]
#                         if p == -1:
#                             ok = False
#                             break
#                         nodes_rev.append(p)
#                         cur = p
#                         kk -= 1
#                     if not ok:
#                         continue
#                     # nodes_rev = [s, ..., s] in reverse; reverse to forward order
#                     path_fwd = list(reversed(nodes_rev))  # [s, ..., s], len = k+1

#                     # sanity: ensure start == end
#                     if path_fwd[0] != s or path_fwd[-1] != s:
#                         continue

#                     best_prod = prod
#                     best_closed_path_nodes = path_fwd

#     if best_closed_path_nodes is None or best_prod <= 1.0 + EPS:
#         return {"path": [], "gain": 0}

#     # Convert closed path [s, ..., s] to open cycle nodes [n0,...,nL-1]
#     open_cycle = best_closed_path_nodes[:-1]

#     # Canonicalize rotation using lexicographical order of good names
#     open_cycle = _canonical_rotate(open_cycle, goods)

#     named = [goods[i] for i in open_cycle] + [goods[open_cycle[0]]]
#     gain = (best_prod - 1.0) * 100.0  # do NOT round; many graders check the raw float
#     return {"path": named, "gain": gain}


# def _solve_single(obj):
#     goods = obj.get("goods", [])
#     rates = obj.get("rates", [])
#     return _best_cycle_max_product(goods, rates)


# @app.route("/The-Ink-Archive", methods=["POST"])
# def the_ink_archive():
#     try:
#         payload = request.get_json(force=True, silent=False)
#     except Exception:
#         return jsonify({"error": "Invalid JSON"}), 400

#     if payload is None:
#         return jsonify({"error": "Missing JSON body"}), 400

#     if isinstance(payload, list):
#         return jsonify([_solve_single(x) for x in payload if isinstance(x, dict)]), 200

#     if isinstance(payload, dict):
#         return jsonify(_solve_single(payload)), 200

#     return jsonify({"error": "Unexpected JSON structure"}), 400

## DUO LINGO SORT

# -------------------------
# Utilities: Roman numerals
# -------------------------
_ROMAN_MAP = {
    'I': 1, 'V': 5, 'X': 10, 'L': 50,
    'C': 100, 'D': 500, 'M': 1000
}
_ROMAN_PATTERN = re.compile(r'^(M{0,3})(CM|CD|D?C{0,3})'
                            r'(XC|XL|L?X{0,3})(IX|IV|V?I{0,3})$')

def is_roman(s: str) -> bool:
    s = s.strip().upper()
    return bool(s) and bool(re.fullmatch(r'[IVXLCDM]+', s)) and bool(_ROMAN_PATTERN.match(s))

def roman_to_int(s: str) -> int:
    s = s.strip().upper()
    total = 0
    i = 0
    while i < len(s):
        v = _ROMAN_MAP[s[i]]
        if i+1 < len(s) and _ROMAN_MAP[s[i+1]] > v:
            total += _ROMAN_MAP[s[i+1]] - v
            i += 2
        else:
            total += v
            i += 1
    return total

# -------------------------
# Utilities: Arabic digits
# -------------------------
def is_arabic_digits(s: str) -> bool:
    return bool(re.fullmatch(r'\d+', s.strip()))

# -------------------------
# Utilities: English words
# -------------------------
_EN_UNITS = {
    "zero":0, "one":1, "two":2, "three":3, "four":4, "five":5,
    "six":6, "seven":7, "eight":8, "nine":9, "ten":10, "eleven":11,
    "twelve":12, "thirteen":13, "fourteen":14, "fifteen":15,
    "sixteen":16, "seventeen":17, "eighteen":18, "nineteen":19
}
_EN_TENS = {
    "twenty":20, "thirty":30, "forty":40, "fifty":50,
    "sixty":60, "seventy":70, "eighty":80, "ninety":90
}
_EN_SCALES = {"hundred":100, "thousand":1_000, "million":1_000_000, "billion":1_000_000_000}

def maybe_english_to_int(s: str) -> int | None:
    # Normalize
    t = s.strip().lower()
    if not re.fullmatch(r"[a-z\- ]+", t):
        return None
    t = t.replace("-", " ")
    tokens = [w for w in t.split() if w and w != "and"]
    if not tokens:
        return None

    total, current = 0, 0
    for w in tokens:
        if w in _EN_UNITS:
            current += _EN_UNITS[w]
        elif w in _EN_TENS:
            current += _EN_TENS[w]
        elif w == "hundred":
            if current == 0:
                current = 1
            current *= 100
        elif w in ("thousand", "million", "billion"):
            scale = _EN_SCALES[w]
            if current == 0:
                current = 1
            total += current * scale
            current = 0
        else:
            return None
    return total + current

# -------------------------
# Utilities: Chinese numerals (Trad & Simp)
# -------------------------
# Works for 0 up to billions+ by sectioning at 億/亿 (1e8) and 萬/万 (1e4).
_CN_DIGITS = {
    '零':0, '〇':0, '○':0, 'Ｏ':0,
    '一':1, '二':2, '兩':2, '两':2, '三':3, '四':4, '五':5,
    '六':6, '七':7, '八':8, '九':9
}
_CN_UNITS = {'十':10, '百':100, '千':1000}
_BIG_UNITS = {'萬':10_000, '万':10_000, '億':100_000_000, '亿':100_000_000}

def contains_chinese_numeral(s: str) -> bool:
    return any(ch in _CN_DIGITS or ch in _CN_UNITS or ch in _BIG_UNITS for ch in s)

def chinese_to_int(s: str) -> int:
    s = s.strip()
    if s == "零" or s == "〇":
        return 0

    def parse_section(segment: str) -> int:
        # parse up to thousands within a 10^4 chunk
        num, last_unit = 0, 1
        current = 0
        i = 0
        # support leading '十' = 10..19
        if segment and segment[0] == '十':
            segment = '一' + segment
        while i < len(segment):
            ch = segment[i]
            if ch in _CN_DIGITS:
                current = _CN_DIGITS[ch]
                i += 1
                # If next is a small unit, apply; else just add later
                if i < len(segment) and segment[i] in _CN_UNITS:
                    unit = _CN_UNITS[segment[i]]
                    num += (current if current != 0 else 1) * unit
                    current = 0
                    i += 1
                else:
                    num += current
                    current = 0
            elif ch in _CN_UNITS:
                # e.g. '十' without explicit digit before
                unit = _CN_UNITS[ch]
                num += (1 if current == 0 else current) * unit
                current = 0
                i += 1
            else:
                # Ignore unrecognized char in this parser scope
                i += 1
        return num

    # Split by big units: 億/亿 then 萬/万
    total = 0
    # handle 億 / 亿
    def split_big(s_, unit_chars):
        idx = -1
        for uc in unit_chars:
            j = s_.rfind(uc)
            if j > idx:
                idx = j
        if idx >= 0:
            return s_[:idx], s_[idx+1:], True
        return s_, "", False

    # 1) billions (億/亿)
    left, right, has_yi = split_big(s, ['億','亿'])
    if has_yi:
        total += chinese_to_int(left) * 100_000_000
        s = right

    # 2) ten-thousands (萬/万)
    left, right, has_wan = split_big(s, ['萬','万'])
    if has_wan:
        total += chinese_to_int(left) * 10_000
        s = right

    # remainder (0..9999)
    total += parse_section(s)
    return total

def is_traditional_chinese(s: str) -> bool:
    return any(ch in "萬億兩" for ch in s)

def is_simplified_chinese(s: str) -> bool:
    return any(ch in "万亿两" for ch in s)

# -------------------------
# Utilities: German number words
# -------------------------
# Handles concatenations: tausend, hundert, ...und...zig, teens, zehn, etc.
_DE_UNITS = {
    "null":0, "ein":1, "eins":1, "eine":1, "einen":1, "einem":1, "einer":1,
    "zwei":2, "drei":3, "vier":4, "funf":5, "fuenf":5,
    "sechs":6, "sieben":7, "acht":8, "neun":9
}
_DE_TEENS = {
    "zehn":10, "elf":11, "zwolf":12, "zwoelf":12,
    "dreizehn":13, "vierzehn":14, "funfzehn":15, "fuenfzehn":15,
    "sechzehn":16, "siebzehn":17, "achtzehn":18, "neunzehn":19
}
_DE_TENS = {
    "zwanzig":20, "dreissig":30, "dreissig":30, "dreissig":30, "dreissig":30,
    "dreissig":30,  # keep key; normalization maps ß->ss and ä ö ü -> a o u
    "dreissig":30,  # idempotent
}
# Fill _DE_TENS properly (after normalization)
_DE_TENS = {
    "zwanzig":20, "dreissig":30, "dreissig":30, "dreißig":30,  # handled by normalization
    "vierzig":40, "funfzig":50, "fuenfzig":50,
    "sechzig":60, "siebzig":70, "achtzig":80, "neunzig":90
}
_DE_SCALES = {"hundert":100, "tausend":1000, "million":1_000_000, "millionen":1_000_000}

def _de_norm(t: str) -> str:
    t = t.lower().strip()
    t = t.replace("ß","ss")
    # map umlauts to plain vowels (keeps our mapping simple)
    t = (t.replace("ä","a").replace("ö","o").replace("ü","u")
           .replace("ae","a").replace("oe","o").replace("ue","u"))
    return t

def maybe_german_to_int(s: str) -> int | None:
    t = _de_norm(s)
    if not re.fullmatch(r"[a-z]+", t):
        return None

    # handle millions (rare in tasks, but supported)
    for kw in ("millionen","million"):
        if kw in t:
            parts = t.split(kw, 1)
            left = parts[0] or "ein"
            right = parts[1]
            lval = _de_parse_basic(left)  # how many millions
            if lval is None:
                return None
            rval = maybe_german_to_int(right) or 0
            return lval * 1_000_000 + rval

    # tausend
    if "tausend" in t:
        left, right = t.split("tausend", 1)
        left = left or "ein"
        lval = _de_parse_basic(left)
        if lval is None:
            return None
        rval = maybe_german_to_int(right) or 0
        return lval * 1000 + rval

    # hundert inside
    if "hundert" in t:
        left, right = t.split("hundert", 1)
        left = left or "ein"
        lval = _de_parse_basic(left)
        if lval is None:
            return None
        rval = _de_parse_basic(right) or 0
        return lval * 100 + rval

    # otherwise just tens/units/teens
    return _de_parse_basic(t)

def _de_parse_basic(t: str) -> int | None:
    if t == "" or t is None:
        return 0
    # exact matches
    if t in _DE_UNITS:
        return _DE_UNITS[t]
    if t in _DE_TEENS:
        return _DE_TEENS[t]
    if t in _DE_TENS:
        return _DE_TENS[t]
    # pattern: siebenundachtzig = sieben + und + achtzig
    if "und" in t:
        # split on the last 'und' to handle rare edge concatenations
        i = t.rfind("und")
        left, right = t[:i], t[i+3:]
        # left must be a unit; right a tens
        lu = _de_parse_basic(left)
        rt = _DE_TENS.get(right)
        if lu is not None and rt is not None:
            return rt + lu
        # fallback fail
        return None
    # handle composed tens like "vierundzwanzig" (already caught by 'und'),
    # teens already matched; nothing else left
    return None

# -------------------------
# Language detection & parse
# -------------------------
LANG_ROMAN = "roman"
LANG_EN = "english"
LANG_ZH_TRAD = "zh_trad"
LANG_ZH_SIMP = "zh_simp"
LANG_DE = "german"
LANG_ARABIC = "arabic"

# Tie-break order for Part 2 duplicates:
TIE_ORDER = [LANG_ROMAN, LANG_EN, LANG_ZH_TRAD, LANG_ZH_SIMP, LANG_DE, LANG_ARABIC]
TIE_INDEX = {lang:i for i,lang in enumerate(TIE_ORDER)}

def parse_any(s: str, part_two: bool = False) -> tuple[int, str]:
    raw = s

    # Arabic digits
    if is_arabic_digits(raw):
        return int(raw), LANG_ARABIC

    # Roman
    if is_roman(raw):
        return roman_to_int(raw), LANG_ROMAN

    # Chinese
    if contains_chinese_numeral(raw):
        val = chinese_to_int(raw)
        # decide trad vs simp for tie-order
        if is_traditional_chinese(raw):
            return val, LANG_ZH_TRAD
        if is_simplified_chinese(raw):
            return val, LANG_ZH_SIMP
        # ambiguous: default to trad slot (common for generic numerals like 十五)
        return val, LANG_ZH_TRAD

    # English
    en = maybe_english_to_int(raw)
    if en is not None:
        return en, LANG_EN

    # German
    de = maybe_german_to_int(raw)
    if de is not None:
        return de, LANG_DE

    # If nothing matched in Part 2, treat as error. In Part 1 the input is guaranteed (Roman/Arabic).
    raise ValueError(f"Unsupported numeral format: {raw}")


@app.route("/duolingo-sort", methods=["POST"])
def duolingo_sort():
    data = request.get_json(force=True, silent=False)
    part = str(data.get("part", "")).strip().upper()
    payload = data.get("challengeInput", {}) or {}
    items = payload.get("unsortedList", [])
    if not isinstance(items, list):
        return jsonify({"error": "challengeInput.unsortedList must be a list of strings"}), 400

    try:
        if part == "ONE":
            # Roman + Arabic input; output as decimal strings
            parsed = []
            for s in items:
                s2 = s.strip()
                if is_arabic_digits(s2):
                    parsed.append(int(s2))
                elif is_roman(s2):
                    parsed.append(roman_to_int(s2))
                else:
                    raise ValueError(f"Part ONE only accepts Roman numerals and Arabic digits. Got: {s2}")
            parsed.sort()
            return jsonify({"sortedList": [str(x) for x in parsed]})

        elif part == "TWO":
            enriched = []
            for s in items:
                val, lang = parse_any(s, part_two=True)
                enriched.append((val, TIE_INDEX.get(lang, 999), s, lang))
            # Sort by value, then by tie-order, then lexicographically for stability
            enriched.sort(key=lambda x: (x[0], x[1], x[2]))
            return jsonify({"sortedList": [s for (_, _, s, _) in enriched]})
        else:
            return jsonify({"error": "part must be 'ONE' or 'TWO'"}), 400
    except Exception as e:
        return jsonify({"error": str(e)}), 400
    
## SAILING CLUB

# ---------- helpers ----------

def merge_intervals(slots):
    """Merge intervals where next.start <= current.end (touching intervals merge)."""
    if not slots:
        return []
    slots = sorted(slots, key=lambda x: (x[0], x[1]))
    merged = []
    cur_start, cur_end = slots[0]
    for s, e in slots[1:]:
        if s <= cur_end:  # overlap or touching
            cur_end = max(cur_end, e)
        else:
            merged.append([cur_start, cur_end])
            cur_start, cur_end = s, e
    merged.append([cur_start, cur_end])
    return merged

def min_boats_needed(slots):
    """Sweep-line max concurrency; ends free boats before equal-time starts."""
    if not slots:
        return 0
    starts = sorted(s for s, _ in slots)
    ends   = sorted(e for _, e in slots)
    i = j = 0
    active = max_active = 0
    n = len(starts)
    while i < n and j < n:
        if starts[i] < ends[j]:
            active += 1
            if active > max_active: max_active = active
            i += 1
        else:
            active -= 1
            j += 1
    return max_active

# ---------- routes ----------

@app.route("/sailing-club", methods=["POST"])
def submission():
    # Accept strict JSON, but also sanitize common trailing commas in bodies
    raw = request.data.decode("utf-8") if request.data else ""
    if not raw:
        return jsonify({"error": "Empty body", "hint": "Send JSON with key 'testCases'"}), 400

    # Remove trailing commas before } or ]  (so your sample with trailing commas works)
    cleaned = re.sub(r",\s*([}\]])", r"\1", raw)

    try:
        payload = json.loads(cleaned)
    except Exception:
        return jsonify({"error": "Invalid JSON"}), 400

    test_cases = payload.get("testCases", [])
    if not isinstance(test_cases, list):
        return jsonify({"error": "'testCases' must be a list"}), 400

    solutions = []
    for case in test_cases:
        cid = (case or {}).get("id")
        slots = (case or {}).get("input", [])
        if cid is None:
            solutions.append({"id": None, "sortedMergedSlots": [], "minBoatsNeeded": 0})
            continue

        # keep only valid [start, end] with start < end and ints
        clean = []
        for it in slots:
            if (isinstance(it, (list, tuple)) and len(it) == 2
                and isinstance(it[0], int) and isinstance(it[1], int)
                and it[0] < it[1]):
                clean.append([it[0], it[1]])

        merged = merge_intervals(clean)
        boats  = min_boats_needed(clean)

        solutions.append({
            "id": cid,
            "sortedMergedSlots": merged,
            "minBoatsNeeded": boats
        })

    return jsonify({"solutions": solutions}), 200

## MAGE GAMBIT

def earliest_time_for_case(intel, reserve, fronts, stamina_max):
    """
    Compute earliest time (in minutes) to clear all intel while obeying:
      - Order of intel
      - Mana & stamina constraints
      - 10 min per new target, 0 min to extend same target
      - 10 min cooldown to fully restore
      - Must end in cooldown if at least one attack was cast
    """
    # Basic validation (kept lightweight to match challenge style)
    if reserve <= 0 or stamina_max <= 0 or fronts <= 0:
        return None  # invalid

    for f, mp in intel:
        if not (1 <= f <= fronts) or not (1 <= mp <= reserve):
            return None  # invalid

    mana = reserve
    stamina = stamina_max
    time = 0
    last_front = None          # None means no active “locked target”
    did_any_attack = False

    i = 0
    n = len(intel)
    while i < n:
        f, mp = intel[i]

        # Need resources before casting this spell?
        if mana < mp or stamina == 0:
            # cooldown
            time += 10
            mana = reserve
            stamina = stamina_max
            last_front = None  # target lock lost
            continue  # retry same intel after cooldown

        # We can cast now
        is_extension = (last_front == f and did_any_attack)
        # NOTE: Extension is only possible if previous action was an attack on the same front.
        # Our tracking uses last_front to represent the last attack's target.
        # If we just cooled down, last_front is None so extension won't apply.

        # Time cost: 0 if extension, otherwise 10
        time += 0 if is_extension else 10

        # Spend resources
        mana -= mp
        stamina -= 1
        did_any_attack = True
        last_front = f  # still locked to this front for possible extension on NEXT intel

        i += 1  # move to next intel

    # Must finish in cooldown if at least one attack happened and last action wasn't a cooldown
    # If we ended right after a cooldown (e.g., because there was no intel or we already cooled),
    # last_front would be None. The condition below only adds cooldown if we ended with an attack.
    if did_any_attack and last_front is not None:
        time += 10  # final cooldown

    return time


@app.route("/the-mages-gambit", methods=["POST"])
def the_mages_gambit():
    """
    Expected request body (application/json):
    [
      {
        "intel": [[2,1],[4,2],[4,2],[1,3]],
        "reserve": 3,
        "fronts": 5,
        "stamina": 4
      },
      ...
    ]

    Response (application/json):
    [
      { "time": 70 },
      ...
    ]
    """
    try:
        payload = request.get_json(force=True, silent=False)
        if not isinstance(payload, list):
            return jsonify({"error": "Body must be a JSON array of scenarios."}), 400

        results = []
        for case in payload:
            if not isinstance(case, dict):
                return jsonify({"error": "Each scenario must be an object."}), 400

            intel = case.get("intel")
            reserve = case.get("reserve")
            fronts = case.get("fronts")
            stamina = case.get("stamina")

            if not isinstance(intel, list) or not all(isinstance(x, (list, tuple)) and len(x) == 2 for x in intel):
                return jsonify({"error": "intel must be a list of [front, mp] pairs."}), 400
            if not all(isinstance(x[0], int) and isinstance(x[1], int) for x in intel):
                return jsonify({"error": "Each intel pair must be [int, int]."}), 400
            if not all(x[0] >= 1 and x[1] >= 1 for x in intel):
                return jsonify({"error": "Front and MP in intel must be >= 1."}), 400
            if not isinstance(reserve, int) or not isinstance(fronts, int) or not isinstance(stamina, int):
                return jsonify({"error": "reserve, fronts, stamina must be integers."}), 400

            t = earliest_time_for_case(intel, reserve, fronts, stamina)
            if t is None:
                return jsonify({"error": "Invalid parameters: check ranges for fronts, reserve, stamina, and intel."}), 400
            results.append({"time": t})

        return jsonify(results), 200

    except Exception as e:
        # Keep errors simple and clean for the challenge
        return jsonify({"error": str(e)}), 400


# Trading Bot
# --- simple sentiment keyword lists (extend as needed) ---
# POSITIVE_WORDS = {
#     "surge", "rally", "bull", "bullish", "gain", "gains", "soar", "skyrock",
#     "record", "beat", "up", "upside", "pump", "adopt", "adoption", "approve",
#     "signed", "clearance", "support", "backing", "strategic", "reserve"
# }
# NEGATIVE_WORDS = {
#     "crash", "dump", "bear", "bearish", "drop", "drops", "plummet", "panic",
#     "slash", "selloff", "sack", "sacks", "ban", "baned", "illegal", "fine",
#     "hack", "breach", "default", "debt", "loss", "lower", "down", "fall"
# }

# def clean_text(s: str) -> str:
#     return re.sub(r"[^A-Za-z0-9 ]+", " ", s.lower())

# def sentiment_score(title: str) -> float:
#     """
#     crude sentiment: (+1) if positive words appear, (-1) if negative appear.
#     If both appear, scores combine. Score normalized to [-1,1].
#     """
#     text = clean_text(title)
#     toks = set(text.split())
#     pos = len(POSITIVE_WORDS & toks)
#     neg = len(NEGATIVE_WORDS & toks)
#     if pos == 0 and neg == 0:
#         return 0.0
#     score = (pos - neg) / (pos + neg)
#     return max(-1.0, min(1.0, score))

# def safe_get_last_close(candles: List[Dict]) -> float:
#     if not candles:
#         return None
#     return float(candles[-1]["close"])

# def safe_get_first_obs_close(candles: List[Dict]) -> float:
#     if not candles:
#         return None
#     return float(candles[0]["close"])

# def compute_momentum(prev_candles: List[Dict], obs_candles: List[Dict]) -> float:
#     """
#     Returns a normalized momentum: (obs0_close - prev_last_close)/prev_last_close
#     If data missing returns 0.0
#     """
#     prev_close = safe_get_last_close(prev_candles)
#     obs0 = safe_get_first_obs_close(obs_candles)
#     if prev_close is None or obs0 is None or prev_close == 0:
#         return 0.0
#     return (obs0 - prev_close) / prev_close  # e.g. 0.01 => +1% move

# def compute_volatility(prev_candles: List[Dict]) -> float:
#     """
#     Simple volatility measure: std of returns across prev candles' closes.
#     If insufficient candles => small positive default.
#     """
#     closes = [float(c["close"]) for c in prev_candles if "close" in c]
#     if len(closes) < 2:
#         return 0.0
#     returns = []
#     for i in range(1, len(closes)):
#         prev = closes[i-1]
#         cur = closes[i]
#         if prev == 0:
#             continue
#         returns.append((cur - prev) / prev)
#     if not returns:
#         return 0.0
#     mean = sum(returns) / len(returns)
#     var = sum((r - mean) ** 2 for r in returns) / len(returns)
#     return math.sqrt(var)

# def sigmoid(x: float) -> float:
#     # numerically stable sigmoid
#     if x >= 0:
#         z = math.exp(-x)
#         return 1 / (1 + z)
#     else:
#         z = math.exp(x)
#         return z / (1 + z)

# def score_event(e: Dict) -> Dict:
#     """
#     Return a dict with id, probability_of_long, and decision.
#     Weights chosen heuristically. Deterministic (no training).
#     """
#     sid = e.get("id")
#     title = e.get("title", "")
#     prev = e.get("previous_candles", []) or []
#     obs = e.get("observation_candles", []) or []

#     s_sent = sentiment_score(title)          # [-1,1]
#     s_mom = compute_momentum(prev, obs)      # small-ish (e.g. -0.05..+0.05)
#     s_vol = compute_volatility(prev)         # e.g. 0..0.05 typically

#     # Heuristic combination:
#     # - momentum is strong signal: positive => favors LONG, negative => SHORT
#     # - sentiment nudges direction
#     # - volatility reduces confidence slightly (divides contribution)
#     # We normalize by a small factor so momentum matters at percent level.
#     # weights
#     w_sent = 0.8
#     w_mom = 20.0   # scale momentum (which is a small fraction) to same range
#     w_bias = 0.0   # bias term to shift overall LONG/SHORT baseline if desired

#     # Confidence dampening: higher volatility -> slightly reduce magnitude
#     vol_damp = 1.0 / (1.0 + s_vol * 50.0)  # s_vol ~0.01 => damp ~0.666 -> adjust as desired

#     raw = (w_sent * s_sent) + (w_mom * s_mom) + w_bias
#     raw *= vol_damp

#     prob_long = sigmoid(raw)  # between 0 and 1

#     decision = "LONG" if prob_long >= 0.5 else "SHORT"
#     confidence = abs(prob_long - 0.5)   # how far from 0.5 we are; used for selecting top 50

#     return {
#         "id": sid,
#         "prob_long": prob_long,
#         "decision": decision,
#         "confidence": confidence,
#         "raw_score": raw,
#         "features": {"sentiment": s_sent, "momentum": s_mom, "volatility": s_vol}
#     }

# @app.route("/trading-bot", methods=["POST"])
# def trading_bot():
#     """
#     Expect JSON array of ~1000 events; return 50 selected decisions.
#     """
#     data = request.get_json()
#     if not isinstance(data, list):
#         return jsonify({"error": "expected JSON array of events"}), 400

#     # Score all events
#     scored = []
#     for e in data:
#         try:
#             scored.append(score_event(e))
#         except Exception as ex:
#             # skip malformed event but keep going
#             continue

#     # Sort by confidence descending, pick top 50.
#     # If fewer than 50 events available, return all.
#     scored_sorted = sorted(scored, key=lambda x: x["confidence"], reverse=True)
#     topk = scored_sorted[:50]

#     # Build response with id + decision (uppercase)
#     out = [{"id": int(item["id"]), "decision": item["decision"]} for item in topk]

#     return jsonify(out), 200

# =========
# Config
# =========
TOP_K_DEFAULT = int(os.getenv("TOP_K", "50"))

WEIGHTS = {
    "sent": float(os.getenv("W_SENT", "1.2")),
    "mom": float(os.getenv("W_MOM", "0.8")),
    "ema": float(os.getenv("W_EMA", "0.4")),
    "gap": float(os.getenv("W_GAP", "0.25")),
}

EXTREME_THRESHOLDS = (
    float(os.getenv("THRESH_MILD", "1.2")),
    float(os.getenv("THRESH_MED", "1.8")),
    float(os.getenv("THRESH_EXTREME", "2.5")),
)

FADE_MULTIPLIERS = {
    "mild": float(os.getenv("FADE_MILD", "0.6")),
    "med": float(os.getenv("FADE_MED", "0.25")),
    "extreme": float(os.getenv("FADE_EXTREME", "-0.4")),
}

# =========
# Metrics (very simple counters)
# =========
METRICS = {
    "requests_total": 0,
    "bad_requests_total": 0,
    "items_seen_total": 0,
    "responses_returned_total": 0,
}

# =========
# Data types
# =========
@dataclass
class Candle:
    open: float
    high: float
    low: float
    close: float

def _sf(x: Any, default: float = 0.0) -> float:
    try:
        return float(x)
    except Exception:
        return default

def parse_candle(d: Dict[str, Any]) -> Candle | None:
    try:
        return Candle(
            open=_sf(d.get("open")),
            high=_sf(d.get("high")),
            low=_sf(d.get("low")),
            close=_sf(d.get("close")),
        )
    except Exception:
        return None

# =========
# Sentiment resources
# =========
BULLISH = {
    "surge", "soar", "rally", "bull", "bullish", "breakout", "record", "ath",
    "adopt", "adoption", "approve", "approved", "approval", "etf", "spot", "reserve",
    "treasury", "accumulate", "accumulation", "positive", "buy", "long", "launch",
    "listing", "support", "integrate", "integration", "partnership", "upgrade",
    "unveil", "investment", "institutional", "raises", "funding", "liquidity",
    "stimulus", "easing", "halving", "cut", "cuts", "rate", "rates", "qe",
    "backed", "strategic", "reserve", "accumulating", "allocates", "allocation",
    "greenlight", "okays", "approves", "builds", "buildout",
    # tokens for bitcoin
    "bitcoin", "btc", "sats", "sat"
}
BEARISH = {
    "dump", "plunge", "crash", "bear", "bearish", "sell", "selloff", "rug",
    "ban", "bans", "banned", "prohibit", "restrict", "lawsuit", "sue", "sues",
    "hack", "exploit", "breach", "outage", "insolvent", "insolvency", "bankrupt",
    "liquidation", "margin", "liquidated", "withdrawals", "paused", "delist",
    "delisting", "tightening", "hike", "hikes", "qt", "seize", "penalty", "fine",
    "criminal", "sanction", "tax", "probe", "investigation", "freeze", "frozen"
}
NEGATORS = {"no", "not", "never", "none", "without", "denies", "denied", "isn’t", "isnt", "wasn’t", "wasnt"}
EMOJI_BULL = {"🚀", "🟢", "📈", "🔥", "💎🙌", "✅", "🟩"}
EMOJI_BEAR = {"💀", "🟥", "📉", "❌", "⚠️", "🔻"}

RE_WORD = re.compile(r"[a-zA-Z][a-zA-Z\-']+|\$[A-Za-z]+|#[A-Za-z0-9_]+")
RE_BREAKING = re.compile(r"\b(BREAKING|URGENT|ALERT|JUST IN)\b", re.I)

def tokenize(text: str) -> List[str]:
    toks = RE_WORD.findall(text)
    # split hashtags like #BitcoinETF -> ["bitcoin", "etf"]
    out: List[str] = []
    for t in toks:
        if t.startswith("#"):
            clean = t[1:]
            # split camel or numeric tails
            parts = re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?=[A-Z]|$)|\d+", clean)
            out.extend([p.lower() for p in parts if p])
        elif t.startswith("$"):
            out.append(t[1:].lower())
        else:
            out.append(t.lower())
    return out

def emoji_sentiment(text: str) -> float:
    s = 0.0
    if any(e in text for e in EMOJI_BULL):
        s += 0.5
    if any(e in text for e in EMOJI_BEAR):
        s -= 0.5
    return s

def sentiment_score(title: str, source: str = "") -> Tuple[float, Dict[str, float]]:
    """
    Lexical sentiment with:
      - negation window (flips next 1-2 tokens)
      - caps/breaking boost
      - emoji weighting
      - source weighting (Twitter/realtime slight boost)
    Returns (score, components).
    """
    if not title:
        return 0.0, {"lex": 0.0, "caps": 0.0, "emoji": 0.0, "source": 0.0}

    toks = tokenize(title)
    score = 0.0
    negate_span = 0

    for t in toks:
        if t in NEGATORS:
            negate_span = 2  # next 2 tokens flipped
            continue
        hit = 0.0
        if t in BULLISH:
            hit = 1.0
        elif t in BEARISH:
            hit = -1.0
        if hit != 0.0:
            if negate_span > 0:
                hit *= -1.0
                negate_span -= 1
            score += hit
        elif negate_span > 0:
            # consume window even if token not a sentiment term
            negate_span -= 1

    s_caps = 0.0
    if RE_BREAKING.search(title):
        s_caps += 0.5
    if title.isupper() and len(title) > 12:
        s_caps += 0.25

    s_emoji = emoji_sentiment(title)

    s_src = 0.0
    s = (source or "").lower()
    if "twitter" in s or "x.com" in s or "tweet" in s:
        s_src += 0.25
    elif any(k in s for k in ("coindesk", "cointelegraph", "bloomberg", "reuters")):
        s_src += 0.15

    # clamp lex a bit and normalize overall to ≈[-1.2, 1.2]
    lex = max(-3.0, min(3.0, score))
    total = (lex + s_caps + s_emoji + s_src) / 2.5
    return total, {"lex": lex, "caps": s_caps, "emoji": s_emoji, "source": s_src}

# =========
# Price helpers
# =========
def atr(prev: List[Candle]) -> float:
    if not prev:
        return 1.0
    rng = [(max(0.0, c.high - c.low)) for c in prev]
    avg = sum(rng) / len(rng) if rng else 1.0
    return max(avg, 1e-6)

def momentum(prev: List[Candle], n: int = 3) -> float:
    if not prev:
        return 0.0
    closes = [c.close for c in prev[-n:]]
    if len(closes) < 2:
        return 0.0
    return (closes[-1] - closes[0]) / (len(closes) - 1)

def ema(values: List[float], alpha: float) -> float:
    if not values:
        return 0.0
    e = values[0]
    for v in values[1:]:
        e = alpha * v + (1 - alpha) * e
    return e

def ema_signal(prev: List[Candle]) -> float:
    closes = [c.close for c in prev]
    if len(closes) < 3:
        return 0.0
    fast = ema(closes[-6:] if len(closes) >= 6 else closes, 0.6)
    slow = ema(closes, 0.2)
    return fast - slow

def zsafe(x: float, d: float) -> float:
    return 0.0 if d <= 1e-9 else x / d

# =========
# Scoring
# =========
def score_item(item: Dict[str, Any]) -> Tuple[float, str, int, Dict[str, Any]]:
    """
    Returns (|score|, decision, id, debug_components)
    """
    iid = int(item.get("id", 0))
    title = str(item.get("title", "") or "")
    source = str(item.get("source", "") or "")

    prev_raw = item.get("previous_candles") or []
    obs_raw = item.get("observation_candles") or []

    prev = [parse_candle(c) for c in prev_raw if isinstance(c, dict)]
    prev = [c for c in prev if c is not None]
    obs = [parse_candle(c) for c in obs_raw if isinstance(c, dict)]
    obs = [c for c in obs if c is not None]

    if not prev or not obs:
        # missing data → very low-conviction default SHORT
        return 0.0, "SHORT", iid, {"reason": "insufficient_data"}

    entry = obs[0].close
    a = atr(prev)
    mom = momentum(prev)
    ema_sig = ema_signal(prev)
    last_prev_close = prev[-1].close
    gap = entry - last_prev_close

    sent, sent_parts = sentiment_score(title, source)

    mom_n = zsafe(mom, a)
    ema_n = zsafe(ema_sig, a)
    gap_n = zsafe(gap, a)

    # weighted blend
    score = (
        WEIGHTS["sent"] * sent +
        WEIGHTS["mom"] * mom_n +
        WEIGHTS["ema"] * ema_n +
        WEIGHTS["gap"] * gap_n
    )

    # fade extreme gaps
    t1, t2, t3 = EXTREME_THRESHOLDS
    if abs(gap_n) > t3:
        score *= FADE_MULTIPLIERS["extreme"]
        fade = "extreme"
    elif abs(gap_n) > t2:
        score *= FADE_MULTIPLIERS["med"]
        fade = "med"
    elif abs(gap_n) > t1:
        score *= FADE_MULTIPLIERS["mild"]
        fade = "mild"
    else:
        fade = "none"

    score = math.tanh(score)  # squash tiny noise

    decision = "LONG" if score > 0 else "SHORT"
    magnitude = abs(score)

    debug = {
        "entry": entry,
        "atr": a,
        "mom": mom, "ema_sig": ema_sig, "gap": gap,
        "mom_n": mom_n, "ema_n": ema_n, "gap_n": gap_n,
        "sent": sent, "sent_parts": sent_parts,
        "fade": fade,
        "raw_score_after_fade_squashed": score,
    }
    return magnitude, decision, iid, debug

def pick_top_k(items: List[Dict[str, Any]], k: int) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Returns (response_minimal, debug_list)
    """
    scored = [score_item(x) for x in items]
    # sort by |score| desc, then id asc (deterministic)
    scored.sort(key=lambda t: (-t[0], t[2]))
    picked = scored[: min(k, len(scored))]
    minimal = [{"id": iid, "decision": decision} for (_, decision, iid, _) in picked]
    debug = [{"id": iid, "decision": decision, "abs_score": abs_s, **dbg} for (abs_s, decision, iid, dbg) in picked]
    return minimal, debug

# =========
# HTTP
# =========
@app.route("/trading-bot", methods=["POST"])
def trading_bot():
    METRICS["requests_total"] += 1
    # stricter content-type helps Postman users avoid HTML/doctype issues
    if not request.content_type or "application/json" not in request.content_type.lower():
        METRICS["bad_requests_total"] += 1
        return jsonify({
            "error": "Content-Type must be application/json",
            "hint": "In Postman, set Headers → Content-Type: application/json"
        }), 415

    try:
        data = request.get_json(silent=False, force=False)
    except Exception as e:
        METRICS["bad_requests_total"] += 1
        return jsonify({"error": "Invalid JSON payload", "details": str(e)}), 400

    if not isinstance(data, list):
        METRICS["bad_requests_total"] += 1
        return jsonify({"error": "Request body must be a JSON array of news events."}), 400

    if len(data) == 0:
        return jsonify([]), 200

    # sanitize items & ensure IDs
    cleaned: List[Dict[str, Any]] = []
    for i, item in enumerate(data):
        if not isinstance(item, dict):
            continue
        if "id" not in item:
            item = dict(item)  # copy
            item["id"] = i + 1
        cleaned.append(item)

    METRICS["items_seen_total"] += len(cleaned)

    k = TOP_K_DEFAULT
    # hard requirement is 50, but allow explicit override for local testing via query string, e.g., /trading-bot?top_k=5
    top_k_param = request.args.get("top_k")
    if top_k_param:
        try:
            k = max(1, min(int(top_k_param), len(cleaned)))
        except Exception:
            pass

    minimal, debug = pick_top_k(cleaned, k)
    METRICS["responses_returned_total"] += len(minimal)

    # default: minimal per spec; debug only when requested
    if request.args.get("debug") in ("1", "true", "yes"):
        return jsonify({"results": minimal, "debug": debug}), 200
    return jsonify(minimal), 200


# Miscellaneous
@app.route("/")
def testing():
    return "Hello UBS Global Coding Challenge 2025 Singapore"

if __name__ == '__main__':
    app.run()
