from flask import Flask, render_template, request, jsonify, send_from_directory, Response
import re
import math
import heapq
from typing import List, Tuple, Dict, Set
from collections import defaultdict, deque
from statistics import median
from itertools import chain
import string

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


# Universal Bureau of Surveillance
@app.route("/investigate", methods=["POST", "OPTIONS"], strict_slashes=False)
def investigate():
    if request.method == "OPTIONS":
        return ("", 204)

    payload = request.get_json(silent=True)
    if payload is None:
        return jsonify(error="Expected JSON body with Content-Type: application/json"), 400

    # Accept either {"networks":[...]} OR just [...]
    if isinstance(payload, dict):
        networks_in = payload.get("networks")
        if not isinstance(networks_in, list):
            return jsonify(error="Missing 'networks' key in object payload"), 400
    elif isinstance(payload, list):
        networks_in = payload
    else:
        return jsonify(error="Payload must be object with 'networks' or a list"), 400

    out = []

    for idx, item in enumerate(networks_in):
        if not isinstance(item, dict):
            return jsonify(error=f"networks[{idx}] must be an object"), 400

        net_id = item.get("networkId")
        edges_in = item.get("network")
        if not isinstance(edges_in, list):
            return jsonify(error=f"networks[{idx}].network must be a list"), 400
        if len(edges_in) == 0:
            # Guard so you don't silently return []
            out.append({"networkId": net_id, "extraChannels": []})
            continue

        # ---- Build undirected graph ----
        adj = defaultdict(list)       # node -> [(neighbor, edge_id)]
        edges_by_id = {}              # edge_id -> (u, v)
        for eid, e in enumerate(edges_in):
            if not isinstance(e, dict):
                return jsonify(error=f"networks[{idx}].network[{eid}] must be an object"), 400
            u, v = e.get("spy1"), e.get("spy2")
            if not isinstance(u, str) or not isinstance(v, str):
                return jsonify(error=f"networks[{idx}].network[{eid}] needs string spy1/spy2"), 400
            edges_by_id[eid] = (u, v)
            adj[u].append((v, eid))
            adj[v].append((u, eid))

        # ---- Tarjan bridges ----
        disc, low, time = {}, {}, [0]
        bridges = set()

        def dfs(u, peid=-1):
            disc[u] = low[u] = time[0]; time[0] += 1
            for v, eid in adj[u]:
                if eid == peid:
                    continue
                if v not in disc:
                    dfs(v, eid)
                    low[u] = min(low[u], low[v])
                    if low[v] > disc[u]:
                        bridges.add(eid)
                else:
                    low[u] = min(low[u], disc[v])

        for node in list(adj.keys()):
            if node not in disc:
                dfs(node)

        # Non-bridges = edges on cycles
        extra = [
            {"spy1": u, "spy2": v}
            for eid, (u, v) in edges_by_id.items()
            if eid not in bridges
        ]

        out.append({"networkId": net_id, "extraChannels": extra})

    return jsonify({"networks": out}), 200

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
    """
    Heuristic pipeline:
    - parse to floats
    - remove outliers (MAD)
    - compute convex hull of remaining points
    - return number of hull vertices as the 'hidden numeric parameter'
    (This is intentionally generic but robust for many puzzles where points form a simple polygon/shape.)
    """
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
        # fallback: use count of non-decoy points
        return len(filtered)
    hull = convex_hull(filtered)
    # numeric parameter: hull vertex count
    return len(hull)

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
    ctype = cipher_type.strip().upper()
    if ctype == "RAILFENCE":
        return rail_fence_decrypt(payload, rails=3)
    if ctype == "KEYWORD":
        # Keyword substitution using SHADOW
        return keyword_decrypt(payload, keyword="SHADOW")
    if ctype == "POLYBIUS":
        return polybius_decrypt(payload)
    if ctype in ("ROTATION_CIPHER", "ROT13", "ROT"):
        return rot13(payload)
    # fallback: attempt rot13, railfence, keyword
    attempt = rot13(payload)
    if all(ch.isalpha() or ch.isspace() for ch in attempt):
        return attempt
    attempt2 = rail_fence_decrypt(payload, rails=3)
    return attempt2

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
    result = {
        "challenge_one": None,
        "challenge_two": None,
        "challenge_three": None,
        "challenge_four": None
    }

    # --- Challenge 1 ---
    try:
        c1 = data.get("challenge_one", {})
        trans_str = c1.get("transformations", "")
        transformed_word = c1.get("transformed_encrypted_word", "")
        trans_list = parse_transformation_list(trans_str)
        recovered = reverse_transform(trans_list, transformed_word)
        result["challenge_one"] = recovered
    except Exception as e:
        result["challenge_one"] = f"ERROR: {str(e)}"

    # --- Challenge 2 ---
    try:
        c2 = data.get("challenge_two", [])
        numeric_param = analyze_coordinates(c2)
        result["challenge_two"] = numeric_param
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
                # try to infer if payload looks like rot13 (typical uppercase letters)
                decrypted_guess = rot13(encrypted_payload)
                result["challenge_three"] = decrypted_guess
            else:
                decrypted = decrypt_payload(cipher_type, encrypted_payload)
                result["challenge_three"] = decrypted
    except Exception as e:
        result["challenge_three"] = f"ERROR: {str(e)}"

    # --- Challenge 4 ---
    # Heuristic: if user supplied 'final_ciphertext' and optionally 'final_method', try to decrypt using recovered items:
    try:
        final_ct = data.get("final_ciphertext", None)
        final_method = data.get("final_method", "").upper() if data.get("final_method") else ""
        c1_val = result["challenge_one"]
        c2_val = result["challenge_two"]

        if final_ct:
            # try methods:
            final_plain = None
            # If user specified method, try it
            if final_method == "VIGENERE" and isinstance(c1_val, str):
                final_plain = vigenere_decrypt(final_ct, c1_val)
            elif final_method == "CAESAR" and isinstance(c2_val, int):
                final_plain = caesar_decrypt(final_ct, int(c2_val))
            else:
                # Try sensible combos:
                # 1) Vigenere using challenge_one as key
                if isinstance(c1_val, str):
                    try:
                        final_plain = vigenere_decrypt(final_ct, c1_val)
                    except Exception:
                        final_plain = None
                # 2) Caesar using challenge_two as shift
                if final_plain is None and isinstance(c2_val, int):
                    try:
                        final_plain = caesar_decrypt(final_ct, int(c2_val))
                    except Exception:
                        final_plain = None
                # 3) ROT13 fallback
                if final_plain is None:
                    final_plain = rot13(final_ct)
            result["challenge_four"] = final_plain
        else:
            result["challenge_four"] = {
                "note": "No final_ciphertext provided. Returning recovered components to use for final decryption.",
                "recovered_key_from_challenge_one": c1_val,
                "numeric_parameter_from_challenge_two": c2_val,
                "decrypted_payload_from_challenge_three": result["challenge_three"]
            }
    except Exception as e:
        result["challenge_four"] = f"ERROR: {str(e)}"

    return jsonify(result)


# Miscellaneous
@app.route("/")
def testing():
    return "Hello UBS Global Coding Challenge 2025 Singapore"

if __name__ == '__main__':
    app.run()
