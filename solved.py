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

## INK ARCHIVES

# ---------- Johnson's algorithm to enumerate elementary cycles ----------
def simple_cycles_johnson(n, edges):
    """
    Enumerate elementary (simple) cycles in directed graph with node IDs 0..n-1.
    edges: list of (u, v, rate) tuples. This returns cycles as lists of node indices
    where cycle[-1] == cycle[0].
    """
    G = defaultdict(list)
    for u, v, _ in edges:
        G[u].append(v)

    cycles = []

    blocked = set()
    B = defaultdict(set)
    stack = []

    def unblock(u):
        if u in blocked:
            blocked.remove(u)
            while B[u]:
                w = B[u].pop()
                unblock(w)

    def circuit(v, s):
        f = False
        blocked.add(v)
        stack.append(v)
        for w in G[v]:
            if w < s:
                continue
            if w == s:
                cycles.append(stack.copy() + [s])
                f = True
            elif w not in blocked:
                if circuit(w, s):
                    f = True
        if f:
            unblock(v)
        else:
            for w in G[v]:
                if w >= s:
                    B[w].add(v)
        stack.pop()
        return f

    # Main loop: consider subgraphs induced by nodes >= s
    for s in range(n):
        blocked.clear()
        B.clear()
        circuit(s, s)

    return cycles

# ---------- Best cycle selection (maximize geometric mean), with rotation ----------
def find_best_cycle(goods, ratios):
    """
    goods: list of names
    ratios: list of [u, v, rate]
    returns: {"path": [...], "gain": float}
    Behavior:
      - Enumerate all simple cycles.
      - For each cycle compute product and geometric mean (product**(1/num_trades)).
      - Pick the cycle with maximum geometric mean.
      - Rotate cycle so it starts at the node whose incoming edge in the cycle has the largest rate.
      - Return the path (names, with final element equal to the first) and gain = (product - 1) * 100.
    """
    n = len(goods)
    edges = [(int(u), int(v), float(r)) for u, v, r in ratios]

    if n == 0 or not edges:
        return {"path": [], "gain": 0.0}

    rate_map = {(u, v): r for u, v, r in edges}

    # Enumerate cycles
    cycles = simple_cycles_johnson(n, edges)
    if not cycles:
        # fallback: pick first direct round-trip if any
        u, v, r = edges[0]
        back = next((r2 for uu, vv, r2 in edges if uu == v and vv == u), 1.0)
        prod = r * back
        path = [goods[u], goods[v], goods[u]]
        return {"path": path, "gain": (prod - 1) * 100.0}

    best_cycle = None
    best_prod = 1.0
    best_geo = -float("inf")

    for cyc in cycles:
        # cyc is like [a, b, c, a]
        # compute product along edges
        prod = 1.0
        valid = True
        for i in range(len(cyc) - 1):
            u, v = cyc[i], cyc[i + 1]
            if (u, v) not in rate_map:
                valid = False
                break
            prod *= rate_map[(u, v)]
        if not valid:
            continue
        trades = len(cyc) - 1
        geo = prod ** (1.0 / trades)  # geometric mean per trade
        if geo > best_geo:
            best_geo = geo
            best_prod = prod
            best_cycle = cyc.copy()

    # If no valid cycle (unlikely), fallback
    if best_cycle is None:
        if edges:
            u, v, r = edges[0]
            back_rate = next((r2 for uu, vv, r2 in edges if uu == v and vv == u), 1.0)
            prod = r * back_rate
            return {"path": [goods[u], goods[v], goods[u]], "gain": (prod - 1) * 100.0}
        else:
            return {"path": [], "gain": 0.0}

    # Rotate chosen cycle so it starts at the node whose incoming edge has largest rate
    # incoming for node cyc[i+1] is edge cyc[i] -> cyc[i+1]
    trades = len(best_cycle) - 1
    # Build list of (node, incoming_rate, index_of_node_in_cycle)
    incoming = []
    for i in range(trades):
        u = best_cycle[i]
        v = best_cycle[i + 1]
        incoming.append((v, rate_map[(u, v)], i + 1))  # index where node v sits

    # pick the node (v) with largest incoming rate
    node_with_max_incoming = max(incoming, key=lambda x: x[1])
    start_pos = node_with_max_incoming[2] % trades  # convert to 0..trades-1

    # rotate: best_cycle is [n0,n1,...,n0]; we want to start at index=start_pos
    rotated = best_cycle[start_pos:trades] + best_cycle[0:start_pos+1]  # keep last==first
    if rotated[-1] != rotated[0]:
        rotated.append(rotated[0])

    path_names = [goods[i] for i in rotated]
    gain = (best_prod - 1.0) * 100.0

    return {"path": path_names, "gain": gain}

# ---------- Flask endpoint ----------
@app.route("/The-Ink-Archive", methods=["POST"])
def the_ink_archive():
    try:
        data = request.get_json(force=True)
        if not isinstance(data, list):
            return jsonify({"error": "expected a JSON array of datasets"}), 400

        results = []
        for dataset in data:
            goods = dataset.get("goods", [])
            ratios = dataset.get("ratios", [])
            # defensive defaults and casting handled inside find_best_cycle
            result = find_best_cycle(goods, ratios)
            # ensure types are JSON serializable
            if result["path"] is None:
                result["path"] = []
            result["gain"] = float(result["gain"])
            results.append(result)

        return jsonify(results)

    except Exception as e:
        # helpful for Render / production logs
        print("Error in /The-Ink-Archive:", str(e))
        return jsonify({"error": str(e)}), 500
    
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

@app.route("/", methods=["POST"])
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