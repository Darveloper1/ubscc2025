from math import log
from flask import Flask, request, jsonify

app = Flask(__name__)

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


if __name__ == "__main__":
    # Run with: python app.py
    # Or set HOST/PORT via env if you deploy behind a reverse proxy
    app.run(host="0.0.0.0", port=8000, debug=False)
