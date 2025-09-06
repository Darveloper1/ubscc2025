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