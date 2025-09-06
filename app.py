from flask import Flask, render_template, request, jsonify, send_from_directory, Response
import math
import heapq
from typing import List, Tuple, Dict, Set
from collections import defaultdict

app = Flask(__name__)

# Challenge 1
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

#Challenge 2 (Ticketing Agent)
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

# Challenge 14 (Princess Diaries)
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

from flask import Flask, request, jsonify
from collections import defaultdict

from flask import Flask, request, jsonify
from collections import defaultdict

app = Flask(__name__)

@app.after_request
def _cors(r):
    r.headers["Access-Control-Allow-Origin"] = "*"
    r.headers["Access-Control-Allow-Methods"] = "POST, OPTIONS"
    r.headers["Access-Control-Allow-Headers"] = "Content-Type"
    return r

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

# Miscellaneous
@app.route("/")
def testing():
    return "Hello UBS Global Coding Challenge 2025 Singapore"


if __name__ == '__main__':
    app.run()
