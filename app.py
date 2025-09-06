from flask import Flask, render_template, request, jsonify, send_from_directory, Response
import math
import heapq
from typing import List, Tuple, Dict, Set

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
    Using interval scheduling dynamic programming.
    """
    # Build the subway graph
    graph = build_graph(subway)
    
    # Get all unique stations we need
    stations = {starting_station}
    for task in tasks:
        stations.add(task['station'])
    
    # Compute all pairwise distances between relevant stations
    distances = compute_all_distances(graph, stations)
    
    # Sort tasks by end time for interval scheduling DP
    n = len(tasks)
    tasks_with_idx = [(i, task) for i, task in enumerate(tasks)]
    tasks_with_idx.sort(key=lambda x: x[1]['end'])
    
    # Create mapping from original index to sorted index
    sorted_to_original = [t[0] for t in tasks_with_idx]
    original_to_sorted = {orig: sort for sort, orig in enumerate(sorted_to_original)}
    
    # Find previous compatible task for each task (last task that doesn't overlap)
    prev_compatible = [-1] * n
    for i in range(n):
        for j in range(i - 1, -1, -1):
            if tasks_with_idx[j][1]['end'] <= tasks_with_idx[i][1]['start']:
                prev_compatible[i] = j
                break
    
    # DP arrays
    # dp[i] = (max_score, min_fee, selected_task_indices) for tasks 0..i
    dp = [(0, 0, [])] * (n + 1)
    
    for i in range(n):
        curr_task = tasks_with_idx[i][1]
        
        # Option 1: Don't take current task
        option1_score = dp[i][0]
        option1_fee = dp[i][1]
        option1_tasks = dp[i][2]
        
        # Option 2: Take current task
        prev_idx = prev_compatible[i]
        if prev_idx == -1:
            # First task in sequence
            prev_score = 0
            prev_fee = 0
            prev_tasks = []
            prev_station = starting_station
        else:
            prev_score = dp[prev_idx + 1][0]
            prev_fee = dp[prev_idx + 1][1]
            prev_tasks = dp[prev_idx + 1][2]
            prev_task = tasks_with_idx[prev_tasks[-1]][1] if prev_tasks else None
            prev_station = prev_task['station'] if prev_task else starting_station
        
        # Calculate fee for adding current task
        additional_fee = 0
        
        # If this is the first task or we're coming from a previous task
        if prev_station != curr_task['station']:
            if (prev_station, curr_task['station']) in distances:
                additional_fee = distances[(prev_station, curr_task['station'])]
            else:
                # Can't reach this station
                dp[i + 1] = (option1_score, option1_fee, option1_tasks)
                continue
        
        option2_score = prev_score + curr_task['score']
        option2_fee = prev_fee + additional_fee
        option2_tasks = prev_tasks + [i]
        
        # Choose better option
        if option2_score > option1_score or (option2_score == option1_score and option2_fee < option1_fee):
            dp[i + 1] = (option2_score, option2_fee, option2_tasks)
        else:
            dp[i + 1] = (option1_score, option1_fee, option1_tasks)
    
    # Get the best solution
    best_score, _, best_task_indices = dp[n]
    
    # Now calculate the actual minimum fee including return to start
    if not best_task_indices:
        return {
            'max_score': 0,
            'min_fee': 0,
            'schedule': []
        }
    
    # Calculate total fee with return journey
    total_fee = 0
    
    # From start to first task
    first_task = tasks_with_idx[best_task_indices[0]][1]
    if (starting_station, first_task['station']) in distances:
        total_fee += distances[(starting_station, first_task['station'])]
    
    # Between consecutive tasks
    for i in range(len(best_task_indices) - 1):
        task1 = tasks_with_idx[best_task_indices[i]][1]
        task2 = tasks_with_idx[best_task_indices[i + 1]][1]
        if task1['station'] != task2['station']:
            if (task1['station'], task2['station']) in distances:
                total_fee += distances[(task1['station'], task2['station'])]
    
    # From last task back to start
    last_task = tasks_with_idx[best_task_indices[-1]][1]
    if (last_task['station'], starting_station) in distances:
        total_fee += distances[(last_task['station'], starting_station)]
    
    # Get task names in chronological order
    selected_tasks = [tasks_with_idx[i][1] for i in best_task_indices]
    selected_tasks.sort(key=lambda x: x['start'])
    schedule = [task['name'] for task in selected_tasks]
    
    return {
        'max_score': best_score,
        'min_fee': total_fee,
        'schedule': schedule
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





# Miscellaneous
@app.route("/")
def testing():
    return "Hello UBS Global Coding Challenge 2025 Singapore"

@app.route("/health", methods=["GET"])
def health():
    """Health check endpoint."""
    return jsonify({'status': 'healthy'})

if __name__ == '__main__':
    app.run()