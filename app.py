from flask import Flask, render_template, request, jsonify, send_from_directory, Response

app = Flask(__name__)

def calculate_points(customer, concert, priority):
    points - 0

    if customer.get("vip_status"):
        points += 100

    credit_card = customer.get("credit_card")
    if credit_card in priority and priority[credit_card] == concert["name"]:
        points += 50

    cx, cy = customer["location"]
    bx, by = concert["booking_center_location"]
    distance = math.sqrt((cx - bx) ** 2 + (cy - by) ** 2)
    latency_points = max(0, 30 - distance)  # simple linear scale
    points += latency_points

    return points

@app.route("/trivia", methods=["GET"])
def trivia():
    return {
        "answers": [
            4,
            1,
            2,
            2,
            3,
            4,
            2,
            5,
            5
        ]
    }


def ticketing_agent():
    data = request.get_json()

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



if __name__ == '__main__':
    app.run()