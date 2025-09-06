from flask import Flask, render_template, request, jsonify, send_from_directory, Response

app = Flask(__name__)

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
            3,
            5,
            4
        ]
    }


@app.route("/")
def testing():
    return "Hello UBS Global Coding Challenge 2025 Singapore"

if __name__ == '__main__':
    app.run()