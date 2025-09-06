from flask import Flask, render_template, request, jsonify, send_from_directory, Response

app = Flask(__name__)

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


@app.route("/")
def testing():
    return "Hello World dar"

if __name__ == '__main__':
    app.run()