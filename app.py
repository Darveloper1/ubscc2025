from flask import Flask, render_template, request, jsonify, send_from_directory, Response

app = Flask(__name__)

@app.route("/trivia", methods=["GET"])
def trivia():
    return {
        "answers": [
            1,
            1,
            1,
            1,
            1
        ]
    }


@app.route("/")
def testing():
    return "Hello World dar"

if __name__ == '__main__':
    app.run()