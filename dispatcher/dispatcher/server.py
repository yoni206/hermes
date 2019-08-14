from flask import Flask, request, jsonify
from daas import VerificationTask, verify
import json

app = Flask(__name__)

def shutdown_server():
    func = request.environ.get('werkzeug.server.shutdown')
    if func is None:
        raise RuntimeError('Not running with the Werkzeug Server')
    func()


@app.route('/shutdown', methods=['POST', 'GET'])
def shutdown():
    shutdown_server()
    return 'Server shutting down...'


@app.route('/verify', methods=['POST'])
def solve_reasoning_graph():
    solver_input = request.get_json()
    solver_output = {"results": []}
    for query in solver_input["queries"]:
        task = VerificationTask(query["id"], query["query"], query["lang"], "")
        result = verify(task)
        solver_output["results"].append(result)
        print(query["id"] + ": " + result.result)

    return json.dumps(solver_output, default=lambda o: o.__dict__)

app.run(debug=True)
