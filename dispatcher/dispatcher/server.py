from flask import Flask, request, jsonify
from daas import VerificationTask, verify, LANG
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


@app.route('/ping', methods=['POST', 'GET'])
def ping():
    return 'Server is up and running...'


@app.route('/verify', methods=['POST'])
def solve_reasoning_graph():
    solver_input = request.get_json()
    solver_output = {"results": []}
    for query in solver_input["queries"]:
        additional_options = []
        if query["multiModels"]:
            additional_options = ["--block-models=values", "--incremental"]
        task = VerificationTask(query["id"], query["query"], LANG[query["lang"]], additional_options, ["normal"])
        task.timeout = solver_input["timeout"]
        result = verify(task)
        solver_output["results"].append(result)

    return json.dumps(solver_output, default=lambda o: o.__dict__)


if __name__ == '__main__':
    app.run(debug=True, use_reloader=False)
