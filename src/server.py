from flask import Flask, request

from reasoning_graph import *

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

@app.route('/solve_graph', methods=['POST'])
def solve_reasoning_graph():
    graph = get_param("graph")
    solvers_to_disable = get_param("disable_solver")
    dreal_precision = get_param("dreal_precision")
    config = Config()
    config.disabled_solvers = solvers_to_disable
    config.dreal_precision = dreal_precision
    return process_graph_with_strings(graph, config)
#    return "Got it! %s %s %s" % (graph, solvers_to_disable, dreal_precision)


def get_param(param_name):
    """
    Safely get parameter from the request and return empty string if specified parameter doesn't exist
    """
    try:
        return request.values[param_name]
    except KeyError:
        return ""


def test_solve_graph():
    with app.test_client() as c:
        request_data = dict(graph="(this is my graph!)", disable_solver="dreal", dreal_precision="1")
        response = c.post("/solve_graph", data=request_data)
        print(response.data)

if __name__ == "__main__":
    test_solve_graph()
