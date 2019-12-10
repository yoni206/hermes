from flask import Flask, request

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
    input = request.get_json()
    print(input.queries)
    return ""

app.run(debug=True)
