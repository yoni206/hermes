CURRENT_DIR=$(pwd)
export LC_ALL=C.UTF-8
export LANG=C.UTF-8
export FLASK_APP=server.py

flask run -h 0.0.0.0 -p 5000