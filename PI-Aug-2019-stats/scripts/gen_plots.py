import pandas as ps
import matplotlib.pyplot as plt
import sys
import os

def new_names(columns):
    result = []
    for c in columns:
        if "cvc4_2018" in c:
            result.append("cvc4_2018")
        elif "cvc4_2019" in c:
            result.append("cvc4_2019")
        elif "yices" in c:
            result.append("yices")
        elif "best" in c:
            result.append("best")
        else:
            result.append(c)
    return result

def to_int(x):
    try:
        result = int(x)
    except:
        if x == "-":
            return 0
        else:
            return x
    return result

def highlight_max(s):    
    is_max = s == s.max()
    print("panda", is_max)
    return ['background-color: red' if v else '' for v in is_max]

def gen_diff(d): 
    if "yices" in d.columns:
        return abs(data["cvc4_2019"] - data["yices"])
    else:
        return abs(data["cvc4_2019"] - data["cvc4_2018"]) 

assert(len(sys.argv) >= 3)
cluster_csv_dir = sys.argv[1]
destination_csv_dir = sys.argv[2]
for csv_file in os.listdir(cluster_csv_dir):
    data = ps.read_csv(cluster_csv_dir + "/" + csv_file)
    data = data.applymap(to_int)
    data.columns = new_names(data.columns)
    print("panda", data.columns)
    if "best" in data.columns:
        data.sort_values("best", inplace=True)
    data = data.tail(10)
    print(data)
    p = data.plot(kind='bar', x="DIRECTORY")
    f = p.get_figure()
    f.savefig('/home/yoniz/git/hermes/PI-Aug-2019-stats/plots/' + csv_file + '.png')
    data.style.apply(highlight_max)
    tab = data.style.render()
    with open('/home/yoniz/git/hermes/PI-Aug-2019-stats/tables/' + csv_file + '.html', 'w') as f:
        f.write(tab)

    
