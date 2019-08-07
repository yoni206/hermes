import pandas as ps
import matplotlib.pyplot as plt
import sys
import os

def to_int(x):
    try:
        result = int(x)
    except:
        return x
    return result

assert(len(sys.argv) >= 3)
cluster_csv_dir = sys.argv[1]
destination_csv_dir = sys.argv[2]
for csv_file in os.listdir(cluster_csv_dir):
    data = ps.read_csv(cluster_csv_dir + "/" + csv_file)
    data = data.applymap(to_int)
    #data.sort_values(data.columns[2], inplace=True)
    #print(data
    print(data.columns)
    p = data.plot(kind='bar', x="DIRECTORY")
    f = p.get_figure()
    f.savefig('/home/yoniz/git/hermes/PI-Aug-2019-stats/plots/' + csv_file + '.png')

