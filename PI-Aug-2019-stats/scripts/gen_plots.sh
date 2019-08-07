mkdir ~/scratch
sshfs yoniz@barrett1:/barrett/scratch/yoniz ~/scratch
scratch=~/scratch
cluster_csv_dir=$scratch/hermes/csv
python3 scripts/gen_plots.py $cluster_csv_dir csv
