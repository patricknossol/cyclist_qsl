import os

timeouts = [19, 20, 21, 22, 23, 24, 26, 30, 33, 35]

with open('./formulae', 'r') as file:
  i = 0
  for line in file:
    if i in timeouts:
      cores = f"{8*timeouts.index(i)}-{8*timeouts.index(i)+7}"
      os.system(f"screen -dmS {i} -L -Logfile {i}.log taskset -c {cores} qsl_prove -D ./qsl.defs -s -cputime -t 86400 -S \"{line.strip()}\"")
    else:
      os.system(f"taskset -c 80-87 qsl_prove -D ./qsl.defs -s -cputime -t 86400 -S \"{line.strip()}\" > {i}.log")
    i+=1
