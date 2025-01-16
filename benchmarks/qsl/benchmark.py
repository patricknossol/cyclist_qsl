import os

with open('./formulae', 'r') as file:
  i = 0
  for line in file:
    os.system(f"screen -dmS {i} -L -Logfile {i}.log qsl_prove -D ./qsl.defs -s -t 86400 -S \"{line.strip()}\" > {i}.log")
    i+=1
