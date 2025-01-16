#!/bin/sh

eval $(opam env)
python3 benchmark.py
