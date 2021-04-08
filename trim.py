#!/usr/bin/python3
import sys

line = ""
while True:
    line = sys.stdin.readline()
    if not line:
        break
    if line.find('The following is the error trace for the error:') != -1:
        break

sys.stdout.write(line)
while True:
    line = sys.stdin.readline()
    if not line:
        break
    sys.stdout.write(line)
