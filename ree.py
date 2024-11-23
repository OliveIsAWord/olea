#!/bin/env python
from sys import stdin
import re

no_spans = re.compile(r'(Spanned \{ kind: |, span: [0-9]+\.\.[0-9]+ \})')

for line in stdin.readlines():
    line = no_spans.sub("", line)
    print(line, end='')
