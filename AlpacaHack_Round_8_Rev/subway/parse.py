#!/usr/bin/env python3

import re

with open("decompiled_167A.txt") as f:
    symbol_array = []
    code_lines = []
    for code in f.read().split(";"):
        code = code.replace("pContextDest->", "")
        code = code.replace("pContextSrc->", "")
        code = code.replace("\n", " ")
        code = re.sub(r"\s+", " ", code)
        code = code.strip()
        if not code:
            continue

        code_lines.append(code)

for code in code_lines:
    print(f"    {code}")
