#!/usr/bin/env python3
"""Drop Lake's cached diagnostics for a dependency's build directory.

Lake stores each module's build diagnostics in its `.trace` file's `log` array and re-emits them
(`⚠ Replayed`) on every downstream build, so Foundation's own warnings — upstream's, not ours, and
not ours to fix — would spam every build here. Emptying each `.trace`'s `log` array drops the
replay and leaves the `.olean` untouched.
"""

import json
import pathlib
import sys

if len(sys.argv) != 2:
    sys.exit(f"usage: {sys.argv[0]} <build directory>")
root = pathlib.Path(sys.argv[1])
cleared = 0
for trace in root.rglob("*.trace"):
    try:
        cached = json.loads(trace.read_text())
    except (ValueError, OSError):
        continue
    if cached.get("log"):
        cached["log"] = []
        trace.write_text(json.dumps(cached))
        cleared += 1
print(f"cleared warning cache in {cleared} trace(s) under {root}")
