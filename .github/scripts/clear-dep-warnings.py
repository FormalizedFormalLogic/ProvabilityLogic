#!/usr/bin/env python3
"""Drop Lake's cached diagnostics for a dependency's build directory.

Lake re-emits each module's cached log on every downstream build. Emptying the `log` array of each
`.trace` drops the replay and leaves the `.olean` untouched.
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
