#!/usr/bin/env python3
"""Move every dependency pin `lakefile.toml` names, and say what moved.

    scripts/bump-deps.py            # `just bump`

The toolchain is taken from UPSTREAM, since this library is built against it; a pin whose `rev`
is a version tag is moved onto the tag naming that toolchain, where its remote has published
one. Then the named requirements — and only those — are re-resolved: a bare `lake update` would
also drag the inherited dependencies, which follow branches, off the revisions Mathlib pins, and
a ProofWidgets disagreeing with Mathlib's makes `lake exe cache get` refuse to fetch its oleans.

Prints one Markdown list item per pin that moved, and nothing at all when none did.
"""

import json
import pathlib
import re
import subprocess
import sys
import tomllib
import urllib.request

# The library this one follows: its default branch decides the toolchain, and everything else is
# resolved against that.
UPSTREAM = "https://github.com/FormalizedFormalLogic/Foundation"
UPSTREAM_BRANCH = "master"

LAKEFILE = pathlib.Path("lakefile.toml")
MANIFEST = pathlib.Path("lake-manifest.json")
TOOLCHAIN = pathlib.Path("lean-toolchain")

# `v4.34.0`, `v4.35.0-rc1`: a release tag, as opposed to a branch or a bare revision.
VERSION_TAG = re.compile(r"^v\d+\.\d+\.\d+")


def required():
    """Every `[[require]]` in `lakefile.toml`, in the order it is written."""
    return tomllib.loads(LAKEFILE.read_text()).get("require", [])


def pins():
    """`{name: (revision, url)}` for everything the manifest currently resolves to."""
    packages = json.loads(MANIFEST.read_text())["packages"]
    return {p["name"]: (p["rev"], re.sub(r"\.git$", "", p["url"])) for p in packages}


def take_toolchain():
    """Adopt UPSTREAM's toolchain, before lake runs, so lake resolves under the one it targets."""
    url = f"{UPSTREAM.replace('github.com', 'raw.githubusercontent.com')}/{UPSTREAM_BRANCH}/lean-toolchain"
    with urllib.request.urlopen(url) as response:
        TOOLCHAIN.write_bytes(response.read())
    toolchain = TOOLCHAIN.read_text().strip()
    print(f"the toolchain is {toolchain}", file=sys.stderr)
    return toolchain.rsplit(":", 1)[-1]


def tagged(remote, tag):
    return subprocess.run(
        ["git", "ls-remote", "--exit-code", "--tags", remote, f"refs/tags/{tag}"],
        capture_output=True,
    ).returncode == 0


def follow_toolchain(tag):
    """Move each version-tag pin onto `tag`, where its remote has published one.

    Such a package is released per toolchain because it reads Lean's or Mathlib's internals, and
    a pin left behind at the previous tag would be resolved twice over against the one UPSTREAM
    requires. An unpublished tag leaves the pin alone: the pair is still coherent, and the next
    run picks the laggard up.
    """
    text = LAKEFILE.read_text()
    for require in required():
        name, rev, remote = require["name"], require.get("rev", ""), require.get("git")
        if not (VERSION_TAG.match(rev) and remote):
            continue
        if rev == tag:
            continue
        if not tagged(remote, tag):
            print(f"{name}: {remote} has no {tag} tag yet; its pin is left alone", file=sys.stderr)
            continue
        # The one `rev` that follows this `name`, before the next `[[require]] begins.
        text, moved = re.subn(
            rf'(name = "{re.escape(name)}"\n(?:[^\[\n][^\n]*\n)*?\s*rev = ")[^"]*(")',
            rf"\g<1>{tag}\g<2>",
            text,
        )
        if moved != 1:
            sys.exit(f"expected one {name} rev in {LAKEFILE}, rewrote {moved}")
        print(f"{name}: pinned at {tag}", file=sys.stderr)
    LAKEFILE.write_text(text)


def main():
    before = pins()
    follow_toolchain(take_toolchain())
    names = [require["name"] for require in required()]
    subprocess.run(["lake", "update", *names], check=True)

    for name in names:
        old, _ = before.get(name, (None, None))
        new, url = pins()[name]
        if old == new:
            continue
        moved = f"[`{old[:7]}` → `{new[:7]}`]({url}/compare/{old}...{new})" if old else f"`{new[:7]}` (new)"
        print(f"- `{name}` {moved}")


if __name__ == "__main__":
    main()
