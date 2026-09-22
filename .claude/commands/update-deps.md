---
description: Move the dependency pins, make the build green, and open the bump
---

A dependency bump happens here, on this machine, start to finish: move the pins, build what the
move breaks, repair it, open the pull request. Nothing schedules this in CI. A runner has no
built dependency layer, and elaborating Foundation's ~1300 modules is most of what one would
spend its budget on; a machine that already has those oleans can see within minutes whether a
bump is safe. `ci.yml` only judges the pull request this produces.

`lakefile.toml` names two dependencies. **Foundation** follows `master`. **Forgive** follows the
tag naming our toolchain, which is Foundation's, and Foundation requires it by that same tag — a
pin left behind would be resolved twice over. Everything else, mathlib included, is inherited
from Foundation and moves when it does.

Read `contribute/index.md` before committing.

## 1. Look at what is already open

```shell
gh pr list --label update-deps --state open --json number,headRefName,url,labels
```

- **Labelled `want-human`.** A previous run gave up on that bump and a human has not answered
  yet. Go on anyway *only* if the pins below actually move: a new pin is a new problem, and you
  then take the label off. If they do not move, stop and say the bump is still waiting.
- **Open without that label.** Its branch is what you add to. Never rewrite it.
- **None.** The branch restarts from `main`.

## 2. Work where the build already exists

Rebuilding a dependency layer from nothing is the one cost worth going out of your way to avoid.
Use, in order of preference:

- the main checkout, when it is clean and on `main` — it has the `.lake` and needs no disk;
- otherwise a worktree under `.claude/worktrees/`, kept across bumps for the same reason.

Pull `main` (or the bump's branch) first. If you used the main tree, leave it back on
`main` when you are done, however the run ended: the next run tests for exactly that
before it will use it.

## 3. Move the pins

```shell
curl -fsSL https://raw.githubusercontent.com/FormalizedFormalLogic/Foundation/master/lean-toolchain -o lean-toolchain
```

Take the toolchain *before* lake runs, so lake resolves under the toolchain it is resolving for.
Then, if `FormalizedFormalLogic/forgive` has published the tag naming that toolchain
(`git ls-remote --tags`), set Forgive's `rev` in `lakefile.toml` to it; if it has not, leave the
pin alone and say so — the next run picks it up.

```shell
lake update Foundation Forgive
```

**By name, never bare.** A bare `lake update` upgrades *all* dependencies, and the inherited ones
follow branches (`proofwidgets: main`, `aesop: master`, …). It would drag them off the revisions
mathlib pins, and a ProofWidgets disagreeing with mathlib's makes `lake exe cache get` compute
wrong hashes and refuse to fetch mathlib's oleans.

If `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are all unchanged, there is no bump.
Stop, in one line.

## 4. Build it, and repair what the bump broke

```shell
just cache
lake build ProvabilityLogic
```

`just cache` first, always: it takes mathlib's oleans from its own cache and Foundation's from
the shared FFL store, at the revision the new manifest pins. A miss is not an error, but a
Foundation revision that has not been published yet is worth waiting a cycle out for rather than
elaborating by hand.

Read the compiler against the upstream's own diff over the range the pins moved — renames,
changed signatures, lemmas that moved. Where Foundation has absorbed material that used to live
here (`ProvabilityLogic/ToFoundation/` is where that material waits), Foundation's version wins:
delete the local copy, use Foundation's, and adapt every call site, leaving no wrapper behind.

Never write `sorry`, and change nothing outside `ProvabilityLogic/`, `forgive.yml` and the pin
files. `.github/`, `contribute/`, `README.md` and `AGENTS.md` are not what a bump breaks.

## 5. Verify everything CI verifies

```shell
lake build ProvabilityLogic     # no errors and no warnings
lake env leanchecker ProvabilityLogic
just forgive
just mk-all                     # leaves no diff
```

## 6. Open the bump

Commit with the `Co-Authored-By` trailer, on the `update-deps` branch, and push — **never
force-push** onto a branch that already carries a bump. Then open or refresh one pull request
labelled `update-deps`, titled `chore(deps): Update <what moved>`, whose body links the compare
range for each pin that moved and says the bump was made and verified locally by an agent.

- **The pins moved and nothing else had to change.** Queue the merge:
  `gh pr merge <number> --squash --auto`. CI has the last word.
- **The branch also carries a repair.** Do not queue it and do not merge it —
  `gh pr merge <number> --disable-auto` if it was queued for an earlier, cleaner bump. Say in the
  body what you had to change and why; a human confirms it.

If a `want-human` label survived from a previous bump, take it off now:
`gh pr edit <number> --remove-label want-human`.

## When you cannot make it green

Push the pin commit alone — never a half-repair, which the next run cannot tell from the pins —
open or refresh the pull request as above, and then

```shell
gh pr edit <number> --add-label want-human
gh pr comment <number> --body '...'
```

The comment names what broke, what you tried, and what a human has to decide. Do not open an
issue for it.
