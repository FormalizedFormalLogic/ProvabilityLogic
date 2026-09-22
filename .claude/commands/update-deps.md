---
description: Move the dependency pins, make the build green, and open the bump
---

A bump happens here, not in CI. A runner has no built dependency layer, so it would elaborate
the whole of upstream before it could say whether the bump is safe — and when it is not, the
repair belongs on a machine that has those oleans anyway. `ci.yml` only confirms what this
produces.

`just bump` moves the pins and prints what moved. `just check` runs what CI runs. Yours is the
part neither can do: making the build green again. Read `contribute/index.md` before committing.

## 1. Look at what is open

```shell
gh pr list --label update-deps --state open --json number,headRefName,labels
```

`want-human` on it means an earlier run gave up and nobody has answered yet. Go on only if the
pins actually move this time; otherwise stop and say the bump is still waiting.

An open bump's branch is what you add to — never rewrite it. With none open, `update-deps`
restarts from `main`.

## 2. Work where the build already exists

The main tree, when it is clean and on `main`; otherwise a worktree under `.claude/worktrees/`,
kept across bumps rather than made fresh. Leave the main tree back on `main` whichever way the
run ends — the next run tests for that before it will use it.

## 3. Bump

```shell
just bump
```

It prints one line per pin that moved, and nothing when none did. Nothing means no bump: stop,
in one line.

## 4. Make it green

```shell
just cache
just check
```

`just cache` before building, always: it is the difference between minutes and hours.

Read the compiler against the upstream diffs `just bump` printed — renames, changed signatures,
lemmas that moved. Where upstream has absorbed material that used to live here, upstream's
version wins: delete the local copy, use theirs, and adapt every call site, leaving no wrapper
behind.

Never write `sorry`, and change nothing outside `ProvabilityLogic/`, `forgive.yml` and the files
`just bump` touched.

## 5. Open it

Commit with the `Co-Authored-By` trailer, push to `update-deps` — **never force-push** — and open
or refresh one pull request labelled `update-deps`, titled `chore(deps): …`, whose body is what
`just bump` printed. Take a stale `want-human` back off.

- **The pins moved and nothing else had to.** `gh pr merge <n> --squash --auto`; CI has the last
  word.
- **It also carries a repair.** Leave it for a human — `--disable-auto` if an earlier, cleaner
  bump had queued it — and say in the body what you changed and why.

## When you cannot make it green

Push the pins alone. Never a half-repair: the next run cannot tell one from a bump. Open the
pull request as above, label it `want-human`, and comment what broke, what you tried, and what a
human has to decide. Do not open an issue.
