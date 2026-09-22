---
description: Pick up the automated dependency bump and make it green
---

Handle the automated dependency pin bump. `.github/workflows/update-deps.yml` keeps one branch,
`update-deps`, behind one pull request labelled `update-deps`, whose body tabulates the revisions
it moved. It moves the pins and nothing else, and a bump that breaks nothing merges itself, so a
bump still open in front of you is one whose build this repository has to be repaired for.

Nothing repairs it in CI: a runner has no built dependency layer and would spend its whole budget
elaborating one. The repair happens here, locally, against an existing build.

Read `contribute/index.md` before committing anything.

## When to stop without acting

Stop immediately, reporting nothing but the reason, when

- there is no open pull request labelled `update-deps`;
- it carries the `want-human` label — a previous session already gave up on this bump, and the
  next bump takes the label off again;
- its checks are still running, or have not started;
- its checks are green. A green bump either merges itself or, once it carries a repair, is a
  human's to confirm; either way it is not yours. Say which of the two it is.

## Repairing a red bump

1. Find it and read why it is red:
   ```shell
   gh pr list --label update-deps --state open --json number,headRefName,url,labels
   gh pr checks <number>
   gh run view <run-id> --log-failed
   ```
   The log is where a failure that is not a compile error shows up — `just mk-all` leaving a diff,
   the axiom audit, `leanchecker`.

2. Work in a worktree under `.claude/worktrees/`, and keep the same one across bumps: it holds a
   built `.lake`, and rebuilding that from nothing is the one cost worth avoiding here. Pull the
   branch first — the workflow commits newer pins on top of it, so a local copy may be behind.

3. Fill the build from the caches before building anything:
   ```shell
   just cache
   ```
   That takes Mathlib's oleans from its own cache and Foundation's from the shared FFL store, at
   the revision the bumped manifest pins. Without it Foundation's ~1300 modules are elaborated
   from source, which is hours. A miss is not an error, but a bump whose Foundation revision has
   not been published yet is worth waiting a run out for rather than compiling by hand.

4. Build, and repair this repository against the upstream's own diff over the range the pull
   request body links — renames, changed signatures, lemmas that moved. Where Foundation has
   absorbed material that used to live here (`ProvabilityLogic/ToFoundation/` is where that
   material waits), Foundation's version wins: delete the local copy, use Foundation's, and adapt
   every call site, leaving no wrapper behind.

   Never write `sorry`, and change nothing outside `ProvabilityLogic/`, `ProvabilityLogicPlayground/`,
   `forgive.yml` and the pin files — `.github/`, `contribute/`, `README.md` and `AGENTS.md` are
   not what a dependency bump breaks.

5. Verify exactly what CI verifies, all of it:
   ```shell
   lake build ProvabilityLogic     # no errors and no warnings
   lake env leanchecker ProvabilityLogic
   just forgive
   just mk-all                     # leaves no diff
   ```

6. Commit with the `Co-Authored-By` trailer `contribute/index.md` asks for, and push to the same
   branch. **Never force-push**: the workflow adds the next bump's commits on top of yours. Then
   turn auto-merge off, since the branch is no longer pins-only and the repair is for a human to
   confirm:
   ```shell
   gh pr merge <number> --disable-auto
   ```
   Do not merge it yourself.

## When you cannot get it green

Commit nothing. Leaving a half-repair on the branch is worse than leaving the bump red: the next
session inherits it and cannot tell it from the pins. Instead label the pull request and say why:

```shell
gh pr edit <number> --add-label want-human
gh pr comment <number> --body '...'
```

The comment names what broke, what you tried, and what a human has to decide — a missing result,
an upstream change that needs mathematics this repository does not have. Do not open an issue for
it. The next bump takes the label off and restarts the cycle.
