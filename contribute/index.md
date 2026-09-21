# Contributing to ProvabilityLogic

How to contribute to this repository: getting a working build, the flow to `main`, PR/commit titles, pre-submission checks, and disclosure of AI involvement. For the coding conventions of the Lean sources, see [style.md](./style.md).

Items marked 🤖 are especially directed at AI coding agents.

## Getting started

After cloning, fetch the prebuilt artifacts before building anything:

```shell
just cache
```

That pulls three things: Mathlib's oleans from its own cache (`lake exe cache get`), Foundation's
from the build cache the organization shares, at the revision `lake-manifest.json` pins, and this
repository's own, at the newest ancestor of your `HEAD` that CI has published. Foundation is a Git
dependency with no Reservoir presence, so without this its ~1300 modules are elaborated from
source — a quarter of an hour on a CI runner, and the reason the pin is worth keeping on a
published revision.

A miss is not an error. `lake build` compiles whatever the cache did not supply, so a pin at an
unpublished revision, a branch of your own, or the odd module the cache is short of merely costs
time. Re-run `just cache` after a `lake update` or a rebase onto a newer `main`.

The store is an R2 bucket read anonymously over HTTPS from `ffl.sno2wman.net`; nothing needs
configuring, and only CI writes to it — this repository publishes its own outputs on pushes to
`main` alone, since a PR builds a tree that will not exist after the squash-merge.
[`lake-cache.toml`](../lake-cache.toml) at the repository root describes it and is the same file in
every FFL repository. The CI steps come from the composite actions in
[`FormalizedFormalLogic/.github`](https://github.com/FormalizedFormalLogic/.github/tree/main/lake-cache).

## How changes land on `main`

All changes to `main` go through GitHub pull requests. PRs are always squash-merged, so the PR title becomes the commit message on `main` — hence the title convention below.

## PR titles and commit convention

PR titles are in English, in the usual conventional-commit form:

```
<type>(scope): <subject>
```

`<type>` is one of the following (do not use `feat`):

| type | meaning |
| --- | --- |
| `add` | new results, definitions, theorems |
| `fix` | fixing something misformalized |
| `refactor` | renaming/organizing; existing facts essentially unchanged |
| `doc` | documents |
| `ci` | GitHub Actions |
| `chore` | other maintenance (e.g. version-up) |

`scope` is optional; specify the affected module (`Kripke`, `Gentzen`, `Logic/D`, …) if needed, following precedents in `git log --oneline`.

For `<subject>`, name one representative result of the PR; no verb phrases like "formalize the …" — write "Arithmetical completeness of D", not "formalize the arithmetical completeness of D".

PRs (title and body) are written in English. Commit messages — subject, body and trailers alike — are written in English as well.

## Before submitting

- The affected modules build with `lake build`, with no errors or warnings (including remaining `sorry`).
- The axiom audit passes:
  ```shell
  just forgive
  ```
  Every declaration under `ProvabilityLogic` may reach only the axioms `forgive.yml` accepts. A
  result taken on faith needs an entry there naming it, and so does everything that depends on
  one; conversely, proving such a result means deleting its entry and every mention of it. The
  audit reads the oleans, so build first. CI runs the same check.
- Run import-all to keep `ProvabilityLogic.lean` up to date:
  ```shell
  just mk-all
  ```
- If you added entries to `references.bib`, format it and regenerate the keys:
  ```shell
  just format-bib
  ```
  Keys follow the AMS (MathSciNet/MRef) convention (`Bek90`, `AB05`, `JdJ98`); do not hand-tune them, take whatever `just format-bib` produces. When a key changes, rename the corresponding PDF alongside it.
- 🤖 No development-time artifacts survive in the code — plan references, issue numbers, step numbers, stale skeleton-era comments. See [style.md](./style.md#stale-comments-and-planning-artifacts).

## Reference PDFs

PDFs of the papers being formalized live outside version control, named after their BibTeX key (`<key>.pdf` for the `<key>` entry). Adding a paper means adding its `references.bib` entry and naming the file after the generated key.

Unpublished or informal material (personal notes, blog posts, repository memos) is kept separately and does not go into `references.bib`.

## Disclosing AI involvement

🤖 Whenever an AI agent was involved in producing the changes — fully generated or merely assisted — this must be disclosed in the contribution itself:

- every commit created with an AI agent carries a co-author trailer, e.g.
  ```
  Co-Authored-By: Claude <noreply@anthropic.com>
  ```
- the PR states in natural language (in the body, or in the title if appropriate) that an AI agent was used.
