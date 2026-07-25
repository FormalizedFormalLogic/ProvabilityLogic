# Contributing to ProvabilityLogic

How to contribute to this repository: the flow to `main`, PR/commit titles, pre-submission checks, and disclosure of AI involvement. For the coding conventions of the Lean sources, see [style.md](./style.md).

Items marked 🤖 are especially directed at AI coding agents.

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
- Run import-all to keep `ProvabilityLogic.lean` up to date:
  ```shell
  just mk-all
  ```
- Remove unused imports and unnecessary `public`. `lake shake` needs a completed build, so run it after `lake build`, then build once more because it rewrites import lines:
  ```shell
  just shake
  lake build
  ```
  Watch for `meta import` lines: shake mistakes them for duplicates of the `public import` of the same module and deletes them. Annotate them with `-- shake: keep`, and if the build fails with `Invalid \`meta\` definition … consider adding \`public meta import …\``, restore the deleted line with that annotation.
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
