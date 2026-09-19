# ProvabilityLogic Project Instructions

- Before committing or submitting PRs, read **`contribute/index.md`**.
- Before writing or refactoring proofs, read **`contribute/style.md`**.

## Setup

Proof work in this repository uses the `lean4` plugin (marketplace `lean4-skills`, providing `/lean4:autoprove` etc.) and the `lean-lsp` MCP server (defined in `.mcp.json`; requires `uv` and `ripgrep`). Enable both after cloning:

```
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4@lean4-skills
```

Bibliographic metadata and BibTeX for `references.bib` are fetched with the Zotero MCP server (`mcp__zotero__*`, configured at user scope).

This file is the project's only instruction file; no `CLAUDE.md` is checked in. Claude Code reads it through the built-in `agents-md` plugin, whose default mode steps in only for a project with no instruction file of its own — a `CLAUDE.md`, `.claude/CLAUDE.md` or `CLAUDE.local.md` anywhere from the filesystem root down to the working directory makes it stand down and leaves this file unread. Per-clone notes belong in `.claude/AGENTS.md`, which is git-ignored and read beside this file.
