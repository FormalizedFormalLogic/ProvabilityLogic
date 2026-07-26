# ProvabilityLogic Coding Style

Coding conventions for the formal proofs in this repository. The guiding principle: proofs are read and maintained by humans, so write them the way the human maintainers read them.

As a baseline, follow the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html) (line length, spacing, naming, calc/tactic formatting, etc.). This document only records what is specific to this project; where it differs from the Mathlib guide, this document takes precedence.

Human contributors need not follow this document to the letter — treat it as a description of the house style. 🤖 AI coding agents should follow it as closely as possible, especially the items marked 🤖: machine-generated proofs tend to drift toward a verbose, defensive style, and those items exist to counteract that drift.

## General conventions

- Omit type annotations that are trivially inferred. In particular, do not ascribe `(LogicGL : Logic α)` when the type of the formulas already determines `α`.
- Do not introduce implicit variables ad hoc in lemma statements. Declare them with `variable` in a `section`, and cut a new `section` when the context changes, rather than keeping one giant file-wide block.
- To fix the propositional-variable type of a logic, prefer writing the logic applied to its type — `@LogicGL α` — over ascribing a type to the formulas (`A : Formula α`).

## Proof style

Overall: construct terms directly when the type determines them, and hand the residue to automation — rather than opening holes in the goal and filling them one by one.

🤖 **Prefer direct term construction over `refine … ?_`.**

```lean
-- Avoid:
refine ⟨n, ?_, ?_⟩
· exact hn
· exact hn.le

-- Prefer:
exact ⟨n, hn, hn.le⟩
```

Reserve `refine` for components that genuinely need tactic work — and never write bound variables inside it:

```lean
-- Avoid:
refine ⟨hd, fun x hx => ?_⟩

-- Prefer:
refine ⟨hd, ?_⟩
intro x hx
```

**Prove existential goals with `use`, not `refine`.** Avoid leaving `?_` holes where `use` closes the goal directly.

**Split nested conjunctions with `and_intros`,** not `refine ⟨?_, ⟨?_, ?_⟩, ?_⟩` or repeated `constructor`.

**Use `obtain` when extracting witnesses from existential hypotheses** (`obtain ⟨n, hn⟩ := exists_bound f`), in preference to `rcases`/`rintro`. For other pattern decomposition, `rcases`/`rintro` are equally fine.

🤖 **Use `show` only when the goal unfolds non-trivially.** Restating a goal that is already displayed in the needed form is noise.

**Prefer term-mode pattern matching for structural inductions**, or `induction` with a `<;> simp`-style batch discharge:

```lean
theorem Even.add_two : Even n → Even (n + 2)
  | zero      => …
  | add_two h => …
```

When running an `induction`, try `grind` or `simp_all` on the trivial cases (base cases, plain recursive cases) before writing them out — they usually close.

🤖 **Lean on automation for the final assembly.** State the few needed facts as `have`s and pass them to a tactic (`grind`, `simp`) instead of hand-chaining compositions:

```lean
-- Prefer:
have h₁ : P ↔ Q := …
have h₂ : Q ↔ R := …
grind

-- Avoid:
exact step1.trans <| step2.trans <| step3.trans step4
```

🤖 **Keep proofs short; extract lemmas.** A tactic block beyond roughly thirty lines should be split: promote intermediate `have`s to stand-alone (possibly `private`) lemmas.

🤖 **Do not bundle lemmas into a `structure … : Prop` for convenience.** It is justified only when three or more properties must travel together as the hypothesis of a mutual or nested induction; otherwise state separate lemmas.

**When proving several equivalences at once with `List.TFAE`, do not refer to them by index** (`foo_TFAE.out 1 0`) from other proofs: the indices break as soon as the list is reordered. Cut the individual implications out as named lemmas instead.

### Trailing semicolons

Terminate each tactic line with a semicolon (`;`). This is a deliberate house convention of this repository; do not strip the semicolons in the course of an unrelated refactor.

## Naming intermediate steps

🤖 Name intermediate `have`s with short positional names (`h₁`, `h₂`, …) or conventional ones (`hp`, `ih`), and let the type annotation carry the meaning. Do not give every step a one-shot descriptive compound name — it duplicates the type and goes stale under refactoring. A descriptive name is warranted only when the fact is referred to several times.

```lean
-- Prefer:
have h₁ : a ≤ b := le_of_lt hab
have h₂ : b ≤ c := hbc.le
exact h₁.trans h₂

-- Avoid:
have ha_le_b_of_lt  : a ≤ b := le_of_lt hab
have hb_le_c_weaken : b ≤ c := hbc.le
exact ha_le_b_of_lt.trans hb_le_c_weaken
```

## Variable naming

Modal logic:

| kind | letters |
| --- | --- |
| propositional variables | `a`, `b`, `c`, … |
| formulas | `A`, `B`, `C`, `D`, … |
| lists / finite sets of formulas | `Γ`, `Δ` |
| sets of formulas | `X`, `Y`, `Z` |

Never use Greek letters (`φ`, `ψ`) or late-alphabet capitals (`P`, `Q`) for modal formulas — those namespaces are taken. Within a proof, introduce formulas in order (`A`, `B`, `C`), without skipping letters.

First-order logic:

| kind | letters |
| --- | --- |
| formulas | `φ`, `ψ`, `χ` |
| sentences | `σ`, `π` |

Sequents (`Γ ⟹ Δ` and similar, e.g. `TwoLayeredSequent`) are named `S`, `S'`, `S₁`, … . Do not rename this to `Sq` or similar to dodge a perceived clash with a logic named `S` (as in `LogicS`): the proof-calculus notation always encloses the logic name in brackets (`⊢ʰ[GL]`, `⊢ᵍ[GLPoint3]`, `⊢ᵍ[S]`), so a bare variable `S` never collides with it.

Kripke semantics: worlds are `x`, `y`, `z`, `w`, `v`, `u`. When building one model out of another, index the new model by `Model.World` rather than reintroducing a `κ : Type u`.

Membership in a logic is stated as `provable_*` (e.g. `provable_axiomD`), not `mem_*`.

## Signature indentation

When a declaration signature spans several lines, indent the first level of continuation by **two spaces** from the declaration keyword (`lemma`/`theorem`/`def`). This applies to the branches of a `↔`/`→` broken across lines, to binders placed on their own lines, and to a `: …` result line. The only exception is a single binder (or result type) that is itself too long: its inner continuation may be indented one further level.

```lean
-- Avoid (four-space, staircase indentation):
lemma foo_bar_indep {A : Baz α} (hA : A.Cond) :
    P (f a b) A ↔
      P (f a' b) A := by

-- Prefer:
lemma foo_bar_indep {A : Baz α} (hA : A.Cond) :
  P (f a b) A ↔
  P (f a' b) A := by

lemma exists_equiv_of_indep
  (hindep :
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFoo] (r : M.World) (o o' : α → Prop),
    Q (M, r, o) ↔ Q (M, r, o')
  )
  : ∃ C', Cond C' ∧ Rel C C' ∧ C'.small ⊆ C.small := by
```

## Comments and docstrings

All comments and docstrings are written in English.

🤖 Keep comments minimal. A docstring explains only what the statement says — not the proof strategy. Do not annotate individual `have`s with comments restating them. An inline comment is justified only for what the code cannot express (an elaboration pitfall, why a natural alternative fails), in about one line. Long "Implementation notes" sections are unwanted; if the design needs that much explanation, restructure the proof instead. A proof sketch inside the proof body is warranted only when it will genuinely help someone writing a neighbouring proof.

Module docstrings must be placed before `@[expose] public section`.

### Naming imported from the literature

Write the names used in this repository, not the notation of the source paper. For instance `GLαω` is `LogicA` here, `GLα X` is `LogicGLAlpha X`, `GLβ⁻ X` is `LogicGLBetaMinus X`, and `GLLin`/`GLlin`/`K4.3W` is `LogicGLPoint3`. Customary abbreviations (`GL`, `D`, `S`, `A`, `TBB`) need no translation. The one exception is the docstring of the definition itself, which may record where the alternative name comes from ("also known as `GLLin` or `K4.3W` in Sambin–Valentini").

### References and citations

When a definition or theorem formalizes a result from the literature, add the source to [references.bib](../references.bib) (formatted with bibtool, see [index.md](./index.md)) and cite it in the docstring, so a reader can find the informal counterpart.

Citations go at the end of the docstring as a list, one line per BibTeX key, of the form `- [key, kind number]` — even for a single citation. Do not embed them in running text, write `**Corollary 41(i) in [AB05]**:`, or spell out author names, years, titles and journals. Several results from the same key stay on one line:

```
- [AB05, Corollary 42]
- [VS83, Theorem 10, Theorem 11(b), Theorem 11(c)]
```

If you find a bare year or author name in a docstring, look the work up in `references.bib` and replace it with the key. If no entry corresponds, leave it as plain prose without brackets.

🤖 **For proofs submitted by AI agents, citations are mandatory**: every non-trivial definition and theorem must point to its source in the literature. If none exists (folklore, a routine technical bridge, original to this formalization), the docstring must say so and briefly explain why — never silently omit it.

### Stale comments and planning artifacts

🤖 Code and docstrings must not reference development-time artifacts: plan steps ("see plan Step4 §3"), issue numbers, bare step numbers, section/line labels (`§2`, `L4-1`), or the implementation status of another file ("even while Step 2 is incomplete…"). Fine as working memos, but remove or rewrite them into self-contained explanations before submission. `grep -n "see plan\|issue #\|Step [0-9]\|§[0-9]\|L[0-9]-[0-9]"` helps find survivors; note that `§` inside a citation list entry is legitimate.

🤖 Likewise remove skeleton-era comments (e.g. "most lemmas below are stated with `sorry`") that contradict the finished code.

## The `grind` tactic

Attach `@[grind]` to lemmas and definitions that plausibly help `grind` close goals, choosing a direction (`@[grind =>]`, `@[grind .]`) where it matters. 🤖 Do not attach it mechanically to every declaration. The post-hoc form `attribute [grind] name₁ name₂ …` is also acceptable. Inside proofs, try `grind` before settling on a longer tactic sequence.

## `set_option`

Whenever you use `set_option` (including the single-declaration form `set_option foo false in`), always add a comment explaining the intent: which option is changed, why, and for which declaration. The comment must make clear to a later reader that the option change is deliberate, not a workaround left behind by accident. For example, when suppressing a linter warning:

```lean
-- Intentionally kept as a global simp lemma; scoping it would break implicit uses elsewhere.
set_option warning.simp.varHead false in
@[simp] lemma eq_zero : n = 0 := by cases n; omega
```

**`set_option maxHeartbeats` must not be used actively.** 🤖 In particular, do not raise it to push a proof through — needing it is a sign the proof is in an inefficient form. If a proof only works that way, refactor until the option is unnecessary: extract lemmas, narrow `grind`/`simp` sets, avoid computationally heavy definitions.

## The module system

Cross-file `scoped` notation requires `open scoped Ns` at the use site; a plain `open Ns` does not bring it into scope.

`lake shake --fix` mistakes a `meta import` line for a duplicate of the `public import` of the same module and deletes it, breaking the build. Annotate every `meta import` so shake leaves it alone:

```lean
meta import ProvabilityLogic.Foo -- shake: keep
```
