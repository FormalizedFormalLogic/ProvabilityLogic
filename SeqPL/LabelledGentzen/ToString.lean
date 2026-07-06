module

public import SeqPL.LabelledGentzen.Search
meta import SeqPL.LabelledGentzen.Basic
meta import SeqPL.LabelledGentzen.Search

@[expose]
public section

/-!
Display-only printers for `G3KGL` labelled sequents and proof-search traces. None of
this is used by `SeqPL.LabelledGentzen.Basic`/`SeqPL.LabelledGentzen.Search`'s
mathematical content; it is kept in its own file so that those stay free of printing
concerns.
-/

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

namespace LabelledSequent

/-- Typst math-mode source for a labelled sequent given as list-representations of its
components (as with `LabelledSequent.ofLists`). Unlike `LabelledSequent.toString`, this is
computable and thus usable with `#eval`. -/
def toStringOfLists [ToString α]
  (L : List (Label × Label) × List (LabelledFormula α) × List (LabelledFormula α)) : String :=
  let relStr := String.intercalate ", " (L.1.map (fun p => s!"{p.1} R {p.2}"))
  let antStr := String.intercalate ", " (L.2.1.map LabelledFormula.toString)
  let sucStr := String.intercalate ", " (L.2.2.map LabelledFormula.toString)
  s!"{relStr}, {antStr} tack.r {sucStr}"

/-- Typst math-mode source for this sequent. Extracting the elements of a `Finset` is
noncomputable in general (it goes through `Multiset.toList`), so this is for
human-readable display (e.g. in the goal view) rather than `#eval`; use `toStringOfLists`
on the list-representations of `S`'s components for a computable, `#eval`-friendly variant. -/
protected noncomputable def toString [ToString α] (S : LabelledSequent α) : String :=
  toStringOfLists (S.rel.toList, S.ant.toList, S.suc.toList)

noncomputable instance [ToString α] : ToString (LabelledSequent α) := ⟨LabelledSequent.toString⟩

end LabelledSequent

/-! ### Curryst trace printer for the proof search

Printing the ambient sequent at each node of an already-built `⊢ˡ! S` proof term is
noncomputable (recovering the elements of `S`'s `Finset`s requires choice).
`saturate`/`search`/`searchLeaves`, however, manipulate the sequent as list-represented
components throughout, so mirroring their branching directly on those lists lets every
node of the trace show the full sequent via `LabelledSequent.toStringOfLists`.

`searchTraceAux`/`searchTrace0` are a display-only shadow of `saturate`/`search`/
`searchLeaves`: they select targets with the very same finder functions
(`impRTarget?`, `impLTarget?`, `boxLTarget?`, `transTarget?`, `loopTarget?`,
`lobTarget?`), so the shape of the trace matches what `search` actually derives, but
they make no correctness claim and do not touch `search`'s definition. Being `partial`
(totality is irrelevant for a printer) also lets a single recursive function inline the
leaf-handling that `searchLeaves` needs a batched `List` of leaves for, purely to satisfy
well-founded recursion. -/

/-- Curryst `rule(...)` call for the proof search starting from `(R, Γ, Δ)` with `processed`
already treated by `R□^Löb`, recursing into premises as nested `rule(...)` calls. See the
module docstring above this definition. -/
partial def searchTraceAux [ToString α] (processed : Finset (Formula α))
  (R : List (Label × Label)) (Γ Δ : List (LabelledFormula α)) : String :=
  let concl := LabelledSequent.toStringOfLists (R, Γ, Δ)
  match Γ.find? (fun lf => decide (lf ∈ Δ)) with
  | some _ => s!"rule(name: [Ax], ${concl}$)"
  | none =>
  match Γ.find? (fun lf : LabelledFormula α => decide (lf.formula = (⊥ : Formula α))) with
  | some _ => s!"rule(name: [$bot$L], ${concl}$)"
  | none =>
  match R.find? (fun p => decide (p.1 = p.2)) with
  | some _ => s!"rule(name: [Irref], ${concl}$)"
  | none =>
  match impRTarget? Γ Δ with
  | some (x, A, B) =>
    s!"rule(name: [$->R$], ${concl}$, {searchTraceAux processed R ((x ∶ A) :: Γ) ((x ∶ B) :: Δ)})"
  | none =>
  match impLTarget? Γ Δ with
  | some (x, A, B) =>
    s!"rule(name: [$->L$], ${concl}$, \
      {searchTraceAux processed R Γ ((x ∶ A) :: Δ)}, {searchTraceAux processed R ((x ∶ B) :: Γ) Δ})"
  | none =>
  match boxLTarget? R Γ with
  | some (_, y, A) =>
    s!"rule(name: [$class(\"unary\", square)L$], ${concl}$, {searchTraceAux processed R ((y ∶ A) :: Γ) Δ})"
  | none =>
  match transTarget? R with
  | some (x, _, z) =>
    s!"rule(name: [Trans], ${concl}$, {searchTraceAux processed ((x, z) :: R) Γ Δ})"
  | none =>
  match loopTarget? R Γ Δ with
  | some _ => s!"rule(name: [Loop], ${concl}$)"
  | none =>
  match lobTarget? processed Δ with
  | some (x, A) =>
    let y := (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).freshLabel;
    s!"rule(name: [$class(\"unary\", square)R^Löb$], ${concl}$, \
      {searchTraceAux (insert (□A) processed) ((x, y) :: R) ((y ∶ □A) :: Γ) ((y ∶ A) :: Δ)})"
  | none => s!"rule(name: [$?$], ${concl}$)"

/-- Typst source rendering the proof-search trace for `search0 R Γ Δ` as a `curryst`
proof tree; wrap the containing document with `#import "@preview/curryst:0.5.0": prooftree, rule`
for it to compile. Computable and thus `#eval`-friendly, and shows the full sequent at
every node. -/
def searchTrace0 [ToString α] (R : List (Label × Label)) (Γ Δ : List (LabelledFormula α)) : String :=
  s!"#prooftree(\n  {searchTraceAux ∅ R Γ Δ}\n)"

#eval LabelledSequent.toStringOfLists (α := ℕ) ([], [], [0 ∶ (□(□#0 🡒 #0) 🡒 □#0)])

#eval searchTrace0 (α := ℕ) [] [] [0 ∶ (□(□#0 🡒 #0) 🡒 □#0)]

end LabelledGentzen
