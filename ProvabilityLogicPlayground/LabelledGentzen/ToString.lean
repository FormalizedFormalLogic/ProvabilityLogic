module

public import ProvabilityLogic.LabelledGentzen.Search
meta import ProvabilityLogic.LabelledGentzen.Basic
meta import ProvabilityLogic.LabelledGentzen.Search
meta import LeanTypst.EvalTypst

@[expose]
public section

/-!
Display-only printers for `G3KGL` labelled sequents and proof-search traces. None of
this is used by `ProvabilityLogic.LabelledGentzen.Basic`/`ProvabilityLogic.LabelledGentzen.Search`'s
mathematical content; it is kept in its own file so that those stay free of printing
concerns.
-/

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

namespace LabelledSequent

/-- Typst math-mode source for a labelled sequent given as list-representations of its
components (as with `LabelledSequent.ofLists`). Computable and thus usable with `#eval`. -/
def toStringOfLists [ToString α]
  (L : List LabelRel × List (LabelledFormula α) × List (LabelledFormula α)) : String :=
  let relParts := L.1.map (fun p => s!"{p.1} R {p.2}")
  let antParts := L.2.1.map LabelledFormula.toString
  let sucStr := String.intercalate ", " (L.2.2.map LabelledFormula.toString)
  -- Join the relation atoms and antecedent formulas into a single comma-separated list
  -- (rather than each being joined separately and then concatenated with a hardcoded comma),
  -- so an empty relation or antecedent contributes no stray `, ` — likewise an empty succedent
  -- just renders as nothing after `=>`.
  s!"{String.intercalate ", " (relParts ++ antParts)} => {sucStr}"

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
partial def searchTraceAux [ToString α] (processed : Finset (LabelledFormula α))
  (R : List LabelRel) (Γ Δ : List (LabelledFormula α)) : String :=
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
    -- Drop the just-decomposed `x ∶ A 🡒 B` from the displayed premise's Δ: `search`/`saturate`
    -- keep it (a G3-style calculus doesn't need to consume it), but showing the very formula
    -- being introduced by this `->R` still sitting in its own premise is confusing to read.
    s!"rule(name: [$->R$], \
      {searchTraceAux processed R ((x ∶ A) :: Γ) ((x ∶ B) :: Δ.erase (x ∶ A 🡒 B))}, ${concl}$)"
  | none =>
  match impLTarget? Γ Δ with
  | some (x, A, B) =>
    s!"rule(name: [$->L$], \
      {searchTraceAux processed R (Γ.erase (x ∶ A 🡒 B)) ((x ∶ A) :: Δ)}, \
      {searchTraceAux processed R ((x ∶ B) :: Γ.erase (x ∶ A 🡒 B)) Δ}, ${concl}$)"
  | none =>
  match boxLTarget? R Γ with
  | some (_, y, A) =>
    s!"rule(name: [$class(\"unary\", square)L$], {searchTraceAux processed R ((y ∶ A) :: Γ) Δ}, ${concl}$)"
  | none =>
  match transTarget? R with
  | some (x, _, z) =>
    s!"rule(name: [Trans], {searchTraceAux processed ((x, z) :: R) Γ Δ}, ${concl}$)"
  | none =>
  match loopTarget? R Γ Δ with
  | some _ => s!"rule(name: [Loop], ${concl}$)"
  | none =>
  match lobTarget? processed R Γ Δ with
  | some (x, A) =>
    let y := (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).freshLabel;
    let preds := (R.filter (fun p => p.2 = x)).map Prod.fst;
    -- Like `->R`, drop the just-processed `x ∶ □A` from the displayed premise's Δ: once
    -- inserted into `processed`, `lobTarget?` never selects it again (regardless of whether
    -- it still sits in Δ), so leaving it in only clutters every descendant sequent below.
    s!"rule(name: [$class(\"unary\", square)R^\"Löb\"$], \
      {searchTraceAux (insert (x ∶ □A) processed)
        (preds.map (fun w => (w, y)) ++ (x, y) :: R) ((y ∶ □A) :: Γ)
        ((y ∶ A) :: Δ.erase (x ∶ □A))}, ${concl}$)"
  | none => s!"rule(name: [$?$], ${concl}$)"

/-- Typst source rendering the proof-search trace for `search0 R Γ Δ` as a standalone
`curryst` proof tree document (self-contained, including the `#import` `rule`/`prooftree`
needed to compile). Computable and thus `#eval`/`#eval-typst`-friendly, and shows the full
sequent at every node. -/
def searchTrace0 [ToString α] (R : List LabelRel) (Γ Δ : List (LabelledFormula α)) : String :=
  -- Draw the tree's bars via `#context .. stroke: text.fill` so they follow the infoview's
  -- current theme color instead of a fixed black that can be hard to see against a dark
  -- background.
  s!"#import \"@preview/curryst:0.6.0\": rule, prooftree\n\n\
    #context prooftree(\n  {searchTraceAux ∅ R Γ Δ},\n  stroke: text.fill + 0.05em\n)"

/-- Decide whether `A` is a theorem of `GL` — equivalently, whether the labelled sequent
`⟹ˡ 0 ∶ A` is `⊢ˡ`-provable — by running `search0`, which is decidable and complete
(`isSome_search0_iff_provableLabelledGentzen`). Displays the resulting proof-search trace
as a rendered `curryst` proof tree (like `searchTrace0`) when `A` is provable, or `⊬ A`
otherwise. -/
def decideTrace0 [ToString α] (A : Formula α) : String :=
  match search0 (α := α) [] [] [0 ∶ A] with
  | some _ => searchTrace0 [] [] [0 ∶ A]
  | none => s!"$bold(upright(\"GL\")) tack.r.not {Formula.toString A}$"

#eval-typst decideTrace0 $ □(□#0 🡒 #0) 🡒 □#0
#eval-typst decideTrace0 $ □#0 🡒 #0

end LabelledGentzen
