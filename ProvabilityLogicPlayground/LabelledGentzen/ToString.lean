module

public import ProvabilityLogic.LabelledGentzen.GL.Search
meta import ProvabilityLogic.LabelledGentzen.GL.Basic
meta import ProvabilityLogic.LabelledGentzen.GL.Search
meta import LeanTypst.EvalTypst

/-! Display-only printers for `G3KGL` labelled sequents and proof-search traces. -/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace LabelledSequent

/-- Typst math-mode source for a labelled sequent given as list-representations of its
components (as with `LabelledSequent.ofLists`). Computable and thus usable with `#eval`. -/
def toStringOfLists [ToString α]
  (L : List LabelRel × List (LabelledFormula α) × List (LabelledFormula α)) : String :=
  let relParts := L.1.map (fun p => s!"{p.1} R {p.2}")
  let antParts := L.2.1.map LabelledFormula.toString
  let sucStr := String.intercalate ", " (L.2.2.map LabelledFormula.toString)
  s!"{String.intercalate ", " (relParts ++ antParts)} => {sucStr}"

end LabelledSequent


namespace LogicGL

/-- Curryst proof tree node for the proof search trace. -/
partial def searchTraceAux [ToString α] (processed : Finset (LabelledFormula α))
  (R : List LabelRel) (ℓΓ ℓΔ : List (LabelledFormula α)) : String :=
  let concl := LabelledSequent.toStringOfLists (R, ℓΓ, ℓΔ)
  match ℓΓ.find? (fun ℓA => decide (ℓA ∈ ℓΔ)) with
  | some _ => s!"rule(name: [Ax], ${concl}$)"
  | none =>
  match ℓΓ.find? (fun ℓA : LabelledFormula α => decide (ℓA.formula = (⊥ : Formula α))) with
  | some _ => s!"rule(name: [$bot$L], ${concl}$)"
  | none =>
  match R.find? (fun p => decide (p.1 = p.2)) with
  | some _ => s!"rule(name: [Irref], ${concl}$)"
  | none =>
  match impRTarget? ℓΓ ℓΔ with
  | some (x, A, B) =>
    s!"rule(name: [$->R$], \
      {searchTraceAux processed R ((x ∶ A) :: ℓΓ) ((x ∶ B) :: ℓΔ.erase (x ∶ A 🡒 B))}, ${concl}$)"
  | none =>
  match impLTarget? ℓΓ ℓΔ with
  | some (x, A, B) =>
    s!"rule(name: [$->L$], \
      {searchTraceAux processed R (ℓΓ.erase (x ∶ A 🡒 B)) ((x ∶ A) :: ℓΔ)}, \
      {searchTraceAux processed R ((x ∶ B) :: ℓΓ.erase (x ∶ A 🡒 B)) ℓΔ}, ${concl}$)"
  | none =>
  match boxLTarget? R ℓΓ with
  | some (_, y, A) =>
    s!"rule(name: [$class(\"unary\", square)L$], {searchTraceAux processed R ((y ∶ A) :: ℓΓ) ℓΔ}, ${concl}$)"
  | none =>
  match transTarget? R with
  | some (x, _, z) =>
    s!"rule(name: [Trans], {searchTraceAux processed ((x, z) :: R) ℓΓ ℓΔ}, ${concl}$)"
  | none =>
  match loopTarget? R ℓΓ ℓΔ with
  | some _ => s!"rule(name: [Loop], ${concl}$)"
  | none =>
  match lobTarget? processed R ℓΓ ℓΔ with
  | some (x, A) =>
    let y := (R.toFinset ⸴ ℓΓ.toFinset ⟹ˡ ℓΔ.toFinset).freshLabel;
    let preds := (R.filter (fun p => p.2 = x)).map Prod.fst;
    s!"rule(name: [$class(\"unary\", square)R^\"Löb\"$], \
      {searchTraceAux (insert (x ∶ □A) processed)
        (preds.map (fun w => (w, y)) ++ (x, y) :: R) ((y ∶ □A) :: ℓΓ)
        ((y ∶ A) :: ℓΔ.erase (x ∶ □A))}, ${concl}$)"
  | none => s!"rule(name: [$?$], ${concl}$)"

/-- Typst source rendering the proof-search trace as a `curryst` proof tree document. -/
def searchTrace0 [ToString α] (R : List LabelRel) (ℓΓ ℓΔ : List (LabelledFormula α)) : String :=
  s!"#import \"@preview/curryst:0.6.0\": rule, prooftree\n\n\
    #context prooftree(\n  {searchTraceAux ∅ R ℓΓ ℓΔ},\n  stroke: text.fill + 0.05em\n)"

/-- Decide whether `A` is a theorem of GL, displaying the proof-search trace or `⊬ A`. -/
def decideTrace0 [ToString α] (A : Formula α) : String :=
  match search0 (α := α) [] [] [0 ∶ A] with
  | some _ => searchTrace0 [] [] [0 ∶ A]
  | none => s!"$bold(upright(\"GL\")) tack.r.not {Formula.toString A}$"

#eval-typst decideTrace0 $ □(□#0 🡒 #0) 🡒 □#0
#eval-typst decideTrace0 $ □#0 🡒 #0

end LogicGL
