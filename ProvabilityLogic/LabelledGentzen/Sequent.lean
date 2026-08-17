module

public import ProvabilityLogic.Formula.Basic

/-!
This file defines the labelled formula `x ∶ A` and the labelled sequent `R ⸴ Γ ⟹ˡ Δ`.
Every labelled sequent calculus in this repository (`GL`, `GL.3`) shares these types.

- [MPB23, §2.2]
-/

@[expose]
public section

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

/-- World-labels of the labelled sequent calculus. A bare `abbrev` for `ℕ`, kept
distinct so that arithmetic on `Formula`/proof-search data is not confused with
label bookkeeping. -/
abbrev Label := ℕ

/-- A relational atom `x R y` between two world-labels. -/
abbrev LabelRel := Label × Label

/-- A labelled formula `x : A`: the formula `A` tagged with the world-label `x`. -/
structure LabelledFormula (α : Type u) where
  label : Label
  formula : Formula α
deriving DecidableEq

infix:70 " ∶ " => LabelledFormula.mk

namespace LabelledFormula

/-- Typst math-mode source for a labelled formula `x : A`. -/
protected def toString [ToString α] (lf : LabelledFormula α) : String :=
  s!"{lf.label} : {Formula.toString lf.formula}"

instance [ToString α] : ToString (LabelledFormula α) := ⟨LabelledFormula.toString⟩

/-- Renaming a labelled formula: replace the label `y` by `z` wherever it occurs. -/
def relabel (y z : Label) (lf : LabelledFormula α) : LabelledFormula α := ⟨if lf.label = y then z else lf.label, lf.formula⟩

omit [DecidableEq α] in
@[simp] lemma relabel_label (y z : Label) (lf : LabelledFormula α) : (lf.relabel y z).label = if lf.label = y then z else lf.label := rfl

omit [DecidableEq α] in
@[simp] lemma relabel_formula (y z : Label) (lf : LabelledFormula α) : (lf.relabel y z).formula = lf.formula := rfl

end LabelledFormula

/-- A labelled sequent `R ⸴ Γ ⟹ˡ Δ`: `R` is a finite set of relational atoms
`x R y`, and `Γ`/`Δ` are finite sets of labelled formulas. -/
structure LabelledSequent (α : Type u) where
  rel : Finset LabelRel
  ant : Finset (LabelledFormula α)
  suc : Finset (LabelledFormula α)

notation:50 R:51 " ⸴ " Γ:51 " ⟹ˡ " Δ:51 => LabelledSequent.mk R Γ Δ

namespace LabelledSequent

variable {S : LabelledSequent α} {lf : LabelledFormula α} {p : LabelRel}

/-- Every world-label occurring in `S`, either in a labelled formula or in a relational atom. -/
@[grind]
def labels (S : LabelledSequent α) : Finset Label :=
  S.ant.image LabelledFormula.label ∪ S.suc.image LabelledFormula.label ∪ S.rel.image Prod.fst ∪ S.rel.image Prod.snd

/-- A label not occurring in `S`, for the eigenvariable condition of `R□^Löb`. -/
def freshLabel (S : LabelledSequent α) : Label := S.labels.sup id + 1

omit [DecidableEq α] in
lemma freshLabel_notMem : S.freshLabel ∉ S.labels := by
  intro h;
  have := Finset.le_sup (f := id) h;
  simp only [id, freshLabel] at this;
  exact Nat.not_succ_le_self _ this;

omit [DecidableEq α] in
@[grind =>]
lemma mem_labels_of_mem_ant (h : lf ∈ S.ant) : lf.label ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma mem_labels_of_mem_suc (h : lf ∈ S.suc) : lf.label ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma fst_mem_labels_of_mem_rel (h : p ∈ S.rel) : p.1 ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma snd_mem_labels_of_mem_rel (h : p ∈ S.rel) : p.2 ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

/-- Renaming a labelled sequent: replace the label `y` by `z` wherever it occurs, in the
relational atoms as well as in the antecedent and succedent formulas. -/
def relabel (y z : Label) (S : LabelledSequent α) : LabelledSequent α where
  rel := S.rel.image (fun p => (if p.1 = y then z else p.1, if p.2 = y then z else p.2))
  ant := S.ant.image (LabelledFormula.relabel y z)
  suc := S.suc.image (LabelledFormula.relabel y z)

end LabelledSequent

end LabelledGentzen

end
