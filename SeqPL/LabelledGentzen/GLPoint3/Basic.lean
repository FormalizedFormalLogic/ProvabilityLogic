module

public import SeqPL.LabelledGentzen.Basic

@[expose]
public section

/-!
Labelled sequent calculus for `LogicGLPoint3` (`GL.3`), obtained from the labelled
calculus `G3KGL` for `GL` (`SeqPL.LabelledGentzen.Basic`) by adding a structural
rule `Lin` for linearity (weak connectedness) of the accessibility relation:
given `x R y` and `x R z`, the successors `y` and `z` of a common world are
compared by branching into `y R z`, `y = z` (realised as a relabelling of `y`
to `z`), or `z R y`.
-/

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

namespace LabelledFormula

/-- Renaming a labelled formula: replace the label `y` by `z` wherever it occurs. -/
def relabel (y z : Label) (lf : LabelledFormula α) : LabelledFormula α := ⟨if lf.label = y then z else lf.label, lf.formula⟩

omit [DecidableEq α] in
@[simp] lemma relabel_label (y z : Label) (lf : LabelledFormula α) : (lf.relabel y z).label = if lf.label = y then z else lf.label := rfl

omit [DecidableEq α] in
@[simp] lemma relabel_formula (y z : Label) (lf : LabelledFormula α) : (lf.relabel y z).formula = lf.formula := rfl

end LabelledFormula

namespace LabelledSequent

/-- Renaming a labelled sequent: replace the label `y` by `z` wherever it occurs, in the
relational atoms as well as in the antecedent and succedent formulas. -/
def relabel (y z : Label) (S : LabelledSequent α) : LabelledSequent α where
  rel := S.rel.image (fun p => (if p.1 = y then z else p.1, if p.2 = y then z else p.2))
  ant := S.ant.image (LabelledFormula.relabel y z)
  suc := S.suc.image (LabelledFormula.relabel y z)

end LabelledSequent


namespace GLPoint3

inductive ProofLabelledGentzen : LabelledSequent α → Type u
| axm (x A) : ProofLabelledGentzen (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A})
| botL (x) : ProofLabelledGentzen (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α)))
| wkRel {R R' Γ Δ} : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ) → (_ : R ⊆ R' := by grind) → ProofLabelledGentzen (R' ⸴ Γ ⟹ˡ Δ)
| wkAnt {R Γ Γ' Δ} : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofLabelledGentzen (R ⸴ Γ' ⟹ˡ Δ)
| wkSuc {R Γ Δ Δ'} : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ')
| impL {R Γ Δ x A B} :
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ (insert (x ∶ A) Δ)) →
    ProofLabelledGentzen (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (R ⸴ (insert (x ∶ A 🡒 B) Γ) ⟹ˡ Δ)
| impR {R Γ Δ x A B} :
    ProofLabelledGentzen (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ)) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ (insert (x ∶ A 🡒 B) Δ))
/-- `L□`: uses an already available successor `y` of `x` (`x R y ∈ R`) to unfold `x : □A`. -/
| boxL {R Γ Δ} (x y A) (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ Γ := by grind) :
    ProofLabelledGentzen (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
/-- `R□^Löb`: introduces a fresh successor `y` of `x`, additionally assuming `y : □A` (the Löb trick). -/
| boxRLob {R Γ Δ} (x y A) (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels := by grind) :
    ProofLabelledGentzen (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ)
/-- `Irref`: a reflexive relational atom `x R x` closes any sequent. -/
| irref {R Γ Δ} (x) (h : (x, x) ∈ R := by grind) : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
/-- `Trans`: saturates `R` with the transitive consequence of `x R y` and `y R z`. -/
| trans {R Γ Δ} (x y z) (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) :
    ProofLabelledGentzen (insert (x, z) R ⸴ Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
/-- `Lin`: linearity (weak connectedness). Two successors `y`, `z` of a common world `x` are
compared by branching into `y R z`, `y = z` (realised by relabelling `y` to `z`), or `z R y`. -/
| lin {R Γ Δ} (x y z) (hxy : (x, y) ∈ R := by grind) (hxz : (x, z) ∈ R := by grind) :
    ProofLabelledGentzen (insert (y, z) R ⸴ Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (insert (z, y) R ⸴ Γ ⟹ˡ Δ) →
    ProofLabelledGentzen ((R ⸴ Γ ⟹ˡ Δ).relabel y z) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
prefix:120 "⊢ˡ³! " => ProofLabelledGentzen


abbrev ProvableLabelledGentzen (S : LabelledSequent α) : Prop := Nonempty (ProofLabelledGentzen S)
prefix:120 "⊢ˡ³ " => ProvableLabelledGentzen

end GLPoint3

end LabelledGentzen

end
