module

public import ProvabilityLogic.LabelledGentzen.GL.Basic

/-!
Labelled sequent calculus for `LogicGLPoint3`, extending the calculus for `GL`
with the linearity rule `Lin`. Original to this formalization, applying the method of
[Neg14] — read a frame condition off as a structural rule — to weak connectedness.

- [Neg14, §5]
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace LogicGLPoint3

inductive ProofLabelledGentzen : LabelledSequent α → Type u
| axm (x A) : ProofLabelledGentzen (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A})
| botL (x) : ProofLabelledGentzen (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α)))
| wkRel {R R' ℓΓ ℓΔ} : ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ) → (_ : R ⊆ R' := by grind) → ProofLabelledGentzen (R' ⸴ ℓΓ ⟹ˡ ℓΔ)
| wkAnt {R ℓΓ ℓΓ' ℓΔ} : ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ) → (_ : ℓΓ ⊆ ℓΓ' := by grind) → ProofLabelledGentzen (R ⸴ ℓΓ' ⟹ˡ ℓΔ)
| wkSuc {R ℓΓ ℓΔ ℓΔ'} : ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ) → (_ : ℓΔ ⊆ ℓΔ' := by grind) → ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ')
| impL {R ℓΓ ℓΔ x A B} :
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A) ℓΔ)) →
    ProofLabelledGentzen (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ) →
    ProofLabelledGentzen (R ⸴ (insert (x ∶ A 🡒 B) ℓΓ) ⟹ˡ ℓΔ)
| impR {R ℓΓ ℓΔ x A B} :
    ProofLabelledGentzen (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ (insert (x ∶ B) ℓΔ)) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A 🡒 B) ℓΔ))
| boxL {R ℓΓ ℓΔ} (x y A) (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ ℓΓ := by grind) :
    ProofLabelledGentzen (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ)
| boxRLob {R ℓΓ ℓΔ} (x y A) (hfresh : y ∉ (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ).labels := by grind) :
    ProofLabelledGentzen (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ)
| irref {R ℓΓ ℓΔ} (x) (h : (x, x) ∈ R := by grind) : ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ)
| trans {R ℓΓ ℓΔ} (x y z) (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) :
    ProofLabelledGentzen (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ)
| lin {R ℓΓ ℓΔ} (x y z) (hxy : (x, y) ∈ R := by grind) (hxz : (x, z) ∈ R := by grind) :
    ProofLabelledGentzen (insert (y, z) R ⸴ ℓΓ ⟹ˡ ℓΔ) →
    ProofLabelledGentzen (insert (z, y) R ⸴ ℓΓ ⟹ˡ ℓΔ) →
    ProofLabelledGentzen ((R ⸴ ℓΓ ⟹ˡ ℓΔ).relabel y z) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ)
notation:120 "⊢ˡᵍ[GLPoint3]! " S:121 => ProofLabelledGentzen S


abbrev ProvableLabelledGentzen (S : LabelledSequent α) : Prop := Nonempty (ProofLabelledGentzen S)
notation:120 "⊢ˡᵍ[GLPoint3] " S:121 => ProvableLabelledGentzen S

notation:120 "⊬ˡᵍ[GLPoint3] " S:121 => ¬ ProvableLabelledGentzen S

end LogicGLPoint3

end
