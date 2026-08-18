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

namespace ProvableLabelledGentzen

variable {R R' : Finset LabelRel} {ℓΓ ℓΓ' ℓΔ ℓΔ' : Finset (LabelledFormula α)} {x y z : Label} {A B : Formula α}

lemma axm (x : Label) (A : Formula α) : ⊢ˡᵍ[GLPoint3] (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) := ⟨ProofLabelledGentzen.axm x A⟩
lemma botL (x : Label) : ⊢ˡᵍ[GLPoint3] (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) := ⟨ProofLabelledGentzen.botL x⟩
lemma wkRel (h : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hR : R ⊆ R') : ⊢ˡᵍ[GLPoint3] (R' ⸴ ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.wkRel h.some hR⟩
lemma wkAnt (h : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hΓ : ℓΓ ⊆ ℓΓ') : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ' ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.wkAnt h.some hΓ⟩
lemma wkSuc (h : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hΔ : ℓΔ ⊆ ℓΔ') : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ') := ⟨ProofLabelledGentzen.wkSuc h.some hΔ⟩
lemma impL (h₁ : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ)) (h₂ : ⊢ˡᵍ[GLPoint3] (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GLPoint3] (R ⸴ (insert (x ∶ A 🡒 B) ℓΓ) ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ˡᵍ[GLPoint3] (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ (insert (x ∶ B) ℓΔ))) : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A 🡒 B) ℓΔ)) := ⟨ProofLabelledGentzen.impR h.some⟩
lemma boxL (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ ℓΓ := by grind) (h : ⊢ˡᵍ[GLPoint3] (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  ⟨ProofLabelledGentzen.boxL x y A hxy hxA h.some⟩
lemma boxRLob (hfresh : y ∉ (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ).labels := by grind)
  (h : ⊢ˡᵍ[GLPoint3] (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ)) : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) :=
  ⟨ProofLabelledGentzen.boxRLob x y A hfresh h.some⟩
lemma irref (h : (x, x) ∈ R := by grind) : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.irref x h⟩
lemma trans (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) (h : ⊢ˡᵍ[GLPoint3] (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  ⟨ProofLabelledGentzen.trans x y z hxy hyz h.some⟩
lemma lin (hxy : (x, y) ∈ R := by grind) (hxz : (x, z) ∈ R := by grind)
  (h₁ : ⊢ˡᵍ[GLPoint3] (insert (y, z) R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h₂ : ⊢ˡᵍ[GLPoint3] (insert (z, y) R ⸴ ℓΓ ⟹ˡ ℓΔ))
  (h₃ : ⊢ˡᵍ[GLPoint3] ((R ⸴ ℓΓ ⟹ˡ ℓΔ).relabel y z)) : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  ⟨ProofLabelledGentzen.lin x y z hxy hxz h₁.some h₂.some h₃.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : LabelledSequent α) → ⊢ˡᵍ[GLPoint3] S → Prop}
  (axm : ∀ x A, motive (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) (ProvableLabelledGentzen.axm x A))
  (botL : ∀ x, motive (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) (ProvableLabelledGentzen.botL x))
  (wkRel : ∀ {R R' ℓΓ ℓΔ} (h : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h' : R ⊆ R'),
    motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R' ⸴ ℓΓ ⟹ˡ ℓΔ) (wkRel h h')
  )
  (wkAnt : ∀ {R ℓΓ ℓΓ' ℓΔ} (h : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h' : ℓΓ ⊆ ℓΓ'),
    motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ' ⟹ˡ ℓΔ) (wkAnt h h')
  )
  (wkSuc : ∀ {R ℓΓ ℓΔ ℓΔ'} (h : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h' : ℓΔ ⊆ ℓΔ'),
    motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ ⟹ˡ ℓΔ') (wkSuc h h')
  )
  (impL : ∀ {R ℓΓ ℓΔ x A B} (h₁ : ⊢ˡᵍ[GLPoint3] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ)) (h₂ : ⊢ˡᵍ[GLPoint3] (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ)),
    motive (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ) h₁ → motive (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ) h₂ →
    motive (R ⸴ (insert (x ∶ A 🡒 B) ℓΓ) ⟹ˡ ℓΔ) (impL h₁ h₂)
  )
  (impR : ∀ {R ℓΓ ℓΔ x A B} (h : ⊢ˡᵍ[GLPoint3] (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ (insert (x ∶ B) ℓΔ))),
    motive (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ (insert (x ∶ B) ℓΔ)) h → motive (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A 🡒 B) ℓΔ)) (impR h)
  )
  (boxL : ∀ {R ℓΓ ℓΔ x y A} (hxy : (x, y) ∈ R) (hxA : (x ∶ □A) ∈ ℓΓ) (h : ⊢ˡᵍ[GLPoint3] (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ)),
    motive (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) (boxL hxy hxA h)
  )
  (boxRLob : ∀ {R ℓΓ ℓΔ x y A} (hfresh : y ∉ (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ).labels)
      (h : ⊢ˡᵍ[GLPoint3] (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ)),
    motive (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ) h →
    motive (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) (boxRLob hfresh h)
  )
  (irref : ∀ {R ℓΓ ℓΔ x} (h : (x, x) ∈ R), motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) (irref h))
  (trans : ∀ {R ℓΓ ℓΔ x y z} (hxy : (x, y) ∈ R) (hyz : (y, z) ∈ R) (h : ⊢ˡᵍ[GLPoint3] (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ)),
    motive (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) (trans hxy hyz h)
  )
  (lin : ∀ {R ℓΓ ℓΔ x y z} (hxy : (x, y) ∈ R) (hxz : (x, z) ∈ R)
      (h₁ : ⊢ˡᵍ[GLPoint3] (insert (y, z) R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h₂ : ⊢ˡᵍ[GLPoint3] (insert (z, y) R ⸴ ℓΓ ⟹ˡ ℓΔ))
      (h₃ : ⊢ˡᵍ[GLPoint3] ((R ⸴ ℓΓ ⟹ˡ ℓΔ).relabel y z)),
    motive (insert (y, z) R ⸴ ℓΓ ⟹ˡ ℓΔ) h₁ → motive (insert (z, y) R ⸴ ℓΓ ⟹ˡ ℓΔ) h₂ →
    motive ((R ⸴ ℓΓ ⟹ˡ ℓΔ).relabel y z) h₃ → motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) (lin hxy hxz h₁ h₂ h₃)
  )
  : ∀ {S : LabelledSequent α} (h : ⊢ˡᵍ[GLPoint3] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

end ProvableLabelledGentzen

end LogicGLPoint3

end
