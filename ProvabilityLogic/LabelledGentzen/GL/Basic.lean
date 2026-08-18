module

public import ProvabilityLogic.LabelledGentzen.Sequent
public import Mathlib.Combinatorics.Pigeonhole

/-!
Labelled sequent calculus `G3KGL` for `GL`, and the pigeonhole argument that makes a
sequent provable once its relational atoms chain more worlds than there are boxed
formulas available.

- [MPB23, §2.2, §6]
- [Neg14, Lemma 5.2, Theorem 5.5]
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace LogicGL

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
/-- `L□`: uses an already available successor `y` of `x` (`x R y ∈ R`) to unfold `x : □A`. -/
| boxL {R ℓΓ ℓΔ} (x y A) (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ ℓΓ := by grind) :
    ProofLabelledGentzen (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ)
/-- `R□^Löb`: introduces a fresh successor `y` of `x`, additionally assuming `y : □A` (the Löb trick). -/
| boxRLob {R ℓΓ ℓΔ} (x y A) (hfresh : y ∉ (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ).labels := by grind) :
    ProofLabelledGentzen (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ)
/-- `Irref`: a reflexive relational atom `x R x` closes any sequent. -/
| irref {R ℓΓ ℓΔ} (x) (h : (x, x) ∈ R := by grind) : ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ)
/-- `Trans`: saturates `R` with the transitive consequence of `x R y` and `y R z`. -/
| trans {R ℓΓ ℓΔ} (x y z) (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) :
    ProofLabelledGentzen (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ) →
    ProofLabelledGentzen (R ⸴ ℓΓ ⟹ˡ ℓΔ)
notation:120 "⊢ˡᵍ[GL]! " S:121 => ProofLabelledGentzen S


namespace ProofLabelledGentzen

variable {R : Finset LabelRel} {ℓΓ ℓΔ : Finset (LabelledFormula α)} {x y : Label} {A B : Formula α}

def union (x A) (hΓ : (x ∶ A) ∈ ℓΓ := by grind) (hΔ : (x ∶ A) ∈ ℓΔ := by grind) : ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  wkSuc $ wkAnt $ wkRel (axm x A)

def botL_mem (x) (h : (x ∶ (⊥ : Formula α)) ∈ ℓΓ := by grind) : ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  wkSuc (ℓΔ := ∅) $ wkAnt $ wkRel (botL x)

def mdpL_mem (x A B) (h₁ : (x ∶ A 🡒 B) ∈ ℓΓ := by grind) (h₂ : (x ∶ A) ∈ ℓΓ := by grind) (h₃ : (x ∶ B) ∈ ℓΔ := by grind) : ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  rw [(show ℓΓ = insert (x ∶ A 🡒 B) (insert (x ∶ A) (ℓΓ \ {x ∶ A, x ∶ A 🡒 B})) by grind)];
  apply impL;
  . apply union x A;
  . apply union x B;

def negL : ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A) ℓΔ)) → ⊢ˡᵍ[GL]! (R ⸴ (insert (x ∶ ∼A) ℓΓ) ⟹ˡ ℓΔ) := λ p => impL p (wkSuc $ wkAnt $ wkRel (botL x))

def negR : ⊢ˡᵍ[GL]! (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ ℓΔ) → ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ ∼A) ℓΔ)) := λ p => impR $ wkSuc $ wkAnt p (by grind)

def andL : ⊢ˡᵍ[GL]! (R ⸴ (insert (x ∶ A) $ insert (x ∶ B) $ ℓΓ) ⟹ˡ ℓΔ) → ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A ⋏ B) ℓΓ ⟹ˡ ℓΔ) := λ p => by
  apply impL;
  . apply impR;
    apply negR;
    simpa [(show (insert (x ∶ A) $ insert (x ∶ B) ℓΓ) = (insert (x ∶ B) $ insert (x ∶ A) ℓΓ) by grind)] using p;
  . exact botL_mem x;

def andR : ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ) → ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ insert (x ∶ B) ℓΔ) → ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A ⋏ B) ℓΔ) := λ p q => by
  apply impR;
  apply impL;
  . exact wkSuc p;
  . exact negL $ wkSuc q;

def orL : ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A) ℓΓ ⟹ˡ ℓΔ) → ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ) → ⊢ˡᵍ[GL]! (R ⸴ insert (x ∶ A ⋎ B) ℓΓ ⟹ˡ ℓΔ) := λ p q => by
  apply impL;
  . exact negR p;
  . exact q;

def orR : ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A) $ insert (x ∶ B) ℓΔ)) → ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A ⋎ B) ℓΔ) := λ p => by
  apply impR;
  apply negL;
  simpa;

/--
A *looping* sequent, where the same boxed formula `□A` is attached
to the antecedent side of `x` and the succedent side of `y` for an accessibility atom
`x R y`, is derivable outright.

- [Neg14, Lemma 5.2]
-/
def loop (x y z : Label) (A : Formula α)
  (hz : z ∉ (R ⸴ ℓΓ ⟹ˡ ℓΔ).labels)
  (hR : (x, y) ∈ R := by grind)
  (hx : (x ∶ □A) ∈ ℓΓ := by grind)
  (hy : (y ∶ □A) ∈ ℓΔ := by grind) : ⊢ˡᵍ[GL]! (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  rw [(show ℓΔ = insert (y ∶ □A) (ℓΔ.erase (y ∶ □A)) by grind)];
  apply boxRLob y z A;
  apply trans x y z;
  apply boxL x z A;
  exact union z A;

end ProofLabelledGentzen


abbrev ProvableLabelledGentzen (S : LabelledSequent α) : Prop := Nonempty (ProofLabelledGentzen S)
notation:120 "⊢ˡᵍ[GL] " S:121 => ProvableLabelledGentzen S

notation:120 "⊬ˡᵍ[GL] " S:121 => ¬ ProvableLabelledGentzen S

namespace ProvableLabelledGentzen

variable {R R' : Finset LabelRel} {ℓΓ ℓΓ' ℓΔ ℓΔ' : Finset (LabelledFormula α)} {x y z : Label} {A B : Formula α}

lemma axm (x : Label) (A : Formula α) : ⊢ˡᵍ[GL] (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) := ⟨ProofLabelledGentzen.axm x A⟩
lemma union (x : Label) (A : Formula α) (hΓ : (x ∶ A) ∈ ℓΓ := by grind) (hΔ : (x ∶ A) ∈ ℓΔ := by grind) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.union x A hΓ hΔ⟩
lemma botL (x : Label) : ⊢ˡᵍ[GL] (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) := ⟨ProofLabelledGentzen.botL x⟩
@[grind =>] lemma botL_mem (x : Label) (h : (x ∶ (⊥ : Formula α)) ∈ ℓΓ := by grind) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.botL_mem x h⟩
lemma wkRel (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hR : R ⊆ R') : ⊢ˡᵍ[GL] (R' ⸴ ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.wkRel h.some hR⟩
lemma wkAnt (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hΓ : ℓΓ ⊆ ℓΓ') : ⊢ˡᵍ[GL] (R ⸴ ℓΓ' ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.wkAnt h.some hΓ⟩
lemma wkSuc (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hΔ : ℓΔ ⊆ ℓΔ') : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ') := ⟨ProofLabelledGentzen.wkSuc h.some hΔ⟩
lemma impL (h₁ : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ)) (h₂ : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ (insert (x ∶ A 🡒 B) ℓΓ) ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ˡᵍ[GL] (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ (insert (x ∶ B) ℓΔ))) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A 🡒 B) ℓΔ)) := ⟨ProofLabelledGentzen.impR h.some⟩
lemma boxL (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ ℓΓ := by grind) (h : ⊢ˡᵍ[GL] (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  ⟨ProofLabelledGentzen.boxL x y A hxy hxA h.some⟩
lemma boxRLob (hfresh : y ∉ (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ).labels := by grind)
    (h : ⊢ˡᵍ[GL] (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) :=
  ⟨ProofLabelledGentzen.boxRLob x y A hfresh h.some⟩
lemma irref (h : (x, x) ∈ R := by grind) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.irref x h⟩
lemma trans (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) (h : ⊢ˡᵍ[GL] (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  ⟨ProofLabelledGentzen.trans x y z hxy hyz h.some⟩

lemma negL (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ ∼A) ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.negL h.some⟩
lemma negR (h : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ A) ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ ∼A) ℓΔ) := ⟨ProofLabelledGentzen.negR h.some⟩
lemma andL (h : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ A) (insert (x ∶ B) ℓΓ) ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ A ⋏ B) ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.andL h.some⟩
lemma andR (h₁ : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ)) (h₂ : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ B) ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A ⋏ B) ℓΔ) := ⟨ProofLabelledGentzen.andR h₁.some h₂.some⟩
lemma orL (h₁ : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ A) ℓΓ ⟹ˡ ℓΔ)) (h₂ : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ A ⋎ B) ℓΓ ⟹ˡ ℓΔ) := ⟨ProofLabelledGentzen.orL h₁.some h₂.some⟩
lemma orR (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) (insert (x ∶ B) ℓΔ))) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A ⋎ B) ℓΔ) := ⟨ProofLabelledGentzen.orR h.some⟩

lemma loop (x y : Label) (A : Formula α) (hR : (x, y) ∈ R := by grind)
  (hx : (x ∶ □A) ∈ ℓΓ := by grind) (hy : (y ∶ □A) ∈ ℓΔ := by grind) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  ⟨ProofLabelledGentzen.loop x y (R ⸴ ℓΓ ⟹ˡ ℓΔ).freshLabel A LabelledSequent.freshLabel_notMem hR hx hy⟩

@[induction_eliminator]
lemma rec
  {motive : (S : LabelledSequent α) → ⊢ˡᵍ[GL] S → Prop}
  (axm : ∀ x A, motive (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) (ProvableLabelledGentzen.axm x A))
  (botL : ∀ x, motive (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) (ProvableLabelledGentzen.botL x))
  (wkRel : ∀ {R R' ℓΓ ℓΔ} (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h' : R ⊆ R'),
    motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R' ⸴ ℓΓ ⟹ˡ ℓΔ) (wkRel h h')
  )
  (wkAnt : ∀ {R ℓΓ ℓΓ' ℓΔ} (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h' : ℓΓ ⊆ ℓΓ'),
    motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ' ⟹ˡ ℓΔ) (wkAnt h h')
  )
  (wkSuc : ∀ {R ℓΓ ℓΔ ℓΔ'} (h : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (h' : ℓΔ ⊆ ℓΔ'),
    motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ ⟹ˡ ℓΔ') (wkSuc h h')
  )
  (impL : ∀ {R ℓΓ ℓΔ x A B} (h₁ : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ)) (h₂ : ⊢ˡᵍ[GL] (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ)),
    motive (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ) h₁ → motive (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ) h₂ →
    motive (R ⸴ (insert (x ∶ A 🡒 B) ℓΓ) ⟹ˡ ℓΔ) (impL h₁ h₂)
  )
  (impR : ∀ {R ℓΓ ℓΔ x A B} (h : ⊢ˡᵍ[GL] (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ (insert (x ∶ B) ℓΔ))),
    motive (R ⸴ (insert (x ∶ A) ℓΓ) ⟹ˡ (insert (x ∶ B) ℓΔ)) h → motive (R ⸴ ℓΓ ⟹ˡ (insert (x ∶ A 🡒 B) ℓΔ)) (impR h)
  )
  (boxL : ∀ {R ℓΓ ℓΔ x y A} (hxy : (x, y) ∈ R) (hxA : (x ∶ □A) ∈ ℓΓ) (h : ⊢ˡᵍ[GL] (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ)),
    motive (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) (boxL hxy hxA h)
  )
  (boxRLob : ∀ {R ℓΓ ℓΔ x y A} (hfresh : y ∉ (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ).labels)
      (h : ⊢ˡᵍ[GL] (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ)),
    motive (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ) h →
    motive (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) (boxRLob hfresh h)
  )
  (irref : ∀ {R ℓΓ ℓΔ x} (h : (x, x) ∈ R), motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) (irref h))
  (trans : ∀ {R ℓΓ ℓΔ x y z} (hxy : (x, y) ∈ R) (hyz : (y, z) ∈ R) (h : ⊢ˡᵍ[GL] (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ)),
    motive (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ) h → motive (R ⸴ ℓΓ ⟹ˡ ℓΔ) (trans hxy hyz h)
  )
  : ∀ {S : LabelledSequent α} (h : ⊢ˡᵍ[GL] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

lemma iff_unprovableLabelledGentzen_isEmpty_ProofLabelledGentzen {S : LabelledSequent α} :
  (⊬ˡᵍ[GL] S) ↔ (IsEmpty (⊢ˡᵍ[GL]! S)) := by simp [ProvableLabelledGentzen];

end ProvableLabelledGentzen


namespace ProvableLabelledGentzen

variable {R : Finset LabelRel} {ℓΓ ℓΔ : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

/-- If `y` is reachable from `x` through a nonempty chain of relational atoms in `R`,
then the relational atom `(x, y)` can be discharged by `Trans`. -/
lemma of_transGen_insert (h : Relation.TransGen (λ a b => (a, b) ∈ R) x y)
  : ⊢ˡᵍ[GL] (insert (x, y) R ⸴ ℓΓ ⟹ˡ ℓΔ) → ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  induction h with
  | single hxy =>
    simp [Finset.insert_eq_self.mpr hxy];
  | @tail b c _ hbc ih =>
    intro h;
    apply ih;
    apply trans (x := x) (y := b) (z := c);
    apply wkRel h;
    grind;

/--
Chain form of the looping lemma: a looping sequent is provable. If there is a nonempty
chain of relational atoms from `x` to `y`, and the same boxed formula `□A`
occurs at `x` in the antecedent and at `y` in the succedent, the sequent is provable.
The single-edge case is `ProvableLabelledGentzen.loop`.

- [Neg14, Lemma 5.2]
-/
lemma loopChain (h : Relation.TransGen (λ a b => (a, b) ∈ R) x y)
  (hx : (x ∶ □A) ∈ ℓΓ := by grind) (hy : (y ∶ □A) ∈ ℓΔ := by grind)
  : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  apply of_transGen_insert h;
  exact loop x y A;

/-- `ReflTransGen` variant of `loopChain`, additionally covering the degenerate case `x = y`. -/
lemma loopChain' (h : Relation.ReflTransGen (λ a b => (a, b) ∈ R) x y)
  (hx : (x ∶ □A) ∈ ℓΓ := by grind) (hy : (y ∶ □A) ∈ ℓΔ := by grind)
  : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | h;
  . exact union y (□A);
  . exact loopChain h hx hy;

omit [DecidableEq α] in
/-- A nonempty chain of relational atoms in `R` yields a `TransGen` step. -/
lemma transGen_of_isChain {l : List Label} (hl : l ≠ [])
  (hchain : (x :: l).IsChain (λ a b => (a, b) ∈ R))
  : Relation.TransGen (λ a b => (a, b) ∈ R) x (l.getLast hl) := by
  induction l generalizing x with
  | nil => grind
  | cons b l ih =>
    rcases List.isChain_cons_cons.mp hchain with ⟨hxb, hchain⟩;
    match l with
    | [] => exact Relation.TransGen.single hxb;
    | c :: l =>
      rw [List.getLast_cons (by grind)];
      exact Relation.TransGen.head hxb (ih (by grind) hchain);

/--
`List`-chain form of the looping lemma: `x R y₁, …, yₙ₋₁ R yₙ` with
`x ∶ □A` in the antecedent and `yₙ ∶ □A` in the succedent.

- [Neg14, Lemma 5.2]
-/
lemma loopChain_of_isChain {l : List Label} (hl : l ≠ [])
  (hchain : (x :: l).IsChain (λ a b => (a, b) ∈ R))
  (hx : (x ∶ □A) ∈ ℓΓ := by grind) (hy : ((l.getLast hl) ∶ □A) ∈ ℓΔ := by grind)
  : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) :=
  loopChain (transGen_of_isChain hl hchain) hx hy


section Pigeonhole

variable {n : ℕ} {xs : Fin (n + 1) → Label}

omit [DecidableEq α] in
/-- Any segment of a chain `xs 0 R xs 1 R … R xs n` yields a `ReflTransGen` step. -/
lemma reflTransGen_of_chain (hchain : ∀ i : Fin n, (xs i.castSucc, xs i.succ) ∈ R) (hab : a ≤ b)
  : Relation.ReflTransGen (λ u w => (u, w) ∈ R) (xs a) (xs b) := by
  induction b using Fin.induction with
  | zero =>
    grind;
  | succ i ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt;
    . exact Relation.ReflTransGen.refl;
    . exact Relation.ReflTransGen.tail (ih (by grind)) (hchain i);

/--
Pigeonhole core of the termination argument: suppose that along a chain
`xs 0 R xs 1 R … R xs n` each edge `i` is generated by a boxed formula `□(f i)`,
occurring in the succedent at its source `xs i` and in the antecedent at its
target `xs (i + 1)`, with all `f i` drawn from a finite stock `X`.
If the chain has more edges than `X` has elements, then some boxed formula
repeats along the chain and the sequent is provable.

- [Neg14, Theorem 5.5]
-/
theorem provable_of_long_chain {X : Finset (Formula α)} (hX : X.card < n)
  (hchain : ∀ i : Fin n, (xs i.castSucc, xs i.succ) ∈ R)
  {f : Fin n → Formula α} (hf : ∀ i, f i ∈ X)
  (hant : ∀ i : Fin n, ((xs i.succ) ∶ □(f i)) ∈ ℓΓ)
  (hsuc : ∀ i : Fin n, ((xs i.castSucc) ∶ □(f i)) ∈ ℓΔ)
  : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  -- pigeonhole: more edges than elements of `X` forces two edges `i ≠ j` with `f i = f j`;
  -- whichever of `i.succ`, `j.succ` comes first, `loopChain'` closes the sequent via the repeat
  obtain ⟨i, -, j, -, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin n))) (t := X) (by simpa using hX) (λ i _ => hf i);
  wlog hij : i < j;
  . exact this (i := j) (j := i) ‹_› ‹_› ‹_› ‹_› ‹_› (by grind) (by grind) (by omega);
  apply loopChain' (A := f i) (reflTransGen_of_chain hchain ?_) (hant i) (by rw [heq]; exact hsuc j);
  grind;

end Pigeonhole

end ProvableLabelledGentzen

end LogicGL

end
