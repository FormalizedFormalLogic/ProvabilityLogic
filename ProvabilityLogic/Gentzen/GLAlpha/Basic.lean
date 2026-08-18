module

public import ProvabilityLogic.Gentzen.GL.Basic
public import ProvabilityLogic.Gentzen.GL.WithCut

@[expose]
public section

open LogicGL

variable {α : Type u} [DecidableEq α]

inductive LogicGLAlpha.ProofGentzen (𝔸 : Set ℕ) : TwoLayeredSequent α → Type u
| axm (l) (A)      : ProofGentzen 𝔸 ({A} ⟹[l] {A})
| botL (l)         : ProofGentzen 𝔸 (({⊥} : FormulaFinset α) ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : ProofGentzen 𝔸 (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen 𝔸 (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : ProofGentzen 𝔸 (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen 𝔸 (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : ProofGentzen 𝔸 (Γ ⟹[l] (insert A Δ)) → ProofGentzen 𝔸 (insert B Γ ⟹[l] Δ) → ProofGentzen 𝔸 ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : ProofGentzen 𝔸 ((insert A Γ) ⟹[l] (insert B Δ)) → ProofGentzen 𝔸 (Γ ⟹[l] (insert (A 🡒 B) Δ))
| liftUp {Γ Δ}     : ProofGentzen 𝔸 (Γ ⟹[0] Δ) → ProofGentzen 𝔸 (Γ ⟹[1] Δ)
| boxGL {Γ A}      : ProofGentzen 𝔸 ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) → ProofGentzen 𝔸 (Γ.box ⟹[0] {□A})
| boxGP {Γ Δ n}    : n ∈ 𝔸 → ProofGentzen 𝔸 (Γ ⟹[1] insert (□^[n] ⊥) Δ) → ProofGentzen 𝔸 (Γ ⟹[1] Δ)

namespace LogicGLAlpha

scoped notation:120 "⊢ᵍ[GLAlpha " 𝔸 "]! " S => ProofGentzen 𝔸 S

abbrev ProvableGentzen (𝔸 : Set ℕ) (S : TwoLayeredSequent α) : Prop := Nonempty (⊢ᵍ[GLAlpha 𝔸]! S)
scoped notation:120 "⊢ᵍ[GLAlpha " 𝔸 "] " S => ProvableGentzen 𝔸 S

variable {𝔸 : Set ℕ}

/-- Embed a level-0 `LogicGL` proof into level-0 `LogicGLAlpha`. -/
def ofProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[GL]! (Γ ⟹ Δ) → ⊢ᵍ[GLAlpha 𝔸]! (Γ ⟹[0] Δ)
| .axm A    => .axm 0 A
| .botL     => .botL 0
| .wkL h h' => .wkL (ofProofGentzen h) h'
| .wkR h h' => .wkR (ofProofGentzen h) h'
| .impL h₁ h₂ => .impL (ofProofGentzen h₁) (ofProofGentzen h₂)
| .impR h   => .impR (ofProofGentzen h)
| .boxGL h  => .boxGL (ofProofGentzen h)

/-- Extract a level-0 `LogicGL` proof from level-0 `LogicGLAlpha`. -/
def toProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[GLAlpha 𝔸]! (Γ ⟹[0] Δ) → ⊢ᵍ[GL]! (Γ ⟹ Δ)
| .axm 0 A    => .axm A
| .botL 0     => .botL
| .wkL h h'   => .wkL (toProofGentzen h) h'
| .wkR h h'   => .wkR (toProofGentzen h) h'
| .impL h₁ h₂ => .impL (toProofGentzen h₁) (toProofGentzen h₂)
| .impR h     => .impR (toProofGentzen h)
| .boxGL h    => .boxGL (toProofGentzen h)

/-- Level-`0` `LogicGLAlpha.ProvableGentzen`-provability is exactly (plain, cut-free) `GL`-provability. -/
theorem iff_provableGentzen_provable_zero {Γ Δ : FormulaFinset α} :
  (⊢ᵍ[GL] (Γ ⟹ Δ)) ↔ (⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[0] Δ)) :=
  ⟨λ ⟨h⟩ => ⟨ofProofGentzen h⟩, λ ⟨h⟩ => ⟨toProofGentzen 𝔸 h⟩⟩

namespace ProvableGentzen

variable {𝔸 : Set ℕ}
variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {l : Fin 2} {n : ℕ}

lemma axm (l) (A : Formula α) : ⊢ᵍ[GLAlpha 𝔸] ({A} ⟹[l] {A}) := ⟨ProofGentzen.axm l A⟩
lemma botL (l) : ⊢ᵍ[GLAlpha 𝔸] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨ProofGentzen.botL l⟩
lemma wkL (π : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ[GLAlpha 𝔸] (Γ' ⟹[l] Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] Δ') := ⟨ProofGentzen.wkR π.some h⟩
lemma impL (π₁ : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] insert A Δ)) (π₂ : ⊢ᵍ[GLAlpha 𝔸] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[GLAlpha 𝔸] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᵍ[GLAlpha 𝔸] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩
lemma liftUp (π : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[0] Δ)) : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[1] Δ) := ⟨ProofGentzen.liftUp π.some⟩
lemma boxGL (π : ⊢ᵍ[GLAlpha 𝔸] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})) : ⊢ᵍ[GLAlpha 𝔸] (Γ.box ⟹[0] {□A}) := ⟨ProofGentzen.boxGL π.some⟩
lemma boxGP (n : n ∈ 𝔸) : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[1] insert (□^[n] ⊥) Δ) → ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[1] Δ) := λ ⟨π⟩ => ⟨ProofGentzen.boxGP π⟩

@[induction_eliminator]
lemma rec
  {motive : (S : TwoLayeredSequent α) → ⊢ᵍ[GLAlpha 𝔸] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (ProvableGentzen.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (ProvableGentzen.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (π : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) π → motive (Γ' ⟹[l] Δ) (wkL π h))
  (wkR : ∀ {l Γ Δ Δ'} (π : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) π → motive (Γ ⟹[l] Δ') (wkR π h))
  (impL : ∀ {l Γ Δ A B} (π₁ : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] insert A Δ)) (π₂ : ⊢ᵍ[GLAlpha 𝔸] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) π₁ → motive (insert B Γ ⟹[l] Δ) π₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL π₁ π₂)
  )
  (impR : ∀ {l Γ Δ A B} (π : ⊢ᵍ[GLAlpha 𝔸] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) π → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR π)
  )
  (liftUp : ∀ {Γ Δ} (π : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) π → motive (Γ ⟹[1] Δ) (liftUp π))
  (boxGL : ∀ {Γ A} (π : ⊢ᵍ[GLAlpha 𝔸] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) π → motive (Γ.box ⟹[0] {□A}) (boxGL π)
  )
  (boxGP : ∀ {Γ Δ n} (h : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[1] insert (□^[n] ⊥) Δ)),
    motive (Γ ⟹[1] insert (□^[n] ⊥) Δ) h → motive (Γ ⟹[1] Δ) (boxGP h)
  )
  : ∀ {S : TwoLayeredSequent α} (h : ⊢ᵍ[GLAlpha 𝔸] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

scoped prefix:120 "⊬ᵍ[GLAlpha 𝔸] " => (¬ ProvableGentzen ·)

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : TwoLayeredSequent α} : (⊬ᵍ[GLAlpha 𝔸] S) ↔ (IsEmpty (⊢ᵍ[GLAlpha 𝔸]! S)) := by
  simp [ProvableGentzen];

/-- Initial sequents with side formulas, at any level. -/
lemma union (l) (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] Δ) :=
  wkR (wkL (axm l A) (by grind)) (by grind)

lemma union' (l) (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ[GLAlpha 𝔸] (S.ant ⟹[l] S.suc) :=
  union l A hΓ hΔ

/-- `botL` with side formulas, at any level. -/
lemma botL_mem (l) (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[l] Δ) :=
  wkR (Δ := ∅) (wkL (botL l) (by grind)) (by grind)

lemma not_provable_zero_of_not_provable_one : ⊬ᵍ[GLAlpha 𝔸] (Γ ⟹[1] Δ) → ⊬ᵍ[GLAlpha 𝔸] (Γ ⟹[0] Δ) := by
  contrapose!;
  apply liftUp;

/-- Embed a cut-free `LogicGL` proof of `Γ ⟹ insert (□^[n]⊥) Δ` into level-`1` cut-free
`LogicGLAlpha` provability of `Γ ⟹[1] Δ`. -/
lemma of_provableGentzen_insert_boxItr_bot {n : ℕ}
  (h : ⊢ᵍ[GL] (Γ ⟹ insert (□^[n]⊥) Δ)) : ⊢ᵍ[GLAlpha 𝔸] (Γ ⟹[1] Δ) :=
  boxGP (liftUp (LogicGLAlpha.iff_provableGentzen_provable_zero.mp h))

end ProvableGentzen

open ProvableGentzen

lemma not_provableGentzen_of_not_provable_one {Γ Δ : FormulaFinset α} (h : ⊬ᵍ[GLAlpha 𝔸] (Γ ⟹[1] Δ)) : ⊬ᵍ[GL] (Γ ⟹ Δ) :=
  λ hp => ProvableGentzen.not_provable_zero_of_not_provable_one h (iff_provableGentzen_provable_zero.mp hp)

end LogicGLAlpha


inductive LogicGLAlpha.GentzenWithCutProof : TwoLayeredSequent α → Type u
| axm (l) (A)      : GentzenWithCutProof ({A} ⟹[l] {A})
| botL (l)         : GentzenWithCutProof (({⊥} : FormulaFinset α) ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → GentzenWithCutProof (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → GentzenWithCutProof (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : GentzenWithCutProof (Γ ⟹[l] (insert A Δ)) → GentzenWithCutProof (insert B Γ ⟹[l] Δ) → GentzenWithCutProof ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : GentzenWithCutProof ((insert A Γ) ⟹[l] (insert B Δ)) → GentzenWithCutProof (Γ ⟹[l] (insert (A 🡒 B) Δ))
| liftUp {Γ Δ}     : GentzenWithCutProof (Γ ⟹[0] Δ) → GentzenWithCutProof (Γ ⟹[1] Δ)
| boxGL {Γ A}      : GentzenWithCutProof ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) → GentzenWithCutProof (Γ.box ⟹[0] {□A})
| boxGP {Γ Δ n}    : GentzenWithCutProof (Γ ⟹[1] insert (□^[n] ⊥) Δ) → GentzenWithCutProof (Γ ⟹[1] Δ)
| cut  {l Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹[l] insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹[l] Δ₂) → GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂)

namespace LogicGLAlpha

scoped prefix:120 "⊢ᵍᶜ[GLAlpha 𝔸]! " => GentzenWithCutProof

abbrev GentzenWithCutProvable (S : TwoLayeredSequent α) : Prop := Nonempty (⊢ᵍᶜ[GLAlpha 𝔸]! S)
scoped prefix:120 "⊢ᵍᶜ[GLAlpha 𝔸] " => GentzenWithCutProvable

def GentzenWithCutProof.ofProofGentzen {S : TwoLayeredSequent α} : ⊢ᵍ[GLAlpha 𝔸]! S → ⊢ᵍᶜ[GLAlpha 𝔸]! S
| .axm l A    => .axm l A
| .botL l     => .botL l
| .wkL h h'   => .wkL (GentzenWithCutProof.ofProofGentzen h) h'
| .wkR h h'   => .wkR (GentzenWithCutProof.ofProofGentzen h) h'
| .impL h₁ h₂ => .impL (GentzenWithCutProof.ofProofGentzen h₁) (GentzenWithCutProof.ofProofGentzen h₂)
| .impR h     => .impR (GentzenWithCutProof.ofProofGentzen h)
| .liftUp h   => .liftUp (GentzenWithCutProof.ofProofGentzen h)
| .boxGL h    => .boxGL (GentzenWithCutProof.ofProofGentzen h)
| .boxGP h    => .boxGP (GentzenWithCutProof.ofProofGentzen h)

def GentzenWithCutProof.toGentzenWithCutProofGL {Γ Δ : FormulaFinset α} : ⊢ᵍᶜ[GLAlpha 𝔸]! (Γ ⟹[0] Δ) → ⊢ᵍᶜ[GL]! (Γ ⟹ Δ)
| .axm 0 A    => .axm A
| .botL 0     => .botL
| .wkL h h'   => .wkL (GentzenWithCutProof.toGentzenWithCutProofGL h) h'
| .wkR h h'   => .wkR (GentzenWithCutProof.toGentzenWithCutProofGL h) h'
| .impL h₁ h₂ => .impL (GentzenWithCutProof.toGentzenWithCutProofGL h₁) (GentzenWithCutProof.toGentzenWithCutProofGL h₂)
| .impR h     => .impR (GentzenWithCutProof.toGentzenWithCutProofGL h)
| .boxGL h    => .boxGL (GentzenWithCutProof.toGentzenWithCutProofGL h)
| .cut h₁ h₂  => .cut (GentzenWithCutProof.toGentzenWithCutProofGL h₁) (GentzenWithCutProof.toGentzenWithCutProofGL h₂)

namespace GentzenWithCutProvable

variable {S : TwoLayeredSequent α} {Γ Γ' Δ Δ' Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A B : Formula α} {l : Fin 2}

theorem of_without_cut : ⊢ᵍ[GLAlpha 𝔸] S → ⊢ᵍᶜ[GLAlpha 𝔸] S := λ ⟨h⟩ => ⟨GentzenWithCutProof.ofProofGentzen h⟩

/-- `Prop`-level version of `LogicGLAlpha.GentzenWithCutProof.toGentzenWithCutProofGL`. -/
theorem toGentzenWithCutProvableGL {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[0] Δ)) : ⊢ᵍᶜ[GL] (Γ ⟹ Δ) :=
  ⟨GentzenWithCutProof.toGentzenWithCutProofGL h.some⟩

/-- Level-`0` `LogicGLAlpha`-with-cut provability implies cut-free `LogicGL`-Gentzen provability. -/
theorem toProvableGentzenGL {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[0] Δ)) : ⊢ᵍ[GL] (Γ ⟹ Δ) :=
  LogicGL.ProvableGentzen.of_with_cut (toGentzenWithCutProvableGL h)

lemma axm (l) (A : Formula α) : ⊢ᵍᶜ[GLAlpha 𝔸] ({A} ⟹[l] {A}) := ⟨GentzenWithCutProof.axm l A⟩
lemma botL (l) : ⊢ᵍᶜ[GLAlpha 𝔸] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨GentzenWithCutProof.botL l⟩
lemma wkL (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ') : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ' ⟹[l] Δ) := ⟨GentzenWithCutProof.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ') : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] Δ') := ⟨GentzenWithCutProof.wkR h.some h'⟩
lemma impL (h₁ : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[GLAlpha 𝔸] (insert B Γ ⟹[l] Δ)) : ⊢ᵍᶜ[GLAlpha 𝔸] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨GentzenWithCutProof.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ[GLAlpha 𝔸] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨GentzenWithCutProof.impR h.some⟩
lemma liftUp (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[0] Δ)) : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.liftUp h.some⟩
lemma boxGL (h : ⊢ᵍᶜ[GLAlpha 𝔸] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})) : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ.box ⟹[0] {□A}) := ⟨GentzenWithCutProof.boxGL h.some⟩
lemma boxGP (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[1] insert (□^[n] ⊥) Δ)) : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.boxGP h.some⟩
lemma cut (h₁ : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[GLAlpha 𝔸] (insert A Γ₂ ⟹[l] Δ₂)) : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) :=
  ⟨GentzenWithCutProof.cut h₁.some h₂.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : TwoLayeredSequent α) → ⊢ᵍᶜ[GLAlpha 𝔸] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (GentzenWithCutProvable.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (GentzenWithCutProvable.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) h → motive (Γ' ⟹[l] Δ) (wkL h h'))
  (wkR : ∀ {l Γ Δ Δ'} (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) h → motive (Γ ⟹[l] Δ') (wkR h h'))
  (impL : ∀ {l Γ Δ A B} (h₁ : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[GLAlpha 𝔸] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) h₁ → motive (insert B Γ ⟹[l] Δ) h₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL h₁ h₂)
  )
  (impR : ∀ {l Γ Δ A B} (h : ⊢ᵍᶜ[GLAlpha 𝔸] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) h → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR h)
  )
  (liftUp : ∀ {Γ Δ} (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) h → motive (Γ ⟹[1] Δ) (liftUp h))
  (boxGL : ∀ {Γ A} (h : ⊢ᵍᶜ[GLAlpha 𝔸] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) h → motive (Γ.box ⟹[0] {□A}) (boxGL h)
  )
  (boxGP : ∀ {Γ Δ n} (h : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ ⟹[1] insert (□^[n] ⊥) Δ)),
    motive (Γ ⟹[1] insert (□^[n] ⊥) Δ) h → motive (Γ ⟹[1] Δ) (boxGP h)
  )
  (cut : ∀ {l Γ₁ Γ₂ Δ₁ Δ₂ A} (h₁ : ⊢ᵍᶜ[GLAlpha 𝔸] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[GLAlpha 𝔸] (insert A Γ₂ ⟹[l] Δ₂)),
    motive (Γ₁ ⟹[l] insert A Δ₁) h₁ → motive (insert A Γ₂ ⟹[l] Δ₂) h₂ →
    motive (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) (GentzenWithCutProvable.cut h₁ h₂)
  )
  : ∀ {S : TwoLayeredSequent α} (h : ⊢ᵍᶜ[GLAlpha 𝔸] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

/-- The axiom `∼□^[n]⊥` is with-cut-provable at level `1`. -/
lemma neg_boxItr_bot (n : ℕ) : ⊢ᵍᶜ[GLAlpha 𝔸] ((∅ : FormulaFinset α) ⟹[1] {∼□^[n]⊥}) := by
  show ⊢ᵍᶜ[GLAlpha 𝔸] ((∅ : FormulaFinset α) ⟹[1] {□^[n]⊥ 🡒 ⊥});
  rw [← Finset.insert_empty];
  apply impR;
  apply boxGP (n := n);
  apply wkR (axm 1 (□^[n]⊥));
  grind;

/-- Modus ponens for level-`1` with-cut provability, via the `cut` rule. -/
lemma mdp (hAB : ⊢ᵍᶜ[GLAlpha 𝔸] (∅ ⟹[1] {A 🡒 B})) (hA : ⊢ᵍᶜ[GLAlpha 𝔸] (∅ ⟹[1] {A})) : ⊢ᵍᶜ[GLAlpha 𝔸] (∅ ⟹[1] {B}) := by
  have h₁ : ⊢ᵍᶜ[GLAlpha 𝔸] ((insert (A 🡒 B) (∅ : FormulaFinset α)) ⟹[1] {B}) :=
    impL (wkR hA (by grind)) (wkL (axm 1 B) (by grind));
  have h₂ : ⊢ᵍᶜ[GLAlpha 𝔸] ((∅ : FormulaFinset α) ⟹[1] insert (A 🡒 B) (∅ : FormulaFinset α)) := by
    rwa [Finset.insert_empty];
  simpa using cut h₂ h₁;

end GentzenWithCutProvable

end LogicGLAlpha


end
