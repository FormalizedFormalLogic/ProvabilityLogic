module

public import ProvabilityLogic.Gentzen.GL.Basic

@[expose]
public section

open LogicGL

variable {α : Type u} [DecidableEq α]

/--
  A `Sequent` layered with a level `l : Fin 2`, as used by the two-level sequent calculus
  `LogicS.ProofGentzen`.
-/
structure TwoLayeredSequent (α : Type u) extends Sequent α where
  level : Fin 2
notation:50 Γ:51 " ⟹[" l "] " Δ:51 => TwoLayeredSequent.mk (Γ ⟹ Δ) l

/--
  Sequent calculus for the logic `S` (also called `GLSseq` in the literature, or `𝗚𝐒` in PLPL §2),
  formulated with a single sequent relation `Γ ⟹[l] Δ` indexed by a level `l : Fin 2`. `l = 0` is
  the level-1 (GL) sequent, coinciding with `LogicGL.ProofGentzen`; `l = 1` is
  the level-2 (S) sequent, obtained from the level-1 one by additionally allowing the reflexivity
  rule `boxL`.

  - [KK23, "GLSseq"]
-/
inductive LogicS.ProofGentzen : TwoLayeredSequent α → Type u
| axm (l) (A)      : ProofGentzen ({A} ⟹[l] {A})
| botL (l)         : ProofGentzen (({⊥} : FormulaFinset α) ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : ProofGentzen (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : ProofGentzen (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : ProofGentzen (Γ ⟹[l] (insert A Δ)) → ProofGentzen (insert B Γ ⟹[l] Δ) → ProofGentzen ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹[l] (insert B Δ)) → ProofGentzen (Γ ⟹[l] (insert (A 🡒 B) Δ))
| liftUp {Γ Δ}     : ProofGentzen (Γ ⟹[0] Δ) → ProofGentzen (Γ ⟹[1] Δ)
| boxGL {Γ A}      : ProofGentzen ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) → ProofGentzen (Γ.box ⟹[0] {□A})
| boxL {Γ Δ A}     : ProofGentzen (insert A Γ ⟹[1] Δ) → ProofGentzen (insert (□A) Γ ⟹[1] Δ)

namespace LogicS

scoped notation:120 "⊢ᵍ[S]! " Seq:121 => ProofGentzen Seq

abbrev ProvableGentzen (S : TwoLayeredSequent α) : Prop := Nonempty (⊢ᵍ[S]! S)
scoped notation:120 "⊢ᵍ[S] " Seq:121 => ProvableGentzen Seq

/--
  `LogicS.ProofGentzen` at level `0` coincides syntactically with the plain (level-independent)
  `ProofGentzen` for `GL`: every rule available for a level-`0` conclusion is exactly a rule of
  `ProofGentzen`, and `liftUp`/`boxL` can never conclude a level-`0` sequent.
-/
def ofProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[GL]! (Γ ⟹ Δ) → ⊢ᵍ[S]! (Γ ⟹[0] Δ)
| .axm A    => .axm 0 A
| .botL     => .botL 0
| .wkL h h' => .wkL (ofProofGentzen h) h'
| .wkR h h' => .wkR (ofProofGentzen h) h'
| .impL h₁ h₂ => .impL (ofProofGentzen h₁) (ofProofGentzen h₂)
| .impR h   => .impR (ofProofGentzen h)
| .boxGL h  => .boxGL (ofProofGentzen h)

/-- The converse translation, by structural recursion on level-`0` `LogicS.ProofGentzen`-proofs. -/
def toProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[S]! (Γ ⟹[0] Δ) → ⊢ᵍ[GL]! (Γ ⟹ Δ)
| .axm 0 A    => .axm A
| .botL 0     => .botL
| .wkL h h'   => .wkL (toProofGentzen h) h'
| .wkR h h'   => .wkR (toProofGentzen h) h'
| .impL h₁ h₂ => .impL (toProofGentzen h₁) (toProofGentzen h₂)
| .impR h     => .impR (toProofGentzen h)
| .boxGL h    => .boxGL (toProofGentzen h)

/-- Level-`0` `LogicS.ProvableGentzen`-provability is exactly (plain, cut-free) `GL`-provability. -/
theorem iff_provableGentzen_provable_zero {Γ Δ : FormulaFinset α} :
  (⊢ᵍ[GL] (Γ ⟹ Δ)) ↔ (⊢ᵍ[S] (Γ ⟹[0] Δ)) :=
  ⟨λ ⟨h⟩ => ⟨ofProofGentzen h⟩, λ ⟨h⟩ => ⟨toProofGentzen h⟩⟩

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {l : Fin 2}

lemma axm (l) (A : Formula α) : ⊢ᵍ[S] ({A} ⟹[l] {A}) := ⟨ProofGentzen.axm l A⟩
lemma botL (l) : ⊢ᵍ[S] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨ProofGentzen.botL l⟩
lemma wkL (π : ⊢ᵍ[S] (Γ ⟹[l] Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ[S] (Γ' ⟹[l] Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᵍ[S] (Γ ⟹[l] Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ[S] (Γ ⟹[l] Δ') := ⟨ProofGentzen.wkR π.some h⟩
lemma impL (π₁ : ⊢ᵍ[S] (Γ ⟹[l] insert A Δ)) (π₂ : ⊢ᵍ[S] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[S] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᵍ[S] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍ[S] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩
lemma liftUp (π : ⊢ᵍ[S] (Γ ⟹[0] Δ)) : ⊢ᵍ[S] (Γ ⟹[1] Δ) := ⟨ProofGentzen.liftUp π.some⟩
lemma boxGL (π : ⊢ᵍ[S] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})) : ⊢ᵍ[S] (Γ.box ⟹[0] {□A}) := ⟨ProofGentzen.boxGL π.some⟩
lemma boxL (π : ⊢ᵍ[S] (insert A Γ ⟹[1] Δ)) : ⊢ᵍ[S] (insert (□A) Γ ⟹[1] Δ) := ⟨ProofGentzen.boxL π.some⟩

/--
  Induction principle for `LogicS.ProvableGentzen` at the `Prop` level, mirroring
  `ProvabilityLogic.Gentzen.ProvableGentzen.rec` for the (level-free) `GL` calculus.
-/
@[induction_eliminator]
lemma rec
  {motive : (S : TwoLayeredSequent α) → ⊢ᵍ[S] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (ProvableGentzen.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (ProvableGentzen.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (π : ⊢ᵍ[S] (Γ ⟹[l] Δ)) (h : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) π → motive (Γ' ⟹[l] Δ) (wkL π h))
  (wkR : ∀ {l Γ Δ Δ'} (π : ⊢ᵍ[S] (Γ ⟹[l] Δ)) (h : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) π → motive (Γ ⟹[l] Δ') (wkR π h))
  (impL : ∀ {l Γ Δ A B} (π₁ : ⊢ᵍ[S] (Γ ⟹[l] insert A Δ)) (π₂ : ⊢ᵍ[S] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) π₁ → motive (insert B Γ ⟹[l] Δ) π₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL π₁ π₂)
  )
  (impR : ∀ {l Γ Δ A B} (π : ⊢ᵍ[S] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) π → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR π)
  )
  (liftUp : ∀ {Γ Δ} (π : ⊢ᵍ[S] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) π → motive (Γ ⟹[1] Δ) (liftUp π))
  (boxGL : ∀ {Γ A} (π : ⊢ᵍ[S] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) π → motive (Γ.box ⟹[0] {□A}) (boxGL π)
  )
  (boxL : ∀ {Γ Δ A} (π : ⊢ᵍ[S] (insert A Γ ⟹[1] Δ)),
    motive (insert A Γ ⟹[1] Δ) π → motive (insert (□A) Γ ⟹[1] Δ) (boxL π)
  )
  : ∀ {S : TwoLayeredSequent α} (h : ⊢ᵍ[S] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

scoped prefix:120 "⊬ᴳ " => λ S => ¬⊢ᵍ[S] S

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : TwoLayeredSequent α} : (⊬ᴳ S) ↔ (IsEmpty (⊢ᵍ[S]! S)) := by
  simp [ProvableGentzen];

/-- Initial sequents with side formulas, at any level. -/
lemma union (l) (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[S] (Γ ⟹[l] Δ) :=
  wkR (wkL (axm l A) (by grind)) (by grind)

/-- `Sequent`-shaped variant of `LogicS.ProvableGentzen.union`. -/
lemma union' (l) (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ[S] (S.ant ⟹[l] S.suc) :=
  union l A hΓ hΔ

/-- `botL` with side formulas, at any level. -/
lemma botL_mem (l) (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[S] (Γ ⟹[l] Δ) :=
  wkR (Δ := ∅) (wkL (botL l) (by grind)) (by grind)

/-- If a level-`1` sequent is `LogicS.ProvableGentzen`-unprovable then so is the level-`0` one. -/
lemma not_provable_zero_of_not_provable_one : ⊬ᴳ (Γ ⟹[1] Δ) → ⊬ᴳ (Γ ⟹[0] Δ) := by
  contrapose!;
  apply liftUp;

end ProvableGentzen

open ProvableGentzen

/-- If a level-`1` sequent is `LogicS.ProvableGentzen`-unprovable then the plain sequent is `ProvableGentzen`-unprovable. -/
lemma not_provableGentzen_of_not_provable_one {Γ Δ : FormulaFinset α} (h : ⊬ᴳ (Γ ⟹[1] Δ)) : ⊬ᵍ[GL] (Γ ⟹ Δ) :=
  λ hp => ProvableGentzen.not_provable_zero_of_not_provable_one h (iff_provableGentzen_provable_zero.mp hp)

end LogicS

/--
  `LogicS.ProofGentzen` extended with a level-preserving cut rule (called `Cut^l_l` in PLPL §2).
  This is the "with cut" calculus alongside which `LogicS.ProofGentzen` is cut-free.

  - [KK23]
-/
inductive LogicS.GentzenWithCutProof : TwoLayeredSequent α → Type u
| axm (l) (A)      : GentzenWithCutProof ({A} ⟹[l] {A})
| botL (l)         : GentzenWithCutProof (({⊥} : FormulaFinset α) ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → GentzenWithCutProof (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → GentzenWithCutProof (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : GentzenWithCutProof (Γ ⟹[l] (insert A Δ)) → GentzenWithCutProof (insert B Γ ⟹[l] Δ) → GentzenWithCutProof ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : GentzenWithCutProof ((insert A Γ) ⟹[l] (insert B Δ)) → GentzenWithCutProof (Γ ⟹[l] (insert (A 🡒 B) Δ))
| liftUp {Γ Δ}     : GentzenWithCutProof (Γ ⟹[0] Δ) → GentzenWithCutProof (Γ ⟹[1] Δ)
| boxGL {Γ A}      : GentzenWithCutProof ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) → GentzenWithCutProof (Γ.box ⟹[0] {□A})
| boxL {Γ Δ A}     : GentzenWithCutProof (insert A Γ ⟹[1] Δ) → GentzenWithCutProof (insert (□A) Γ ⟹[1] Δ)
| cut  {l Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹[l] insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹[l] Δ₂) → GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂)

namespace LogicS

scoped notation:120 "⊢ᵍᶜ[S]! " Seq:121 => GentzenWithCutProof Seq

abbrev GentzenWithCutProvable (S : TwoLayeredSequent α) : Prop := Nonempty (⊢ᵍᶜ[S]! S)
scoped notation:120 "⊢ᵍᶜ[S] " Seq:121 => GentzenWithCutProvable Seq

/-- Every `LogicS.ProofGentzen`-proof is in particular a `LogicS.GentzenWithCutProof`-proof. -/
def GentzenWithCutProof.ofProofGentzen {S : TwoLayeredSequent α} : ⊢ᵍ[S]! S → ⊢ᵍᶜ[S]! S
| .axm l A    => .axm l A
| .botL l     => .botL l
| .wkL h h'   => .wkL (GentzenWithCutProof.ofProofGentzen h) h'
| .wkR h h'   => .wkR (GentzenWithCutProof.ofProofGentzen h) h'
| .impL h₁ h₂ => .impL (GentzenWithCutProof.ofProofGentzen h₁) (GentzenWithCutProof.ofProofGentzen h₂)
| .impR h     => .impR (GentzenWithCutProof.ofProofGentzen h)
| .liftUp h   => .liftUp (GentzenWithCutProof.ofProofGentzen h)
| .boxGL h    => .boxGL (GentzenWithCutProof.ofProofGentzen h)
| .boxL h     => .boxL (GentzenWithCutProof.ofProofGentzen h)

namespace GentzenWithCutProvable

variable {S : TwoLayeredSequent α} {Γ Γ' Δ Δ' Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A B : Formula α} {l : Fin 2}

/--
  Cut-free provability of `LogicS.ProofGentzen` implies provability of the with-cut calculus
  `LogicS.GentzenWithCutProof` (a fortiori, adding the cut rule can only add proofs).

  - [KK23, Theorem 3.1]
-/
theorem of_without_cut : ⊢ᵍ[S] S → ⊢ᵍᶜ[S] S := λ ⟨h⟩ => ⟨GentzenWithCutProof.ofProofGentzen h⟩

lemma axm (l) (A : Formula α) : ⊢ᵍᶜ[S] ({A} ⟹[l] {A}) := ⟨GentzenWithCutProof.axm l A⟩
lemma botL (l) : ⊢ᵍᶜ[S] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨GentzenWithCutProof.botL l⟩
lemma wkL (h : ⊢ᵍᶜ[S] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ') : ⊢ᵍᶜ[S] (Γ' ⟹[l] Δ) := ⟨GentzenWithCutProof.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ[S] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ') : ⊢ᵍᶜ[S] (Γ ⟹[l] Δ') := ⟨GentzenWithCutProof.wkR h.some h'⟩
lemma impL (h₁ : ⊢ᵍᶜ[S] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[S] (insert B Γ ⟹[l] Δ)) : ⊢ᵍᶜ[S] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨GentzenWithCutProof.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ[S] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍᶜ[S] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨GentzenWithCutProof.impR h.some⟩
lemma liftUp (h : ⊢ᵍᶜ[S] (Γ ⟹[0] Δ)) : ⊢ᵍᶜ[S] (Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.liftUp h.some⟩
lemma boxGL (h : ⊢ᵍᶜ[S] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})) : ⊢ᵍᶜ[S] (Γ.box ⟹[0] {□A}) := ⟨GentzenWithCutProof.boxGL h.some⟩
lemma boxL (h : ⊢ᵍᶜ[S] (insert A Γ ⟹[1] Δ)) : ⊢ᵍᶜ[S] (insert (□A) Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.boxL h.some⟩
lemma cut (h₁ : ⊢ᵍᶜ[S] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[S] (insert A Γ₂ ⟹[l] Δ₂)) : ⊢ᵍᶜ[S] (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) :=
  ⟨GentzenWithCutProof.cut h₁.some h₂.some⟩

/--
  Induction principle for `LogicS.GentzenWithCutProvable` at the `Prop` level, mirroring
  `ProvabilityLogic.Gentzen.GL.WithCut.GentzenWithCutProvable.rec` for the (level-free) `GL` calculus.
-/
@[induction_eliminator]
lemma rec
  {motive : (S : TwoLayeredSequent α) → ⊢ᵍᶜ[S] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (GentzenWithCutProvable.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (GentzenWithCutProvable.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (h : ⊢ᵍᶜ[S] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) h → motive (Γ' ⟹[l] Δ) (wkL h h'))
  (wkR : ∀ {l Γ Δ Δ'} (h : ⊢ᵍᶜ[S] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) h → motive (Γ ⟹[l] Δ') (wkR h h'))
  (impL : ∀ {l Γ Δ A B} (h₁ : ⊢ᵍᶜ[S] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[S] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) h₁ → motive (insert B Γ ⟹[l] Δ) h₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL h₁ h₂)
  )
  (impR : ∀ {l Γ Δ A B} (h : ⊢ᵍᶜ[S] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) h → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR h)
  )
  (liftUp : ∀ {Γ Δ} (h : ⊢ᵍᶜ[S] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) h → motive (Γ ⟹[1] Δ) (liftUp h))
  (boxGL : ∀ {Γ A} (h : ⊢ᵍᶜ[S] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) h → motive (Γ.box ⟹[0] {□A}) (boxGL h)
  )
  (boxL : ∀ {Γ Δ A} (h : ⊢ᵍᶜ[S] (insert A Γ ⟹[1] Δ)),
    motive (insert A Γ ⟹[1] Δ) h → motive (insert (□A) Γ ⟹[1] Δ) (boxL h)
  )
  (cut : ∀ {l Γ₁ Γ₂ Δ₁ Δ₂ A} (h₁ : ⊢ᵍᶜ[S] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[S] (insert A Γ₂ ⟹[l] Δ₂)),
    motive (Γ₁ ⟹[l] insert A Δ₁) h₁ → motive (insert A Γ₂ ⟹[l] Δ₂) h₂ →
    motive (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) (GentzenWithCutProvable.cut h₁ h₂)
  )
  : ∀ {S : TwoLayeredSequent α} (h : ⊢ᵍᶜ[S] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

end GentzenWithCutProvable

end LogicS


end
