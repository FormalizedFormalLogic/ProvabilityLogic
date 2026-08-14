module

public import ProvabilityLogic.Gentzen.S.Basic

@[expose]
public section

open LogicGL
open scoped LogicS

variable {α : Type u} [DecidableEq α]

/--
  A `Sequent` layered with a level `l : Fin 3`, as used by the three-level sequent calculus
  `LogicD.ProofGentzen`.

  - [KKIM25, §3]
-/
structure ThreeLayeredSequent (α : Type u) extends Sequent α where
  level : Fin 3
notation:50 Γ:51 " ⟹[" l "] " Δ:51 => ThreeLayeredSequent.mk (Γ ⟹ Δ) l

/--
  Sequent calculus `D³_seq` for the provability logic `D`, formulated with a single sequent
  relation `Γ ⟹[l] Δ` indexed by a level `l : Fin 3`. `l = 0` is the GL-sequent (`⇒`),
  coinciding with `LogicGL.ProofGentzen`; `l = 1` is the S-sequent (`⊢`), coinciding with
  `LogicS.ProofGentzen` at level `1`; `l = 2` is the D-sequent (`⇒⇒`), reachable only from
  boxed S-sequents via `liftUpBox`. As noted in the source, the bottom layer of a `D³_seq`-proof
  therefore consists only of the level-generic `LK⇒⇒` rules.

  - [KKIM25, §3]
-/
inductive LogicD.ProofGentzen : ThreeLayeredSequent α → Type u
| axm (l) (A)      : ProofGentzen ({A} ⟹[l] {A})
| botL (l)         : ProofGentzen (({⊥} : FormulaFinset α) ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : ProofGentzen (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : ProofGentzen (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : ProofGentzen (Γ ⟹[l] (insert A Δ)) → ProofGentzen (insert B Γ ⟹[l] Δ) → ProofGentzen ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹[l] (insert B Δ)) → ProofGentzen (Γ ⟹[l] (insert (A 🡒 B) Δ))
| boxGL {Γ A}      : ProofGentzen ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) → ProofGentzen (Γ.box ⟹[0] {□A})
| liftUp {Γ Δ}     : ProofGentzen (Γ ⟹[0] Δ) → ProofGentzen (Γ ⟹[1] Δ)
| boxL {Γ Δ A}     : ProofGentzen (insert A Γ ⟹[1] Δ) → ProofGentzen (insert (□A) Γ ⟹[1] Δ)
| liftUpBox {Γ Δ : FormulaFinset α} : ProofGentzen (Γ.box ⟹[1] Δ.box) → ProofGentzen (Γ.box ⟹[2] Δ.box)

namespace LogicD

scoped notation:120 "⊢ᵍ[D]! " Seq:121 => ProofGentzen Seq

abbrev ProvableGentzen (S : ThreeLayeredSequent α) : Prop := Nonempty (⊢ᵍ[D]! S)
scoped notation:120 "⊢ᵍ[D] " Seq:121 => ProvableGentzen Seq

/--
  `LogicD.ProofGentzen` at level `0` coincides syntactically with the plain (level-independent)
  `ProofGentzen` for `GL`: every rule available for a level-`0` conclusion is exactly a rule of
  `ProofGentzen`, and `liftUp`/`boxL`/`liftUpBox` can never conclude a level-`0` sequent.

  - [KKIM25, Theorem 4.1]
-/
def ofProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[GL]! (Γ ⟹ Δ) → ⊢ᵍ[D]! (Γ ⟹[0] Δ) := sorry

/-- The converse translation, by structural recursion on level-`0` `LogicD.ProofGentzen`-proofs. -/
def toProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[0] Δ) → ⊢ᵍ[GL]! (Γ ⟹ Δ) := sorry

/--
  Level-`0` `LogicD.ProvableGentzen`-provability is exactly (plain, cut-free) `GL`-provability.

  - [KKIM25, Theorem 4.1]
-/
theorem iff_provableGentzen_provable_zero {Γ Δ : FormulaFinset α} :
  (⊢ᵍ[GL] (Γ ⟹ Δ)) ↔ (⊢ᵍ[D] (Γ ⟹[0] Δ)) := sorry

/--
  Every `LogicS.ProofGentzen`-proof of a level-`1` sequent is in particular a
  `LogicD.ProofGentzen`-proof of the same sequent: any `D³_seq`-proof of an S-sequent
  consists only of the rules of `S_seq`.

  - [KKIM25, Theorem 4.2]
-/
def ofProofGentzenS {Γ Δ : FormulaFinset α} : ⊢ᵍ[S]! (Γ ⟹[1] Δ) → ⊢ᵍ[D]! (Γ ⟹[1] Δ) := sorry

/-- The converse translation, by structural recursion on level-`1` `LogicD.ProofGentzen`-proofs. -/
def toProofGentzenS {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[1] Δ) → ⊢ᵍ[S]! (Γ ⟹[1] Δ) := sorry

/--
  Level-`1` `LogicD.ProvableGentzen`-provability is exactly level-`1` `LogicS.ProvableGentzen`-provability.

  - [KKIM25, Theorem 4.2]
-/
theorem iff_provableGentzenS_provable_one {Γ Δ : FormulaFinset α} :
  (⊢ᵍ[S] (Γ ⟹[1] Δ)) ↔ (⊢ᵍ[D] (Γ ⟹[1] Δ)) := sorry

namespace ProofGentzen

/--
  Every `GL`-sequent provable in `GL_seq` is also provable, at the top `D`-sequent level, in
  `D³_seq`: from a `LogicD.ProofGentzen`-proof of a level-`0` sequent, obtain a level-`2` proof of
  the same sequent by applying `(GLtoS)` then `(StoD)` at the `(GL□)` step, and recursing
  through the other `LK⇒⇒` rules.

  - [KKIM25, Theorem 4.3]
-/
def liftUpTwo {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[0] Δ) → ⊢ᵍ[D]! (Γ ⟹[2] Δ) := sorry

end ProofGentzen

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {l : Fin 3}

/--
  The initial sequent `A ⟹[l] A`, at any level.

  - [KKIM25, §3]
-/
lemma axm (l) (A : Formula α) : ⊢ᵍ[D] ({A} ⟹[l] {A}) := ⟨ProofGentzen.axm l A⟩
/--
  The initial sequent `⊥ ⟹[l]`, at any level.

  - [KKIM25, §3]
-/
lemma botL (l) : ⊢ᵍ[D] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨ProofGentzen.botL l⟩
/--
  Left weakening, at any level.

  - [KKIM25, §3]
-/
lemma wkL (π : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ[D] (Γ' ⟹[l] Δ) := sorry
/--
  Right weakening, at any level.

  - [KKIM25, §3]
-/
lemma wkR (π : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ[D] (Γ ⟹[l] Δ') := sorry
/--
  Left introduction of `🡒`, at any level.

  - [KKIM25, §3]
-/
lemma impL (π₁ : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) (π₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[D] ((insert (A 🡒 B) Γ) ⟹[l] Δ) := sorry
/--
  Right introduction of `🡒`, at any level.

  - [KKIM25, §3]
-/
lemma impR (π : ⊢ᵍ[D] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍ[D] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := sorry
/--
  `(GLtoS)`: a GL-sequent lifts to an S-sequent.

  - [KKIM25, §3]
-/
lemma liftUp (π : ⊢ᵍ[D] (Γ ⟹[0] Δ)) : ⊢ᵍ[D] (Γ ⟹[1] Δ) := sorry
/--
  `(GL□)`.

  - [KKIM25, §3]
-/
lemma boxGL (π : ⊢ᵍ[D] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})) : ⊢ᵍ[D] (Γ.box ⟹[0] {□A}) := sorry
/--
  `(S□left)`.

  - [KKIM25, §3]
-/
lemma boxL (π : ⊢ᵍ[D] (insert A Γ ⟹[1] Δ)) : ⊢ᵍ[D] (insert (□A) Γ ⟹[1] Δ) := sorry
/--
  `(StoD)`: a boxed S-sequent lifts to a D-sequent.

  - [KKIM25, §3]
-/
lemma liftUpBox {Γ Δ : FormulaFinset α} (π : ⊢ᵍ[D] (Γ.box ⟹[1] Δ.box)) : ⊢ᵍ[D] (Γ.box ⟹[2] Δ.box) := sorry

/--
  Induction principle for `LogicD.ProvableGentzen` at the `Prop` level, mirroring
  `LogicS.ProvableGentzen.rec` for the two-level `S` calculus.
-/
@[induction_eliminator]
lemma rec
  {motive : (S : ThreeLayeredSequent α) → ⊢ᵍ[D] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (ProvableGentzen.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (ProvableGentzen.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (π : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (h : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) π → motive (Γ' ⟹[l] Δ) (wkL π h))
  (wkR : ∀ {l Γ Δ Δ'} (π : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (h : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) π → motive (Γ ⟹[l] Δ') (wkR π h))
  (impL : ∀ {l Γ Δ A B} (π₁ : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) (π₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) π₁ → motive (insert B Γ ⟹[l] Δ) π₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL π₁ π₂)
  )
  (impR : ∀ {l Γ Δ A B} (π : ⊢ᵍ[D] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) π → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR π)
  )
  (liftUp : ∀ {Γ Δ} (π : ⊢ᵍ[D] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) π → motive (Γ ⟹[1] Δ) (liftUp π))
  (boxGL : ∀ {Γ A} (π : ⊢ᵍ[D] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) π → motive (Γ.box ⟹[0] {□A}) (boxGL π)
  )
  (boxL : ∀ {Γ Δ A} (π : ⊢ᵍ[D] (insert A Γ ⟹[1] Δ)),
    motive (insert A Γ ⟹[1] Δ) π → motive (insert (□A) Γ ⟹[1] Δ) (boxL π)
  )
  (liftUpBox : ∀ {Γ Δ : FormulaFinset α} (π : ⊢ᵍ[D] (Γ.box ⟹[1] Δ.box)),
    motive (Γ.box ⟹[1] Δ.box) π → motive (Γ.box ⟹[2] Δ.box) (liftUpBox π)
  )
  : ∀ {S : ThreeLayeredSequent α} (h : ⊢ᵍ[D] S), motive S h := sorry

scoped prefix:120 "⊬ᴰ " => λ S => ¬⊢ᵍ[D] S

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : ThreeLayeredSequent α} : (⊬ᴰ S) ↔ (IsEmpty (⊢ᵍ[D]! S)) := sorry

/-- Initial sequents with side formulas, at any level. -/
lemma union (l) (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[D] (Γ ⟹[l] Δ) := sorry

/-- `Sequent`-shaped variant of `LogicD.ProvableGentzen.union`. -/
lemma union' (l) (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ[D] (S.ant ⟹[l] S.suc) := sorry

/-- `botL` with side formulas, at any level. -/
lemma botL_mem (l) (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[D] (Γ ⟹[l] Δ) := sorry

/-- If a level-`1` sequent is `LogicD.ProvableGentzen`-unprovable then so is the level-`0` one. -/
lemma not_provable_zero_of_not_provable_one : ⊬ᴰ (Γ ⟹[1] Δ) → ⊬ᴰ (Γ ⟹[0] Δ) := sorry

/--
  Disjunction left, the derived rule for the abbreviation `A ⋎ B := ∼A 🡒 B`, at any level.

  - [KKIM25, §3]
-/
lemma orL (π₁ : ⊢ᵍ[D] (insert A Γ ⟹[l] Δ)) (π₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[D] (insert (A ⋎ B) Γ ⟹[l] Δ) := sorry

/--
  Disjunction right, the derived rule for the abbreviation `A ⋎ B := ∼A 🡒 B`, at any level.

  - [KKIM25, §3]
-/
lemma orR (π : ⊢ᵍ[D] (Γ ⟹[l] (insert A (insert B Δ)))) : ⊢ᵍ[D] (Γ ⟹[l] insert (A ⋎ B) Δ) := sorry

/--
  Negation left, the derived rule for the abbreviation `∼A := A 🡒 ⊥`, at any level.

  - [KKIM25, §3]
-/
lemma negL (π : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) : ⊢ᵍ[D] (insert (∼A) Γ ⟹[l] Δ) := sorry

/--
  Negation right, the derived rule for the abbreviation `∼A := A 🡒 ⊥`, at any level.

  - [KKIM25, §3]
-/
lemma negR (π : ⊢ᵍ[D] (insert A Γ ⟹[l] Δ)) : ⊢ᵍ[D] (Γ ⟹[l] insert (∼A) Δ) := sorry

/--
  `Prop`-level version of `LogicD.ProofGentzen.liftUpTwo`.

  - [KKIM25, Theorem 4.3]
-/
lemma liftUpTwo (π : ⊢ᵍ[D] (Γ ⟹[0] Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) := sorry

/--
  The `D³_seq`-provability of the axiom `□(□A ⋎ □B) 🡒 (□A ⋎ □B)`.

  - [KKIM25, Example 3.2]
-/
lemma axiomD {A B : Formula α} : ⊢ᵍ[D] (∅ ⟹[2] {□(□A ⋎ □B) 🡒 (□A ⋎ □B)}) := sorry

/--
  The `D³_seq`-provability of `∼□⊥`, the `D³_seq` adaptation of the `D²_seq`-proof
  given in the source (there stated with `(GLtoD)`, which `D³_seq` does not have).

  - [KKIM25, Example 3.3]
-/
lemma axiomP : ⊢ᵍ[D] ((∅ : FormulaFinset α) ⟹[2] {∼□(⊥ : Formula α)}) := sorry

end ProvableGentzen

open ProvableGentzen

/--
  Every `GL_seq`-proof lifts to a `D³_seq`-proof of the same sequent at the top D-sequent level.

  - [KKIM25, Theorem 4.3]
-/
theorem provable_two_of_provableGentzen_GL {Γ Δ : FormulaFinset α} (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) := sorry

/--
  Every `GL_seq`-proof lifts to a `D³_seq`-proof of the same sequent at the S-sequent level.

  - [KKIM25, Theorem 4.3]
-/
theorem provable_one_of_provableGentzen_GL {Γ Δ : FormulaFinset α} (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) : ⊢ᵍ[D] (Γ ⟹[1] Δ) := sorry

end LogicD

end
