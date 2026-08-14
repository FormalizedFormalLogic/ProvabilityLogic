module

public import ProvabilityLogic.Gentzen.S.Basic

/-!
Cut-free sequent calculus `D³_seq` for the provability logic `D`.

`LogicD.ProofGentzen` is a single inductive on `ThreeLayeredSequent`, a `Sequent` tagged with
a level `l : Fin 3`: `l = 0` is the GL-sequent, `l = 1` is the S-sequent, and `l = 2` is the
D-sequent. The constructors encode the source's modal rules `(GL□)` (`boxGL`), `(GLtoS)`
(`liftUp`), `(S□left)` (`boxL`), and `(StoD)` (`liftUpBox`).
-/

@[expose]
public section

open LogicGL
open scoped LogicS

variable {α : Type u} [DecidableEq α]

/-- A `Sequent` with a level `l : Fin 3`, used in the three-level sequent calculus for `D`.

  - [KKIM25, §3]
-/
structure ThreeLayeredSequent (α : Type u) extends Sequent α where
  level : Fin 3
notation:50 Γ:51 " ⟹[" l "] " Δ:51 => ThreeLayeredSequent.mk (Γ ⟹ Δ) l

/--
  Sequent calculus `D³_seq` for the provability logic `D`, with levels `l : Fin 3`. Level `0`
  matches `LogicGL.ProofGentzen`; level `1` matches `LogicS.ProofGentzen` at level `1`; level
  `2` is reachable only from boxed S-sequents via `liftUpBox`.

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

scoped prefix:120 "⊢ᵍ[D]! " => ProofGentzen

abbrev ProvableGentzen (S : ThreeLayeredSequent α) : Prop := Nonempty (⊢ᵍ[D]! S)
scoped prefix:120 "⊢ᵍ[D] " => ProvableGentzen

/-- Embed a level-0 `LogicGL` proof into level-0 `LogicD`.

  - [KKIM25, Theorem 4.1]
-/
def ofProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[GL]! (Γ ⟹ Δ) → ⊢ᵍ[D]! (Γ ⟹[0] Δ)
| .axm A      => .axm 0 A
| .botL       => .botL 0
| .wkL h h'   => .wkL (ofProofGentzen h) h'
| .wkR h h'   => .wkR (ofProofGentzen h) h'
| .impL h₁ h₂ => .impL (ofProofGentzen h₁) (ofProofGentzen h₂)
| .impR h     => .impR (ofProofGentzen h)
| .boxGL h    => .boxGL (ofProofGentzen h)

/-- Extract a level-0 `LogicGL` proof from level-0 `LogicD`. -/
def toProofGentzen {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[0] Δ) → ⊢ᵍ[GL]! (Γ ⟹ Δ)
| .axm 0 A    => .axm A
| .botL 0     => .botL
| .wkL h h'   => .wkL (toProofGentzen h) h'
| .wkR h h'   => .wkR (toProofGentzen h) h'
| .impL h₁ h₂ => .impL (toProofGentzen h₁) (toProofGentzen h₂)
| .impR h     => .impR (toProofGentzen h)
| .boxGL h    => .boxGL (toProofGentzen h)

/-- Level-`0` `LogicD.ProvableGentzen`-provability is exactly (plain, cut-free) `GL`-provability.

  - [KKIM25, Theorem 4.1]
-/
theorem iff_provableGentzen_provable_zero {Γ Δ : FormulaFinset α} :
  (⊢ᵍ[GL] (Γ ⟹ Δ)) ↔ (⊢ᵍ[D] (Γ ⟹[0] Δ)) :=
  ⟨λ ⟨h⟩ => ⟨ofProofGentzen h⟩, λ ⟨h⟩ => ⟨toProofGentzen h⟩⟩

/-- Embed a level-1 `LogicS` proof into level-1 `LogicD`.

  - [KKIM25, Theorem 4.2]
-/
def ofProofGentzenS {Γ Δ : FormulaFinset α} : ⊢ᵍ[S]! (Γ ⟹[1] Δ) → ⊢ᵍ[D]! (Γ ⟹[1] Δ)
| .axm 1 A    => .axm 1 A
| .botL 1     => .botL 1
| .wkL h h'   => .wkL (ofProofGentzenS h) h'
| .wkR h h'   => .wkR (ofProofGentzenS h) h'
| .impL h₁ h₂ => .impL (ofProofGentzenS h₁) (ofProofGentzenS h₂)
| .impR h     => .impR (ofProofGentzenS h)
| .liftUp h   => .liftUp (ofProofGentzen (LogicS.toProofGentzen h))
| .boxL h     => .boxL (ofProofGentzenS h)

/-- Extract a level-1 `LogicS` proof from level-1 `LogicD`. -/
def toProofGentzenS {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[1] Δ) → ⊢ᵍ[S]! (Γ ⟹[1] Δ)
| .axm 1 A    => .axm 1 A
| .botL 1     => .botL 1
| .wkL h h'   => .wkL (toProofGentzenS h) h'
| .wkR h h'   => .wkR (toProofGentzenS h) h'
| .impL h₁ h₂ => .impL (toProofGentzenS h₁) (toProofGentzenS h₂)
| .impR h     => .impR (toProofGentzenS h)
| .liftUp h   => .liftUp (LogicS.ofProofGentzen (toProofGentzen h))
| .boxL h     => .boxL (toProofGentzenS h)

/-- Level-`1` `LogicD.ProvableGentzen`-provability is exactly level-`1` `LogicS.ProvableGentzen`-provability.

  - [KKIM25, Theorem 4.2]
-/
theorem iff_provableGentzenS_provable_one {Γ Δ : FormulaFinset α} :
  (⊢ᵍ[S] (Γ ⟹[1] Δ)) ↔ (⊢ᵍ[D] (Γ ⟹[1] Δ)) :=
  ⟨λ ⟨h⟩ => ⟨ofProofGentzenS h⟩, λ ⟨h⟩ => ⟨toProofGentzenS h⟩⟩

namespace ProofGentzen

/-- Lift a level-`0` `LogicD.ProofGentzen`-proof to level `2`, by applying `(GLtoS)` and
  `(StoD)` at the `(GL□)` step and recursing through the other rules.

  - [KKIM25, Theorem 4.3]
-/
def liftUpTwo {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[0] Δ) → ⊢ᵍ[D]! (Γ ⟹[2] Δ)
| .axm 0 A      => .axm 2 A
| .botL 0       => .botL 2
| .wkL h h'     => .wkL (liftUpTwo h) h'
| .wkR h h'     => .wkR (liftUpTwo h) h'
| .impL h₁ h₂   => .impL (liftUpTwo h₁) (liftUpTwo h₂)
| .impR h       => .impR (liftUpTwo h)
| .boxGL (Γ := Γ) (A := A) π => by
    have h := ProofGentzen.liftUp (ProofGentzen.boxGL π);
    rw [(show ({□A} : FormulaFinset α) = ({A} : FormulaFinset α).box by grind)] at h ⊢;
    exact ProofGentzen.liftUpBox h;

end ProofGentzen

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {l : Fin 3}

lemma axm (l) (A : Formula α) : ⊢ᵍ[D] ({A} ⟹[l] {A}) := ⟨ProofGentzen.axm l A⟩
lemma botL (l) : ⊢ᵍ[D] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨ProofGentzen.botL l⟩
lemma wkL (π : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ[D] (Γ' ⟹[l] Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ[D] (Γ ⟹[l] Δ') := ⟨ProofGentzen.wkR π.some h⟩
lemma impL (π₁ : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) (π₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[D] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᵍ[D] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍ[D] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩
lemma liftUp (π : ⊢ᵍ[D] (Γ ⟹[0] Δ)) : ⊢ᵍ[D] (Γ ⟹[1] Δ) := ⟨ProofGentzen.liftUp π.some⟩
lemma boxGL (π : ⊢ᵍ[D] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})) : ⊢ᵍ[D] (Γ.box ⟹[0] {□A}) := ⟨ProofGentzen.boxGL π.some⟩
lemma boxL (π : ⊢ᵍ[D] (insert A Γ ⟹[1] Δ)) : ⊢ᵍ[D] (insert (□A) Γ ⟹[1] Δ) := ⟨ProofGentzen.boxL π.some⟩
lemma liftUpBox {Γ Δ : FormulaFinset α} (π : ⊢ᵍ[D] (Γ.box ⟹[1] Δ.box)) : ⊢ᵍ[D] (Γ.box ⟹[2] Δ.box) := ⟨ProofGentzen.liftUpBox π.some⟩

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
  : ∀ {S : ThreeLayeredSequent α} (h : ⊢ᵍ[D] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

scoped prefix:120 "⊬ᵍ[D] " => (¬ ProvableGentzen ·)

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : ThreeLayeredSequent α} : (⊬ᵍ[D] S) ↔ (IsEmpty (⊢ᵍ[D]! S)) := by
  simp [ProvableGentzen];

/-- Initial sequents with side formulas, at any level. -/
lemma union (l) (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[D] (Γ ⟹[l] Δ) :=
  wkR (wkL (axm l A) (by grind)) (by grind)

lemma union' (l) (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ[D] (S.ant ⟹[l] S.suc) :=
  union l A hΓ hΔ

lemma botL_mem (l) (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[D] (Γ ⟹[l] Δ) :=
  wkR (Δ := ∅) (wkL (botL l) (by grind)) (by grind)

lemma not_provable_zero_of_not_provable_one : ⊬ᵍ[D] (Γ ⟹[1] Δ) → ⊬ᵍ[D] (Γ ⟹[0] Δ) := by
  contrapose!;
  apply liftUp;

/-- Disjunction left, the derived rule for the abbreviation `A ⋎ B := ∼A 🡒 B`. -/
lemma orL (π₁ : ⊢ᵍ[D] (insert A Γ ⟹[l] Δ)) (π₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[D] (insert (A ⋎ B) Γ ⟹[l] Δ) :=
  impL (impR (wkR π₁ (by grind))) π₂

/-- Disjunction right, the derived rule for the abbreviation `A ⋎ B := ∼A 🡒 B`. -/
lemma orR (π : ⊢ᵍ[D] (Γ ⟹[l] (insert A (insert B Δ)))) : ⊢ᵍ[D] (Γ ⟹[l] insert (A ⋎ B) Δ) :=
  impR (impL π (botL_mem l))

/-- Negation left, the derived rule for the abbreviation `∼A := A 🡒 ⊥`. -/
lemma negL (π : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) : ⊢ᵍ[D] (insert (∼A) Γ ⟹[l] Δ) :=
  impL π (botL_mem l)

/-- Negation right, the derived rule for the abbreviation `∼A := A 🡒 ⊥`. -/
lemma negR (π : ⊢ᵍ[D] (insert A Γ ⟹[l] Δ)) : ⊢ᵍ[D] (Γ ⟹[l] insert (∼A) Δ) :=
  impR (wkR π (by grind))

/-- `Prop`-level version of `LogicD.ProofGentzen.liftUpTwo`. -/
lemma liftUpTwo (π : ⊢ᵍ[D] (Γ ⟹[0] Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) := ⟨ProofGentzen.liftUpTwo π.some⟩

/--
  The `D³_seq`-provability of the axiom `□(□A ⋎ □B) 🡒 (□A ⋎ □B)`.

  - [KKIM25, Example 3.2]
-/
lemma axiomD {A B : Formula α} : ⊢ᵍ[D] (∅ ⟹[2] {□(□A ⋎ □B) 🡒 (□A ⋎ □B)}) := by
  have h₁ : ⊢ᵍ[D] (({□A}) ⟹[1] {□A, □B}) := union 1 (□A);
  have h₂ : ⊢ᵍ[D] (({□B}) ⟹[1] {□A, □B}) := union 1 (□B);
  have h₃ : ⊢ᵍ[D] (({□A ⋎ □B} : FormulaFinset α) ⟹[1] {□A, □B}) := orL (Γ := ∅) h₁ h₂;
  have h₄ : ⊢ᵍ[D] (({□(□A ⋎ □B)} : FormulaFinset α) ⟹[1] {□A, □B}) := boxL (A := □A ⋎ □B) (Γ := ∅) h₃;
  rw [(show ({□(□A ⋎ □B)} : FormulaFinset α) = ({□A ⋎ □B} : FormulaFinset α).box by grind),
    (show ({□A, □B} : FormulaFinset α) = ({A, B} : FormulaFinset α).box by grind)] at h₄;
  have h₅ := liftUpBox h₄;
  rw [(show ({□A ⋎ □B} : FormulaFinset α).box = ({□(□A ⋎ □B)} : FormulaFinset α) by grind),
    (show ({A, B} : FormulaFinset α).box = ({□A, □B} : FormulaFinset α) by grind)] at h₅;
  exact impR (orR (Δ := ∅) h₅);

/--
  The `D³_seq`-provability of `∼□⊥`, the `D³_seq` adaptation of the `D²_seq`-proof
  given in the source (there stated with `(GLtoD)`, which `D³_seq` does not have).

  - [KKIM25, Example 3.3]
-/
lemma axiomP : ⊢ᵍ[D] ((∅ : FormulaFinset α) ⟹[2] {∼□⊥}) := by
  have h₁ : ⊢ᵍ[D] (({⊥} : FormulaFinset α) ⟹[1] ∅) := botL 1;
  have h₂ : ⊢ᵍ[D] (({□⊥} : FormulaFinset α) ⟹[1] ∅) := boxL (A := ⊥) (Γ := ∅) h₁;
  rw [(show ({□(⊥ : Formula α)} : FormulaFinset α) = ({⊥} : FormulaFinset α).box by grind),
    (show (∅ : FormulaFinset α) = (∅ : FormulaFinset α).box by grind)] at h₂;
  have h₃ := liftUpBox h₂;
  rw [(show ({⊥} : FormulaFinset α).box = ({□(⊥ : Formula α)} : FormulaFinset α) by grind),
    (show (∅ : FormulaFinset α).box = (∅ : FormulaFinset α) by grind)] at h₃;
  exact negR (Δ := ∅) h₃;

end ProvableGentzen

open ProvableGentzen

/--
  Every `GL_seq`-proof lifts to a `D³_seq`-proof of the same sequent at the top D-sequent level.

  - [KKIM25, Theorem 4.3]
-/
theorem provable_two_of_provableGentzen_GL {Γ Δ : FormulaFinset α} (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) :=
  ProvableGentzen.liftUpTwo ⟨ofProofGentzen h.some⟩

/--
  Every `GL_seq`-proof lifts to a `D³_seq`-proof of the same sequent at the S-sequent level.

  - [KKIM25, Theorem 4.3]
-/
theorem provable_one_of_provableGentzen_GL {Γ Δ : FormulaFinset α} (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) : ⊢ᵍ[D] (Γ ⟹[1] Δ) :=
  ProvableGentzen.liftUp ⟨ofProofGentzen h.some⟩

end LogicD

end
