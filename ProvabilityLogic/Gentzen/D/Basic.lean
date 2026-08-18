module

public import ProvabilityLogic.Gentzen.S.Basic

/-!
The cut-free sequent calculus for the provability logic `D`.

`LogicD.ProofGentzen` is a single inductive on `ThreeLayeredSequent`, a `Sequent` tagged with
a level `l : Fin 3`: `l = 0` is the GL-sequent, `l = 1` is the S-sequent, and `l = 2` is the
D-sequent. The constructors encode the source's modal rules `(GL□)` (`boxGL`), `(GLtoS)`
(`liftUp₀₁`), `(S□left)` (`boxL`), and `(StoD)` (`liftUp₁₂`).
-/

@[expose]
public section

open LogicGL
open scoped LogicS
open scoped FormulaFinset

variable {α : Type u} [DecidableEq α]

/-- A `Sequent` with a level `l : Fin 3`, used in the three-level sequent calculus for `D`.

  - [KKIM25, §3]
-/
structure ThreeLayeredSequent (α : Type u) extends Sequent α where
  level : Fin 3
notation:50 Γ:51 " ⟹[" l "] " Δ:51 => ThreeLayeredSequent.mk (Γ ⟹ Δ) l

/--
  The sequent calculus for the provability logic `D`, with levels `l : Fin 3`. Level `0`
  matches `LogicGL.ProofGentzen`; level `1` matches `LogicS.ProofGentzen` at level `1`; level
  `2` is reachable only from boxed S-sequents via `liftUp₁₂`.

  - [KKIM25, §3, "D³seq"]
-/
inductive LogicD.ProofGentzen : ThreeLayeredSequent α → Type u
| axm (l) (A)      : ProofGentzen ({A} ⟹[l] {A})
| botL (l)         : ProofGentzen ({⊥} ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : ProofGentzen (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : ProofGentzen (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : ProofGentzen (Γ ⟹[l] (insert A Δ)) → ProofGentzen (insert B Γ ⟹[l] Δ) → ProofGentzen ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹[l] (insert B Δ)) → ProofGentzen (Γ ⟹[l] (insert (A 🡒 B) Δ))
| boxGL {Γ : FormulaFinset α} {A} : ProofGentzen ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A}) → ProofGentzen (□Γ ⟹[0] {□A})
| liftUp₀₁ {Γ Δ}   : ProofGentzen (Γ ⟹[0] Δ) → ProofGentzen (Γ ⟹[1] Δ)
| boxL {Γ Δ A}     : ProofGentzen (insert A Γ ⟹[1] Δ) → ProofGentzen (insert (□A) Γ ⟹[1] Δ)
| liftUp₁₂ {Γ Δ : FormulaFinset α} : ProofGentzen (□Γ ⟹[1] □Δ) → ProofGentzen (□Γ ⟹[2] □Δ)

namespace LogicD

scoped prefix:120 "⊢ᵍ[D]! " => ProofGentzen

abbrev ProvableGentzen (S : ThreeLayeredSequent α) : Prop := Nonempty (⊢ᵍ[D]! S)
scoped prefix:120 "⊢ᵍ[D] " => ProvableGentzen

variable {Γ Δ : FormulaFinset α}

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
theorem iff_provableGentzen_provable_0 :
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
| .liftUp h   => .liftUp₀₁ (ofProofGentzen (LogicS.toProofGentzen h))
| .boxL h     => .boxL (ofProofGentzenS h)

/-- Extract a level-1 `LogicS` proof from level-1 `LogicD`. -/
def toProofGentzenS {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[1] Δ) → ⊢ᵍ[S]! (Γ ⟹[1] Δ)
| .axm 1 A    => .axm 1 A
| .botL 1     => .botL 1
| .wkL h h'   => .wkL (toProofGentzenS h) h'
| .wkR h h'   => .wkR (toProofGentzenS h) h'
| .impL h₁ h₂ => .impL (toProofGentzenS h₁) (toProofGentzenS h₂)
| .impR h     => .impR (toProofGentzenS h)
| .liftUp₀₁ h => .liftUp (LogicS.ofProofGentzen (toProofGentzen h))
| .boxL h     => .boxL (toProofGentzenS h)

/-- Level-`1` `LogicD.ProvableGentzen`-provability is exactly level-`1` `LogicS.ProvableGentzen`-provability.

  - [KKIM25, Theorem 4.2]
-/
theorem iff_provableGentzenS_provable_1 :
  (⊢ᵍ[S] (Γ ⟹[1] Δ)) ↔ (⊢ᵍ[D] (Γ ⟹[1] Δ)) :=
  ⟨λ ⟨h⟩ => ⟨ofProofGentzenS h⟩, λ ⟨h⟩ => ⟨toProofGentzenS h⟩⟩

namespace ProofGentzen

/-- Lift a level-`0` `LogicD.ProofGentzen`-proof to level `2`.

  - [KKIM25, Theorem 4.3]
-/
def liftUp₀₂ {Γ Δ : FormulaFinset α} : ⊢ᵍ[D]! (Γ ⟹[0] Δ) → ⊢ᵍ[D]! (Γ ⟹[2] Δ)
| .axm 0 A      => .axm 2 A
| .botL 0       => .botL 2
| .wkL h h'     => .wkL (liftUp₀₂ h) h'
| .wkR h h'     => .wkR (liftUp₀₂ h) h'
| .impL h₁ h₂   => .impL (liftUp₀₂ h₁) (liftUp₀₂ h₂)
| .impR h       => .impR (liftUp₀₂ h)
| .boxGL (Γ := Γ) (A := A) π => by
    have h := ProofGentzen.liftUp₀₁ (ProofGentzen.boxGL π);
    rw [(show ({□A} : FormulaFinset α) = □({A} : FormulaFinset α) by grind)] at h ⊢;
    exact ProofGentzen.liftUp₁₂ h;

end ProofGentzen

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α} {l : Fin 3}

lemma axm (l) (A : Formula α) : ⊢ᵍ[D] ({A} ⟹[l] {A}) := ⟨ProofGentzen.axm l A⟩
lemma botL (l) : ⊢ᵍ[D] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨ProofGentzen.botL l⟩
lemma wkL (h : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (hΓ : Γ ⊆ Γ') : ⊢ᵍ[D] (Γ' ⟹[l] Δ) := ⟨ProofGentzen.wkL h.some hΓ⟩
lemma wkR (h : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (hΔ : Δ ⊆ Δ') : ⊢ᵍ[D] (Γ ⟹[l] Δ') := ⟨ProofGentzen.wkR h.some hΔ⟩
lemma impL (h₁ : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[D] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨ProofGentzen.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍ[D] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍ[D] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR h.some⟩
lemma liftUp₀₁ (h : ⊢ᵍ[D] (Γ ⟹[0] Δ)) : ⊢ᵍ[D] (Γ ⟹[1] Δ) := ⟨ProofGentzen.liftUp₀₁ h.some⟩
lemma boxGL (h : ⊢ᵍ[D] ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A})) : ⊢ᵍ[D] (□Γ ⟹[0] {□A}) := ⟨ProofGentzen.boxGL h.some⟩
lemma boxL (h : ⊢ᵍ[D] (insert A Γ ⟹[1] Δ)) : ⊢ᵍ[D] (insert (□A) Γ ⟹[1] Δ) := ⟨ProofGentzen.boxL h.some⟩
lemma liftUp₁₂ (h : ⊢ᵍ[D] (□Γ ⟹[1] □Δ)) : ⊢ᵍ[D] (□Γ ⟹[2] □Δ) := ⟨ProofGentzen.liftUp₁₂ h.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : ThreeLayeredSequent α) → ⊢ᵍ[D] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (ProvableGentzen.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (ProvableGentzen.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (h : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (hΓ : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) h → motive (Γ' ⟹[l] Δ) (wkL h hΓ))
  (wkR : ∀ {l Γ Δ Δ'} (h : ⊢ᵍ[D] (Γ ⟹[l] Δ)) (hΔ : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) h → motive (Γ ⟹[l] Δ') (wkR h hΔ))
  (impL : ∀ {l Γ Δ A B} (h₁ : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) h₁ → motive (insert B Γ ⟹[l] Δ) h₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL h₁ h₂)
  )
  (impR : ∀ {l Γ Δ A B} (h : ⊢ᵍ[D] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) h → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR h)
  )
  (liftUp₀₁ : ∀ {Γ Δ} (h : ⊢ᵍ[D] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) h → motive (Γ ⟹[1] Δ) (liftUp₀₁ h))
  (boxGL : ∀ {Γ : FormulaFinset α} {A} (h : ⊢ᵍ[D] ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A}) h → motive (□Γ ⟹[0] {□A}) (boxGL h)
  )
  (boxL : ∀ {Γ Δ A} (h : ⊢ᵍ[D] (insert A Γ ⟹[1] Δ)),
    motive (insert A Γ ⟹[1] Δ) h → motive (insert (□A) Γ ⟹[1] Δ) (boxL h)
  )
  (liftUp₁₂ : ∀ {Γ Δ : FormulaFinset α} (h : ⊢ᵍ[D] (□Γ ⟹[1] □Δ)),
    motive (□Γ ⟹[1] □Δ) h → motive (□Γ ⟹[2] □Δ) (liftUp₁₂ h)
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

lemma not_provable_0_of_not_provable_1 : ⊬ᵍ[D] (Γ ⟹[1] Δ) → ⊬ᵍ[D] (Γ ⟹[0] Δ) := by
  contrapose!;
  apply liftUp₀₁;

/-- Disjunction left, the derived rule for the abbreviation `A ⋎ B := ∼A 🡒 B`. -/
lemma orL (h₁ : ⊢ᵍ[D] (insert A Γ ⟹[l] Δ)) (h₂ : ⊢ᵍ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍ[D] (insert (A ⋎ B) Γ ⟹[l] Δ) :=
  impL (impR (wkR h₁ (by grind))) h₂

/-- Disjunction right, the derived rule for the abbreviation `A ⋎ B := ∼A 🡒 B`. -/
lemma orR (h : ⊢ᵍ[D] (Γ ⟹[l] (insert A (insert B Δ)))) : ⊢ᵍ[D] (Γ ⟹[l] insert (A ⋎ B) Δ) :=
  impR (impL h (botL_mem l))

/-- Negation left, the derived rule for the abbreviation `∼A := A 🡒 ⊥`. -/
lemma negL (h : ⊢ᵍ[D] (Γ ⟹[l] insert A Δ)) : ⊢ᵍ[D] (insert (∼A) Γ ⟹[l] Δ) :=
  impL h (botL_mem l)

/-- Negation right, the derived rule for the abbreviation `∼A := A 🡒 ⊥`. -/
lemma negR (h : ⊢ᵍ[D] (insert A Γ ⟹[l] Δ)) : ⊢ᵍ[D] (Γ ⟹[l] insert (∼A) Δ) :=
  impR (wkR h (by grind))

/-- `Prop`-level version of `LogicD.ProofGentzen.liftUp₀₂`. -/
lemma liftUp₀₂ (h : ⊢ᵍ[D] (Γ ⟹[0] Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) := ⟨ProofGentzen.liftUp₀₂ h.some⟩

/--
  `LogicD.ProvableGentzen`-provability of the axiom `□(□A ⋎ □B) 🡒 (□A ⋎ □B)`.

  - [KKIM25, Example 3.2]
-/
lemma axiomD {A B : Formula α} : ⊢ᵍ[D] (∅ ⟹[2] {□(□A ⋎ □B) 🡒 (□A ⋎ □B)}) := by
  have h₁ : ⊢ᵍ[D] ({□A} ⟹[1] {□A, □B}) := union 1 (□A);
  have h₂ : ⊢ᵍ[D] ({□B} ⟹[1] {□A, □B}) := union 1 (□B);
  have h₃ : ⊢ᵍ[D] ({□A ⋎ □B} ⟹[1] {□A, □B}) := orL (Γ := ∅) h₁ h₂;
  have h₄ : ⊢ᵍ[D] ({□(□A ⋎ □B)} ⟹[1] {□A, □B}) := boxL (A := □A ⋎ □B) (Γ := ∅) h₃;
  rw [
    (show ({□(□A ⋎ □B)}) = □({□A ⋎ □B} : FormulaFinset α) by grind),
    (show ({□A, □B}) = □({A, B} : FormulaFinset α) by grind)
  ] at h₄;
  have h₅ := liftUp₁₂ h₄;
  rw [
    (show □({□A ⋎ □B} : FormulaFinset α) = {□(□A ⋎ □B)} by grind),
    (show □({A, B} : FormulaFinset α) = {□A, □B} by grind)
  ] at h₅;
  exact impR (orR (Δ := ∅) h₅);

/--
  `LogicD.ProvableGentzen`-provability of `∼□⊥`. The source proves this in its
  two-sequent calculus, using a rule this three-level calculus does not have.

  - [KKIM25, Example 3.3]
-/
lemma axiomP : ⊢ᵍ[D] ((∅ : FormulaFinset α) ⟹[2] {∼□⊥}) := by
  have h₁ : ⊢ᵍ[D] (({⊥} : FormulaFinset α) ⟹[1] ∅) := botL 1;
  have h₂ : ⊢ᵍ[D] ({□⊥} ⟹[1] ∅) := boxL (A := ⊥) (Γ := ∅) h₁;
  rw [
    (show ({□(⊥ : Formula α)} : FormulaFinset α) = □({⊥} : FormulaFinset α) by grind),
    (show ∅ = □(∅ : FormulaFinset α) by grind)
  ] at h₂;
  have h₃ := liftUp₁₂ h₂;
  rw [
    (show □({⊥} : FormulaFinset α) = ({□(⊥ : Formula α)} : FormulaFinset α) by grind),
    (show □(∅ : FormulaFinset α) = ∅ by grind)
  ] at h₃;
  exact negR (Δ := ∅) h₃;

end ProvableGentzen

open ProvableGentzen

variable {Γ Δ : FormulaFinset α}

/--
  Every `LogicGL.ProvableGentzen`-proof lifts to a `LogicD.ProvableGentzen`-proof of the same
  sequent at the top D-sequent level.

  - [KKIM25, Theorem 4.3]
-/
theorem provable_2_of_provableGentzen_GL (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) :=
  ProvableGentzen.liftUp₀₂ ⟨ofProofGentzen h.some⟩

/--
  Every `LogicGL.ProvableGentzen`-proof lifts to a `LogicD.ProvableGentzen`-proof of the same
  sequent at the S-sequent level.

  - [KKIM25, Theorem 4.3]
-/
theorem provable_1_of_provableGentzen_GL (h : ⊢ᵍ[GL] (Γ ⟹ Δ)) : ⊢ᵍ[D] (Γ ⟹[1] Δ) :=
  ProvableGentzen.liftUp₀₁ ⟨ofProofGentzen h.some⟩

end LogicD

/-- `LogicD.ProofGentzen` with a level-preserving cut rule.

  - [KKIM25, §3]
-/
inductive LogicD.GentzenWithCutProof : ThreeLayeredSequent α → Type u
| axm (l) (A)      : GentzenWithCutProof ({A} ⟹[l] {A})
| botL (l)         : GentzenWithCutProof ({⊥} ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → GentzenWithCutProof (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → GentzenWithCutProof (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : GentzenWithCutProof (Γ ⟹[l] (insert A Δ)) → GentzenWithCutProof (insert B Γ ⟹[l] Δ) → GentzenWithCutProof ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : GentzenWithCutProof ((insert A Γ) ⟹[l] (insert B Δ)) → GentzenWithCutProof (Γ ⟹[l] (insert (A 🡒 B) Δ))
| boxGL {Γ : FormulaFinset α} {A} : GentzenWithCutProof ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A}) → GentzenWithCutProof (□Γ ⟹[0] {□A})
| liftUp₀₁ {Γ Δ}   : GentzenWithCutProof (Γ ⟹[0] Δ) → GentzenWithCutProof (Γ ⟹[1] Δ)
| boxL {Γ Δ A}     : GentzenWithCutProof (insert A Γ ⟹[1] Δ) → GentzenWithCutProof (insert (□A) Γ ⟹[1] Δ)
| liftUp₁₂ {Γ Δ : FormulaFinset α} : GentzenWithCutProof (□Γ ⟹[1] □Δ) → GentzenWithCutProof (□Γ ⟹[2] □Δ)
| cut  {l Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹[l] insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹[l] Δ₂) → GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂)

namespace LogicD

scoped prefix:120 "⊢ᵍᶜ[D]! " => GentzenWithCutProof

abbrev GentzenWithCutProvable (S : ThreeLayeredSequent α) : Prop := Nonempty (⊢ᵍᶜ[D]! S)
scoped prefix:120 "⊢ᵍᶜ[D] " => GentzenWithCutProvable

def GentzenWithCutProof.ofProofGentzen {S : ThreeLayeredSequent α} : ⊢ᵍ[D]! S → ⊢ᵍᶜ[D]! S
| .axm l A    => .axm l A
| .botL l     => .botL l
| .wkL h h'   => .wkL (GentzenWithCutProof.ofProofGentzen h) h'
| .wkR h h'   => .wkR (GentzenWithCutProof.ofProofGentzen h) h'
| .impL h₁ h₂ => .impL (GentzenWithCutProof.ofProofGentzen h₁) (GentzenWithCutProof.ofProofGentzen h₂)
| .impR h     => .impR (GentzenWithCutProof.ofProofGentzen h)
| .boxGL h    => .boxGL (GentzenWithCutProof.ofProofGentzen h)
| .liftUp₀₁ h => .liftUp₀₁ (GentzenWithCutProof.ofProofGentzen h)
| .boxL h     => .boxL (GentzenWithCutProof.ofProofGentzen h)
| .liftUp₁₂ h => .liftUp₁₂ (GentzenWithCutProof.ofProofGentzen h)

/-- The with-cut variant of `LogicD.toProofGentzenS`, at level `0`.

  - [KKIM25, Theorem 4.2]
-/
def GentzenWithCutProof.toGentzenWithCutProofS₀ {Γ Δ : FormulaFinset α} : ⊢ᵍᶜ[D]! (Γ ⟹[0] Δ) → ⊢ᵍᶜ[S]! (Γ ⟹[0] Δ)
| .axm 0 A    => .axm 0 A
| .botL 0     => .botL 0
| .wkL h h'   => .wkL (GentzenWithCutProof.toGentzenWithCutProofS₀ h) h'
| .wkR h h'   => .wkR (GentzenWithCutProof.toGentzenWithCutProofS₀ h) h'
| .impL h₁ h₂ => .impL (GentzenWithCutProof.toGentzenWithCutProofS₀ h₁) (GentzenWithCutProof.toGentzenWithCutProofS₀ h₂)
| .impR h     => .impR (GentzenWithCutProof.toGentzenWithCutProofS₀ h)
| .boxGL h    => .boxGL (GentzenWithCutProof.toGentzenWithCutProofS₀ h)
| .cut h₁ h₂  => .cut (GentzenWithCutProof.toGentzenWithCutProofS₀ h₁) (GentzenWithCutProof.toGentzenWithCutProofS₀ h₂)

/-- The with-cut variant of `LogicD.toProofGentzenS`, at level `1`. This is the bridge that lets
  soundness for level-`2` `LogicD.GentzenWithCutProof` reuse `LogicS.GentzenWithCutProvable.soundness`
  wholesale.

  - [KKIM25, Theorem 4.2]
-/
def GentzenWithCutProof.toGentzenWithCutProofS₁ {Γ Δ : FormulaFinset α} : ⊢ᵍᶜ[D]! (Γ ⟹[1] Δ) → ⊢ᵍᶜ[S]! (Γ ⟹[1] Δ)
| .axm 1 A    => .axm 1 A
| .botL 1     => .botL 1
| .wkL h h'   => .wkL (GentzenWithCutProof.toGentzenWithCutProofS₁ h) h'
| .wkR h h'   => .wkR (GentzenWithCutProof.toGentzenWithCutProofS₁ h) h'
| .impL h₁ h₂ => .impL (GentzenWithCutProof.toGentzenWithCutProofS₁ h₁) (GentzenWithCutProof.toGentzenWithCutProofS₁ h₂)
| .impR h     => .impR (GentzenWithCutProof.toGentzenWithCutProofS₁ h)
| .liftUp₀₁ h => .liftUp (GentzenWithCutProof.toGentzenWithCutProofS₀ h)
| .boxL h     => .boxL (GentzenWithCutProof.toGentzenWithCutProofS₁ h)
| .cut h₁ h₂  => .cut (GentzenWithCutProof.toGentzenWithCutProofS₁ h₁) (GentzenWithCutProof.toGentzenWithCutProofS₁ h₂)

namespace GentzenWithCutProvable

variable {S : ThreeLayeredSequent α} {Γ Γ' Δ Δ' Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A B : Formula α} {l : Fin 3}

/-- Cut-free `LogicD` provability implies `LogicD.GentzenWithCutProof` provability.

  - [KKIM25, §3]
-/
theorem of_without_cut : ⊢ᵍ[D] S → ⊢ᵍᶜ[D] S := λ ⟨h⟩ => ⟨GentzenWithCutProof.ofProofGentzen h⟩

lemma axm (l) (A : Formula α) : ⊢ᵍᶜ[D] ({A} ⟹[l] {A}) := ⟨GentzenWithCutProof.axm l A⟩
lemma botL (l) : ⊢ᵍᶜ[D] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨GentzenWithCutProof.botL l⟩
lemma wkL (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ') : ⊢ᵍᶜ[D] (Γ' ⟹[l] Δ) := ⟨GentzenWithCutProof.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ') : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ') := ⟨GentzenWithCutProof.wkR h.some h'⟩
lemma impL (h₁ : ⊢ᵍᶜ[D] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍᶜ[D] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨GentzenWithCutProof.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ[D] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍᶜ[D] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨GentzenWithCutProof.impR h.some⟩
lemma liftUp₀₁ (h : ⊢ᵍᶜ[D] (Γ ⟹[0] Δ)) : ⊢ᵍᶜ[D] (Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.liftUp₀₁ h.some⟩
lemma boxGL (h : ⊢ᵍᶜ[D] ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A})) : ⊢ᵍᶜ[D] (□Γ ⟹[0] {□A}) := ⟨GentzenWithCutProof.boxGL h.some⟩
lemma boxL (h : ⊢ᵍᶜ[D] (insert A Γ ⟹[1] Δ)) : ⊢ᵍᶜ[D] (insert (□A) Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.boxL h.some⟩
lemma liftUp₁₂ (h : ⊢ᵍᶜ[D] (□Γ ⟹[1] □Δ)) : ⊢ᵍᶜ[D] (□Γ ⟹[2] □Δ) := ⟨GentzenWithCutProof.liftUp₁₂ h.some⟩

lemma cut (h₁ : ⊢ᵍᶜ[D] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[D] (insert A Γ₂ ⟹[l] Δ₂)) : ⊢ᵍᶜ[D] (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) :=
  ⟨GentzenWithCutProof.cut h₁.some h₂.some⟩

/-- `Prop`-level version of `LogicD.GentzenWithCutProof.toGentzenWithCutProofS₁`.

  - [KKIM25, Theorem 4.2]
-/
theorem toGentzenWithCutProvableS (h : ⊢ᵍᶜ[D] (Γ ⟹[1] Δ)) : ⊢ᵍᶜ[S] (Γ ⟹[1] Δ) :=
  ⟨GentzenWithCutProof.toGentzenWithCutProofS₁ h.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : ThreeLayeredSequent α) → ⊢ᵍᶜ[D] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (GentzenWithCutProvable.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (GentzenWithCutProvable.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) h → motive (Γ' ⟹[l] Δ) (wkL h h'))
  (wkR : ∀ {l Γ Δ Δ'} (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) h → motive (Γ ⟹[l] Δ') (wkR h h'))
  (impL : ∀ {l Γ Δ A B} (h₁ : ⊢ᵍᶜ[D] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[D] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) h₁ → motive (insert B Γ ⟹[l] Δ) h₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL h₁ h₂)
  )
  (impR : ∀ {l Γ Δ A B} (h : ⊢ᵍᶜ[D] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) h → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR h)
  )
  (liftUp₀₁ : ∀ {Γ Δ} (h : ⊢ᵍᶜ[D] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) h → motive (Γ ⟹[1] Δ) (liftUp₀₁ h))
  (boxGL : ∀ {Γ : FormulaFinset α} {A} (h : ⊢ᵍᶜ[D] ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ □Γ)) ⟹[0] {A}) h → motive (□Γ ⟹[0] {□A}) (boxGL h)
  )
  (boxL : ∀ {Γ Δ A} (h : ⊢ᵍᶜ[D] (insert A Γ ⟹[1] Δ)),
    motive (insert A Γ ⟹[1] Δ) h → motive (insert (□A) Γ ⟹[1] Δ) (boxL h)
  )
  (liftUp₁₂ : ∀ {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[D] (□Γ ⟹[1] □Δ)),
    motive (□Γ ⟹[1] □Δ) h → motive (□Γ ⟹[2] □Δ) (liftUp₁₂ h)
  )
  (cut : ∀ {l Γ₁ Γ₂ Δ₁ Δ₂ A} (h₁ : ⊢ᵍᶜ[D] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[D] (insert A Γ₂ ⟹[l] Δ₂)),
    motive (Γ₁ ⟹[l] insert A Δ₁) h₁ → motive (insert A Γ₂ ⟹[l] Δ₂) h₂ →
    motive (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) (GentzenWithCutProvable.cut h₁ h₂)
  )
  : ∀ {S : ThreeLayeredSequent α} (h : ⊢ᵍᶜ[D] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

end GentzenWithCutProvable

end LogicD

end
