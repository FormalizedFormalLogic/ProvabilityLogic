module

public import ProvabilityLogic.ProvabilityLogic.Interpret

/-!
# The strong interpretation and the boxdot translation

Port of the `strongInterpret` portion of `Foundation.ProvabilityLogic.Grz.Completeness`, a file
that no longer exists upstream. This file provides the ground work — the strong interpretation
of a formula and its equivalence with the interpretation of the boxdot translate — on top of
which `ProvabilityLogic.ProvabilityLogic.Grz.Basic` builds the arithmetical completeness of the
modal logic `Grz`.

- [Gol78]
- [Boo80]
-/

@[expose] public section

open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
variable {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] {𝔅 : Provability T₀ T}

namespace Formula

omit [L.DecidableEq] in
/-- The strong interpretation sending `□A` to `(A.strongInterpret f) ⋏ 𝔅 (A.strongInterpret f)`
instead of `𝔅 (A.interpret f)`. -/
@[grind]
def strongInterpret (f : Realization α 𝔅) : Formula α → FirstOrder.Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => (A.strongInterpret f) 🡒 (B.strongInterpret f)
  | □A    => (A.strongInterpret f) ⋏ 𝔅 (A.strongInterpret f)

variable {f : Realization α 𝔅} {A : Formula α}

/-- The interpretation of the boxdot translate of `A` is `T`-provably equivalent to the strong
interpretation of `A`. -/
lemma iff_interpret_boxdot_strongInterpret_inside [𝔅.HBL2] :
  T ⊢ f (Aᵇ) 🡘 A.strongInterpret f := by
  induction A with
  | atom a => simp [Formula.interpret, strongInterpret, Formula.boxdotTranslate];
  | bot => simp only [Formula.boxdotTranslate, strongInterpret, Formula.interpret]; cl_prover;
  | imp A B ihA ihB =>
    simp only [Formula.boxdotTranslate, strongInterpret];
    exact ECC!_of_E!_of_E! ihA ihB;
  | box A ih =>
    simp only [Formula.boxdotTranslate, strongInterpret];
    apply E!_trans Formula.interpret_boxdot_inside;
    apply K!_intro;
    . apply CKK!_of_C!_of_C!;
      . cl_prover [ih];
      . apply WeakerThan.pbl (𝓢 := T₀);
        apply 𝔅.mono;
        cl_prover [ih];
    . apply CKK!_of_C!_of_C!;
      . cl_prover [ih];
      . apply WeakerThan.pbl (𝓢 := T₀);
        apply 𝔅.mono;
        cl_prover [ih];

/-- `T` proves the interpretation of the boxdot translate of `A` iff it proves the strong
interpretation of `A`. -/
lemma iff_interpret_boxdot_strongInterpret [𝔅.HBL2] :
  T ⊢ f (Aᵇ) ↔ T ⊢ A.strongInterpret f := by
  constructor;
  . intro h; exact (C_of_E_mp! iff_interpret_boxdot_strongInterpret_inside) ⨀ h;
  . intro h; exact (C_of_E_mpr! iff_interpret_boxdot_strongInterpret_inside) ⨀ h;

/-- A model of `T` satisfies the interpretation of the boxdot translate of `A` iff it satisfies
the strong interpretation of `A`. -/
lemma iff_models_interpret_boxdot_strongInterpret
  {M} [Nonempty M] [Structure L M] [M↓[L] ⊧* T] [𝔅.HBL2] [𝔅.SoundOn M] :
  M↓[L] ⊧ f (Aᵇ) ↔ M↓[L] ⊧ A.strongInterpret f := by
  induction A with
  | box A ih =>
    suffices (M↓[L] ⊧ f (Aᵇ)) ∧ (M↓[L] ⊧ 𝔅 (f (Aᵇ))) ↔
        (M↓[L] ⊧ A.strongInterpret f) ∧ (M↓[L] ⊧ 𝔅 (A.strongInterpret f)) by
      simpa [Formula.boxdotTranslate, Formula.interpret, strongInterpret] using this;
    constructor;
    . rintro ⟨h₁, h₂⟩;
      refine ⟨ih.mp h₁, ?_⟩;
      apply models_of_provable (T := T) inferInstance;
      apply WeakerThan.pbl (𝓢 := T₀);
      apply 𝔅.D1;
      exact iff_interpret_boxdot_strongInterpret.mp (𝔅.sound_on h₂);
    . rintro ⟨h₁, h₂⟩;
      refine ⟨ih.mpr h₁, ?_⟩;
      apply models_of_provable (T := T) inferInstance;
      apply WeakerThan.pbl (𝓢 := T₀);
      apply 𝔅.D1;
      exact iff_interpret_boxdot_strongInterpret.mpr (𝔅.sound_on h₂);
  | _ => simp_all [Formula.interpret, strongInterpret, Formula.boxdotTranslate];

end Formula

end
