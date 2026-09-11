module

public import ProvabilityLogic.ProvabilityLogic.Interpret

/-!
# The strong interpretation and the boxdot translation

The strong interpretation `Formula.strongInterpret`, which reads `□A` as `A ⋏ 𝔅 A`, and its
equivalence with the interpretation of the boxdot translate.

## References

- [Gol78]
- [Boo80]
-/

@[expose] public section

open FFL FFL.Entailment
open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
variable {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] {𝔅 : Provability T₀ T}

namespace Formula

omit [L.DecidableEq] in
@[grind]
def strongInterpret (f : Realization α L) {T₀ T : FirstOrder.Theory L} (𝔅 : Provability T₀ T) :
  Formula α → FirstOrder.Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => (A.strongInterpret f 𝔅) 🡒 (B.strongInterpret f 𝔅)
  | □A    => (A.strongInterpret f 𝔅) ⋏ 𝔅 (A.strongInterpret f 𝔅)

variable {f : Realization α L} {A : Formula α}

lemma iff_interpret_boxdot_strongInterpret_inside [𝔅.HBL2] :
  T ⊢ (Aᵇ).interpret f 𝔅 🡘 A.strongInterpret f 𝔅 := by
  induction A with
  | atom a => simp [Formula.interpret, strongInterpret, Formula.boxdotTranslate];
  | bot => simp only [Formula.boxdotTranslate, strongInterpret, Formula.interpret]; cl_prover;
  | imp A B ihA ihB =>
    simp only [Formula.boxdotTranslate, strongInterpret];
    exact ECC_of_E_of_E ihA ihB;
  | box A ih =>
    simp only [Formula.boxdotTranslate, strongInterpret];
    apply E_trans Formula.interpret_boxdot_inside;
    apply K_intro;
    . apply CKK_of_C_of_C;
      . cl_prover [ih];
      . apply WeakerThan.pbl (𝓢 := T₀);
        apply 𝔅.mono;
        cl_prover [ih];
    . apply CKK_of_C_of_C;
      . cl_prover [ih];
      . apply WeakerThan.pbl (𝓢 := T₀);
        apply 𝔅.mono;
        cl_prover [ih];

lemma iff_interpret_boxdot_strongInterpret [𝔅.HBL2] :
  T ⊢ (Aᵇ).interpret f 𝔅 ↔ T ⊢ A.strongInterpret f 𝔅 := by
  constructor;
  . intro h; exact (C_of_E_mp iff_interpret_boxdot_strongInterpret_inside) ⨀ h;
  . intro h; exact (C_of_E_mpr iff_interpret_boxdot_strongInterpret_inside) ⨀ h;

lemma iff_models_interpret_boxdot_strongInterpret
  {M} [Nonempty M] [Structure L M] [M↓[L] ⊧* T] [𝔅.HBL2] [𝔅.SoundOn M] :
  M↓[L] ⊧ (Aᵇ).interpret f 𝔅 ↔ M↓[L] ⊧ A.strongInterpret f 𝔅 := by
  induction A with
  | box A ih =>
    suffices (M↓[L] ⊧ (Aᵇ).interpret f 𝔅) ∧ (M↓[L] ⊧ 𝔅 ((Aᵇ).interpret f 𝔅)) ↔
        (M↓[L] ⊧ A.strongInterpret f 𝔅) ∧ (M↓[L] ⊧ 𝔅 (A.strongInterpret f 𝔅)) by
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
