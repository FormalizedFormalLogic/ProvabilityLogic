module

public import ProvabilityLogic.ProvabilityLogic.Interpret

/-!
# The strong interpretation and the boxdot translation

Port of the `strongInterpret` portion of `Foundation.ProvabilityLogic.Grz.Completeness`
(removed from Foundation after that repository dropped its `Grz` provability-logic file).
The arithmetical completeness results of that file are out of scope here, since this
repository does not define the modal logic `Grz`.
-/

@[expose] public section

open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T]
variable {𝔅 : Provability T₀ T}

namespace Formula

/-- The strong interpretation of a modal formula, sending `□A` to `(A.strongInterpret f) ⋏ 𝔅 (A.strongInterpret f)`
rather than to `𝔅 (A.interpret f)`. This is the interpretation matching the boxdot translation:
`A.strongInterpret f` is provably equivalent (under `T`) to the ordinary interpretation of `Aᵇ`.

This is a routine technical bridge carried over from Foundation, with no separate source. -/
@[grind]
def strongInterpret (f : Realization α 𝔅) : Formula α → FirstOrder.Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => (A.strongInterpret f) 🡒 (B.strongInterpret f)
  | □A    => (A.strongInterpret f) ⋏ 𝔅 (A.strongInterpret f)

variable {f : Realization α 𝔅} {A : Formula α}

omit [T₀ ⪯ T] in
/-- The interpretation of `⊡A` unfolds through `Formula.interpret` to a De Morgan shape built
from `🡒`/`⊥`, which is not syntactically the ambient `⋏`; this bridges the two.

Routine technical bridge, with no separate source. -/
private lemma interpret_boxdot_inside : T ⊢ f (⊡A) 🡘 (f A) ⋏ 𝔅 (f A) := by
  letI := Classical.decEq (FirstOrder.Sentence L);
  dsimp [Formula.interpret];
  cl_prover;

/-- The interpretation of the boxdot translate of `A` is `T`-provably equivalent to the strong
interpretation of `A`.

This is a routine technical bridge carried over from Foundation, with no separate source. -/
lemma iff_interpret_boxdot_strongInterpret_inside [𝔅.HBL2] :
    T ⊢ f (Aᵇ) 🡘 A.strongInterpret f := by
  letI := Classical.decEq (FirstOrder.Sentence L);
  induction A with
  | atom a => simp [Formula.interpret, strongInterpret, Formula.boxdotTranslate];
  | bot => simp only [Formula.boxdotTranslate, strongInterpret, Formula.interpret]; cl_prover;
  | imp A B ihA ihB =>
    simp only [Formula.boxdotTranslate, strongInterpret];
    exact ECC!_of_E!_of_E! ihA ihB;
  | box A ih =>
    simp only [Formula.boxdotTranslate, strongInterpret];
    apply E!_trans interpret_boxdot_inside;
    apply K!_intro;
    · apply CKK!_of_C!_of_C!;
      · cl_prover [ih];
      · apply WeakerThan.pbl (𝓢 := T₀);
        apply 𝔅.mono;
        cl_prover [ih];
    · apply CKK!_of_C!_of_C!;
      · cl_prover [ih];
      · apply WeakerThan.pbl (𝓢 := T₀);
        apply 𝔅.mono;
        cl_prover [ih];

/-- `T` proves the interpretation of the boxdot translate of `A` iff it proves the strong
interpretation of `A`.

This is a routine technical bridge carried over from Foundation, with no separate source. -/
lemma iff_interpret_boxdot_strongInterpret [𝔅.HBL2] :
    T ⊢ f (Aᵇ) ↔ T ⊢ A.strongInterpret f := by
  constructor;
  · intro h; exact (C_of_E_mp! iff_interpret_boxdot_strongInterpret_inside) ⨀ h;
  · intro h; exact (C_of_E_mpr! iff_interpret_boxdot_strongInterpret_inside) ⨀ h;

/-- A model of `T` satisfies the interpretation of the boxdot translate of `A` iff it satisfies
the strong interpretation of `A`.

This is a routine technical bridge carried over from Foundation, with no separate source. -/
lemma iff_models_interpret_boxdot_strongInterpret
    {M} [Nonempty M] [Structure L M] [M↓[L] ⊧* T] [𝔅.HBL2] [𝔅.SoundOn M] :
    M↓[L] ⊧ f (Aᵇ) ↔ M↓[L] ⊧ A.strongInterpret f := by
  sorry

end Formula

end
