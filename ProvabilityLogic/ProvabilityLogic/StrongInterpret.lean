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

open LO
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

/-- The interpretation of the boxdot translate of `A` is `T`-provably equivalent to the strong
interpretation of `A`.

This is a routine technical bridge carried over from Foundation, with no separate source. -/
lemma iff_interpret_boxdot_strongInterpret_inside [𝔅.HBL2] :
    T ⊢ f (Aᵇ) 🡘 A.strongInterpret f := by
  sorry

/-- `T` proves the interpretation of the boxdot translate of `A` iff it proves the strong
interpretation of `A`.

This is a routine technical bridge carried over from Foundation, with no separate source. -/
lemma iff_interpret_boxdot_strongInterpret [𝔅.HBL2] :
    T ⊢ f (Aᵇ) ↔ T ⊢ A.strongInterpret f := by
  sorry

/-- A model of `T` satisfies the interpretation of the boxdot translate of `A` iff it satisfies
the strong interpretation of `A`.

This is a routine technical bridge carried over from Foundation, with no separate source. -/
lemma iff_models_interpret_boxdot_strongInterpret
    {M} [Nonempty M] [Structure L M] [M↓[L] ⊧* T] [𝔅.HBL2] [𝔅.SoundOn M] :
    M↓[L] ⊧ f (Aᵇ) ↔ M↓[L] ⊧ A.strongInterpret f := by
  sorry

end Formula

end
