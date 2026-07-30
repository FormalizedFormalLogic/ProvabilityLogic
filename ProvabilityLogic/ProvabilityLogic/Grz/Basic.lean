module

public import ProvabilityLogic.Logic.Grz.Boxdot
public import ProvabilityLogic.ProvabilityLogic.S.Basic
public import ProvabilityLogic.ProvabilityLogic.StrongInterpret

/-!
# Arithmetical completeness of Logic Grz

Arithmetical completeness of `Grz`, phrased through the strong interpretation
`Formula.strongInterpret` and the equivalence between `Grz`-provability and `GL`-provability of
the boxdot translate (`iff_provable_boxdot_GL_provable_Grz`).

Main results:
- `LogicGrz.arithmetical_completeness_iff_of_infinity_height`,
  `LogicGrz.arithmetical_completeness_iff_of_sigma1_sound`: `A ∈ LogicGrz` iff the strong
  interpretation of `A` is `T`-provable under every standard realization.
- `LogicGrz.arithmetical_completeness_model_iff`: `A ∈ LogicGrz` iff the strong interpretation of
  `A` holds in the standard model under every standard realization.

- [Gol78]
- [Boo80]
-/

@[expose] public section

open LO
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

variable {α : Type u} {A : Formula α}

namespace LogicGrz

section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/--
  **Arithmetical completeness of `Grz`** (infinite-height case): `A ∈ LogicGrz` iff the strong
  interpretation of `A` is `T`-provable under every standard realization.
-/
theorem arithmetical_completeness_iff_of_infinity_height (height : T.height = (⊤ : ℕ∞))
    [DecidableEq α] :
    A ∈ LogicGrz ↔ (∀ f : StandardRealization α T, T ⊢ A.strongInterpret f) := by
  rw [← iff_provable_boxdot_GL_provable_Grz,
    LogicGL.arithmetical_completeness_iff_of_infinity_height height];
  exact forall_congr' fun f => Formula.iff_interpret_boxdot_strongInterpret;

/-- **Arithmetical completeness of `Grz`** for a `𝚺₁`-sound theory. -/
theorem arithmetical_completeness_iff_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1] [DecidableEq α] :
    A ∈ LogicGrz ↔ (∀ f : StandardRealization α T, T ⊢ A.strongInterpret f) :=
  arithmetical_completeness_iff_of_infinity_height
    (FirstOrder.Arithmetic.height_eq_top_of_sigma1_sound T)

end

section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]

/--
  **Arithmetical completeness of `Grz`** relative to the standard model: `A ∈ LogicGrz` iff the
  strong interpretation of `A` holds in the standard model under every standard realization.
-/
theorem arithmetical_completeness_model_iff [DecidableEq α] :
    A ∈ LogicGrz ↔ (∀ f : StandardRealization α T, ℕ↓[ℒₒᵣ] ⊧ A.strongInterpret f) := by
  rw [← iff_provable_boxdot_S_provable_Grz, LogicS.arithmetical_completeness_iff (T := T)];
  exact forall_congr' fun f => Formula.iff_models_interpret_boxdot_strongInterpret;

end

end LogicGrz

end
