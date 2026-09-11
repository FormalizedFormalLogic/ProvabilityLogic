module

public import ProvabilityLogic.ProvabilityLogic.GL.Basic

@[expose] public section

/-!
# Uniform arithmetical completeness of `GL`

A single realization interpreting exactly the theorems of `GL` as theorems of `T`, taken
here as an axiom: the result is not formalized in this repository.

## References

- [Art86]
- [JdJ98]
-/

open Classical
open FFL
open FFL.FirstOrder.ProvabilityAbstraction

variable {α : Type*}

namespace LogicGL

section

axiom uniform_arithmetical_completeness (α : Type*)
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
  ∃ f : Realization α ℒₒᵣ, ∀ A, T ⊢ f T A ↔ A ∈ LogicGL

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

protected noncomputable def uniformRealization
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : Realization α ℒₒᵣ :=
  (uniform_arithmetical_completeness α T).choose

lemma uniformRealization_spec :
  ∀ A : Formula α, T ⊢ (LogicGL.uniformRealization T) T A ↔ A ∈ LogicGL :=
  (uniform_arithmetical_completeness α T).choose_spec

end

end LogicGL

end
