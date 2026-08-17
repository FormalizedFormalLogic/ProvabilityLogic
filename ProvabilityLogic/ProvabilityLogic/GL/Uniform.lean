module

public import ProvabilityLogic.ProvabilityLogic.GL.Basic

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {κ : Type*} [Nonempty κ]
         {α : Type*}
         {A B : _root_.Formula α}

namespace LogicGL

section

axiom uniform_arithmetical_completeness (α : Type*)
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
  ∃ f : Realization α ℒₒᵣ, ∀ A, T ⊢ A.standardInterpret f T ↔ A ∈ LogicGL

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

protected noncomputable def uniformRealization
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : Realization α ℒₒᵣ :=
  (uniform_arithmetical_completeness α T).choose

lemma uniformRealization_spec :
  ∀ A : Formula α, T ⊢ A.standardInterpret (LogicGL.uniformRealization T) T ↔ A ∈ LogicGL :=
  (uniform_arithmetical_completeness α T).choose_spec

end

end LogicGL

end
