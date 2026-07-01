module

public import SeqPL.ProvabilityLogic.GL.Basic

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {κ : Type*} [Nonempty κ]
         {α : Type*}
         {A B : _root_.Formula α}

namespace LogicGL

section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

theorem uniform_arithmetical_completeness : ∃ f : StandardRealization α T, ∀ A, T ⊢ f A ↔ A ∈ LogicGL := by sorry;

protected noncomputable def uniformRealization (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] : StandardRealization α T := uniform_arithmetical_completeness.choose

lemma uniformRealization_spec : ∀ A : Formula α, T ⊢ LogicGL.uniformRealization T A ↔ A ∈ LogicGL := uniform_arithmetical_completeness.choose_spec

end

end LogicGL

end
