module

public import SeqPL.ProvabilityLogic.Classification.HeightTrace

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

section heightTrace3

omit [𝗜𝚺₁ ⪯ T] in
/-- `⊥` is never a theorem of the truth provability logic of `T`. -/
lemma bot_notMem_provabilityLogicRelativeTo_TA :
    (⊥ : Formula α) ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
  intro h;
  exact not_models_standardProvability_bot (T := T)
    (Arithmetic.TA.provable_iff.mp (h (⟨fun _ => ⊥⟩ : StandardRealization α T)));

end heightTrace3
