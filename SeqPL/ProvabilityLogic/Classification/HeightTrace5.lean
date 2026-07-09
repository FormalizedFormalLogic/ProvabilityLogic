module

public import SeqPL.ProvabilityLogic.Classification.HeightTrace
public import SeqPL.ProvabilityLogic.Classification.HeightTrace2
public import SeqPL.ProvabilityLogic.Classification.A_D

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/--
  Converse direction: if the truth provability logic of `T` is `D`, then `T` is
  `Σ₁`-sound.

  - [AB05, Corollary 41(ii)]
-/
lemma soundOnHierarchy_of_eq_provabilityLogicRelativeTo_TA_LogicD [DecidableEq α] [Nonempty α]
    (h : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = LogicD) :
    T.SoundOnHierarchy 𝚺 1 := by
  -- Uses Corollary 52(i) (`provable_sigma1_reflection_of_mem_not_LogicA`) applied to axiom
  -- `D` itself, which lies in `D` but not in `LogicA` (`LogicA.not_provable_axiomD`).
  apply soundOnHierarchy_of_models_standardProvability_imp;
  intro σ hσ;
  apply Arithmetic.TA.provable_iff.mp;
  obtain ⟨a⟩ := ‹Nonempty α›;
  have hAL : ((□((□(#a) : Formula α) ⋎ □(#a))) 🡒 ((□(#a) : Formula α) ⋎ □(#a))) ∈
      (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
    rw [h];
    exact LogicD.provable_axiomD;
  have hAA := LogicA.not_provable_axiomD (α := α) (a := a);
  have hT : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ := by
    apply Set.eq_univ_of_forall;
    intro n;
    exact mem_trace_of_provable_TBB (h ▸ LogicD.provable_TBB);
  exact provable_sigma1_reflection_of_mem_not_LogicA hT hAL hAA σ hσ;

end
