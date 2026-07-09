module

public import SeqPL.ProvabilityLogic.Classification.HeightTrace3
public import SeqPL.ProvabilityLogic.Classification.GeneralTrace

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u} [DecidableEq α]
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

section heightTrace4

/--
  If the trace of the truth provability logic of `T` is `ω` (i.e. all of `ℕ`), then the
  truth provability logic of `T` is contained in `S`. This is the contrapositive half of
  the trace dichotomy.

  - [AB05, Corollary 41]
-/
lemma provabilityLogicRelativeTo_TA_subset_LogicS_of_trace_eq_univ
    (h : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ) :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ LogicS := by
  -- A truth provability logic outside `S` has a cofinite trace, whence
  -- `L = LogicGLBetaMinus (L.trace)` forces `⊥ ∈ L` once `L.trace = ω`, contradicting
  -- soundness of `𝗧𝗔`.
  by_contra hS;
  have hCf : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).traceᶜ.Finite :=
    cofinite_trace_of_not_subset_LogicS hS;
  have hCf' : (Set.univ : Set ℕ)ᶜ.Finite := by simp;
  have heq : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = LogicGLBetaMinus Set.univ hCf' := by
    rw [eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hS];
    exact LogicGLBetaMinus.congr h hCf hCf';
  exact bot_notMem_provabilityLogicRelativeTo_TA (heq ▸ LogicGLBetaMinus.bot_mem_of_eq_univ);

end heightTrace4

end
