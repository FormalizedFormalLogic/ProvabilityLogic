module

public import SeqPL.ProvabilityLogic.Classification.Trace

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/--
  `GLαω` proves the iterated consistency statement `∼□^[n]⊥` for every `n`, by chaining
  the axioms `TBB 0, …, TBB (n-1)`.
-/
lemma LogicA.provable_neg_boxItr_bot [DecidableEq α] {n : ℕ} :
    ((∼(□^[n]⊥)) : Formula α) ∈ LogicA := by
  induction n with
  | zero =>
    apply Logic.sumQuasiNormal.mem₁;
    apply ProvableHilbert.Kripke.completeness;
    intro κ _ M _ x;
    simp only [Formula.boxItr, Model.World.forces_neg];
    exact fun h => h;
  | succ n ih =>
    have hTBB : (TBB n : Formula α) ∈ LogicA :=
      Logic.sumQuasiNormal.mem₂ ⟨TBB n, ⟨n, by simp, rfl⟩, by simp⟩;
    have hK : ((TBB n 🡒 ((∼(□^[n]⊥)) 🡒 (∼(□^[n + 1]⊥)))) : Formula α) ∈ LogicGL := by
      apply ProvableHilbert.Kripke.completeness;
      intro κ _ M _ x;
      simp only [TBB, Model.World.forces_imp];
      tauto;
    exact Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ hK) hTBB) ih;

/--
  If `A ∉ GLαω`, then `GL ⊬ ◇(⋀A.subfmlsS) 🡒 A`. This is the modal input of Lemma 51
  in [AB05], obtained from the chain lemma
  `LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS` and
  `LogicA.provable_neg_boxItr_bot`.
-/
lemma not_GL_provable_dia_subfmlsS_imp_of_not_mem_LogicA [DecidableEq α]
    {A : Formula α} (h : A ∉ LogicA) :
    ((◇(⋀A.subfmlsS)) 🡒 A) ∉ LogicGL := by
  intro hGL;
  apply h;
  have h₁ : ((∼(□^[A.subfmls.prebox.card + 1]⊥)) : Formula α) ∈ LogicA :=
    LogicA.provable_neg_boxItr_bot;
  have h₂ : ((◇(⋀A.subfmlsS)) : Formula α) ∈ LogicA :=
    Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mem₁ LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS) h₁;
  exact Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ hGL) h₂;

/--
  A formula outside `GLαω` has a finite rooted `GL` countermodel whose root refutes `A`
  and sees an `A`-reflexive node (the model `K₀` in the proof of Lemma 51 in [AB05]).
-/
lemma exists_reflexive_countermodel_of_not_mem_LogicA [DecidableEq α]
    {A : Formula α} (h : A ∉ LogicA) :
    ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
      M.root.1 ⊮ A ∧ ∃ r : M.World, M.root.1 ≺ r ∧ r ⊩ ⋀A.subfmlsS := by
  have := LogicGL_semantical_TFAE (A := (◇(⋀A.subfmlsS)) 🡒 A) |>.out 2 0 |>.not.mpr
    (not_GL_provable_dia_subfmlsS_imp_of_not_mem_LogicA h);
  push Not at this;
  obtain ⟨κ, hne, M, hfgl, hroot⟩ := this;
  obtain ⟨hdia, hnA⟩ := Model.World.not_forces_imp.mp hroot;
  obtain ⟨r, hr, hrS⟩ := Model.World.forces_dia.mp hdia;
  exact ⟨κ, hne, M, hfgl, hnA, r, hr, hrS⟩;

/--
  If the provability logic of `T` relative to `U` has trace `ω` and strictly contains
  `GLαω`, then it contains `D`. Corollary 52(2) in [AB05], via the modified Solovay
  construction of Lemma 51 (refugees jump to a reflexive node).
-/
theorem subset_LogicD_of_ssubset_LogicA_of_univ_trace :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → LogicA ⊂ L → LogicD ⊆ L := by
  sorry

/--
  No provability logic lies strictly between `GLαω` and `D`. Corollary 55 in [AB05].
-/
theorem no_logic_between_LogicA_LogicD :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ¬((LogicA ⊂ L) ∧ (L ⊂ LogicD)) := by
  rintro hT ⟨h₁, h₂⟩;
  exact h₂.not_subset (subset_LogicD_of_ssubset_LogicA_of_univ_trace hT h₁);

end
