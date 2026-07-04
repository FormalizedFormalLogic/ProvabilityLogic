module

public import SeqPL.Kripke.RootedModel
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
  have := (LogicGL.iff_forces_root (A := (◇(⋀A.subfmlsS)) 🡒 A)).not.mp
    (not_GL_provable_dia_subfmlsS_imp_of_not_mem_LogicA h);
  push Not at this;
  obtain ⟨κ, hne, M, hfgl, hroot⟩ := this;
  obtain ⟨hdia, hnA⟩ := Model.World.not_forces_imp.mp hroot;
  obtain ⟨r, hr, hrS⟩ := Model.World.forces_dia.mp hdia;
  exact ⟨κ, hne, M, hfgl, hnA, r, hr, hrS⟩;

section OmegaModel

/--
  **ω-model completeness of `GLαω`** (Lemma 5 in §3 of [Bek90], "On the classification
  of propositional provability logics"). The ω-models are realized as
  `M.graftChainOmega a` for finite rooted GL models `M` and points `a` above the root:
  the root gains an infinite ascending chain (so it forces every `TBB n`), while it
  keeps its lateral cones (so that, unlike the pseudo-tail models of `LogicD`, the
  axioms of `LogicD` can be refuted). The middle item is the deduction-theorem form
  used in the paper's proof.
-/
theorem LogicA.provability_TFAE [DecidableEq α] {A : Formula α} : [
    A ∈ LogicA,
    ∃ n : ℕ, ((∼(□^[n]⊥)) 🡒 A) ∈ LogicGL,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      ∀ a : M.World, M.root.1 ≺ a →
        Forces (M := (M.graftChainOmega a).toModel) (M.graftChainOmega a).root.1 A
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h;
    obtain ⟨Y, hY, hGL⟩ := GL_sumQuasiNormal_finite_provable h;
    -- Recover an index for each `TBB` axiom occurring in `Y` and bound them by `n`.
    set idx : LetterlessFormula → ℕ :=
      fun B => if hB : ∃ i, TBB i = B then hB.choose else 0 with hidx_def;
    have hidx : ∀ B ∈ Y, TBB (idx B) = B := by
      intro B hB;
      obtain ⟨i, -, hi⟩ := hY B hB;
      have he : ∃ j, (TBB j : LetterlessFormula) = B := ⟨i, hi⟩;
      simp only [hidx_def, dif_pos he];
      exact he.choose_spec;
    refine ⟨Y.sup idx + 1, ?_⟩;
    have h₁ : ((∼(□^[Y.sup idx + 1]⊥)) 🡒 (LetterlessFormula.lift (⋀Y) : Formula α)) ∈ LogicGL := by
      apply LogicGL.iff_forces_root.mpr;
      intro κ _ M _ hne;
      haveI : Fintype M.World := Fintype.ofFinite _;
      replace hne : ¬(Model.World.rank M.root.1 < Y.sup idx + 1) :=
        fun hc => (Model.World.forces_neg.mp hne) (Model.iff_rank_lt_forces_boxItr_bot.mp hc);
      have heq : (LetterlessFormula.lift (⋀Y) : Formula α) = ⋀(Y.toList.map LetterlessFormula.lift) := by
        simp [FormulaFinset.conj, LetterlessFormula.eq_lift_lconj];
      rw [heq];
      apply Model.World.forces_lconj.mpr;
      intro C hC;
      obtain ⟨B, hBY, rfl⟩ := List.mem_map.mp hC;
      replace hBY : B ∈ Y := Finset.mem_toList.mp hBY;
      rw [← hidx B hBY, LetterlessFormula.eq_lift_TBB];
      apply Model.iff_forces_TBB_neq_rank.mpr;
      have : idx B ≤ Y.sup idx := Finset.le_sup hBY;
      omega;
    exact ProvableHilbert.impTrans h₁ hGL;
  tfae_have 2 → 3 := by
    rintro ⟨n, hGL⟩ κ _ M _ a Rra;
    haveI := RootedModel.graftChainOmega.isGL (M := M) (a := a) Rra;
    exact ProvableHilbert.Kripke.soundness hGL ((M.graftChainOmega a).toModel)
      (M.graftChainOmega a).root.1
      (Model.World.forces_neg.mpr RootedModel.graftChainOmega.root_not_forces_boxItr_bot);
  tfae_have 3 → 1 := by
    intro h;
    by_contra hA;
    obtain ⟨κ, hne, M, hfgl, hroot, r, Rrr, hrS⟩ :=
      exists_reflexive_countermodel_of_not_mem_LogicA hA;
    haveI := hne; haveI := hfgl;
    have ha : ∀ B, (□B) ∈ A.subfmls → r ⊩ ((□B) 🡒 B) := by
      intro B hB;
      exact Model.World.forces_fconj.mp hrS _
        (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hB));
    apply hroot;
    exact RootedModel.graftChainOmega.mainlemma Rrr ha Formula.mem_subfmls_self
      |>.2 M.root.1 |>.mp (h M r Rrr);
  tfae_finish;

/--
  A formula is a `GLαω` theorem iff it is forced at the root of every ω-model
  (Lemma 5 in §3 of [Bek90]).
-/
theorem LogicA.iff_provable_forces_graftChainOmega_root [DecidableEq α] {A : Formula α} :
    A ∈ LogicA ↔
      (∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
        ∀ a : M.World, M.root.1 ≺ a →
          Forces (M := (M.graftChainOmega a).toModel) (M.graftChainOmega a).root.1 A) :=
  LogicA.provability_TFAE.out 0 2

/--
  Deduction-theorem form of `GLαω`-provability: `GLαω ⊢ A` iff
  `GL ⊢ ∼□^[n]⊥ 🡒 A` for some `n` (used in the proof of Lemma 5 in §3 of [Bek90]).
-/
theorem LogicA.iff_provable_provable_GL_neg_boxItr_bot_imp [DecidableEq α] {A : Formula α} :
    A ∈ LogicA ↔ ∃ n : ℕ, ((∼(□^[n]⊥)) 🡒 A) ∈ LogicGL :=
  LogicA.provability_TFAE.out 0 1

end OmegaModel

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
