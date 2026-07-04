module

public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.GraftChain
public import SeqPL.ProvabilityLogic.ModifiedSolovaySentences
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

/-- A `Fintype` instance derived classically from `Finite`, local to this file: needed to
even state `M.height`/`Model.World.rank` for an arbitrary `Finite` carrier, whose actual
enumeration never matters. High priority so that it is always preferred over the
structural (e.g. `Sum`-compositional) instances Mathlib provides for compound types,
keeping `Fintype` resolution consistent with the instance baked into
`StrongReflexiveCountermodel`'s fields (which are elaborated generically over an abstract
carrier, so they always go through this same classical derivation). -/
noncomputable local instance (priority := high) {κ : Type*} [Finite κ] : Fintype κ :=
  Fintype.ofFinite κ

/--
  **Corollary to Lemma 5 in §4 of [Bek90]**: any finite rooted `GL` countermodel of `A`
  whose root sees an `A`-reflexive node `r` yields a countermodel of `A` in the sense of
  `StrongReflexiveCountermodel`. Both extra conditions are achieved by grafting a chain
  of copies of `r` of length `M.height + 2` between the root and `r`
  (`RootedModel.graftChain`), which is forcing-preserving because `r` is `A`-reflexive.
-/
noncomputable def StrongReflexiveCountermodel.ofReflexive [DecidableEq α] {κ : Type u} [Nonempty κ] [Finite κ]
    {A : Formula α} (M : RootedModel κ α) [M.IsFiniteGL]
    (hnA : M.root.1 ⊮ A) (r : M.World) (hr : M.root.1 ≺ r) (hrS : r ⊩ ⋀A.subfmlsS) :
    StrongReflexiveCountermodel (κ ⊕ Fin (M.height + 2)) A := by
  have ha : ∀ B, (□B) ∈ A.subfmls → r ⊩ ((□B) 🡒 B) := by
    intro B hB;
    exact Model.World.forces_fconj.mp hrS _
      (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hB));
  set k := M.height + 2 with hk;
  haveI hfgl' : (M.graftChain r k).IsFiniteGL := RootedModel.graftChain.isFiniteGL hr;
  refine ⟨M.graftChain r k, ?_, Sum.inr ⟨M.height + 1, by omega⟩, ?_, ?_, ?_, ?_,
    Sum.inr ⟨M.height, by omega⟩, ?_, ?_⟩;
  . -- the root still refutes `A`.
    exact (RootedModel.graftChain.mainlemma hr ha (by grind)).2 M.root.1 |>.not.mpr hnA;
  . -- the root sees the bottom of the grafted chain.
    show M.root.1 = M.root.1;
    rfl;
  . -- the bottom of the grafted chain is still `A`-reflexive.
    apply Model.World.forces_fconj.mpr;
    intro φ hφ;
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hφ;
    replace hB : (□B) ∈ A.subfmls := FormulaFinset.iff_mem_prebox_mem.mp hB;
    have hB' : B ∈ A.subfmls := by grind;
    have e₁ := (RootedModel.graftChain.mainlemma hr ha hB).1 (⟨M.height + 1, by omega⟩ : Fin k);
    have e₂ := (RootedModel.graftChain.mainlemma (k := k) hr ha hB).2 r;
    have e₃ := (RootedModel.graftChain.mainlemma hr ha hB').1 (⟨M.height + 1, by omega⟩ : Fin k);
    have e₄ := (RootedModel.graftChain.mainlemma (k := k) hr ha hB').2 r;
    intro hbox;
    exact e₃.mpr (e₄.mpr ((ha B hB) (e₂.mp (e₁.mp hbox))));
  . -- the root is the only predecessor of the bottom of the grafted chain.
    rintro (y | j) hz;
    . have : y = M.root.1 := hz;
      simp [this];
    . exfalso;
      have h₁ : (M.height + 1 : ℕ) < (j : ℕ) := hz;
      have h₂ : (j : ℕ) < M.height + 2 := lt_of_lt_of_eq j.2 hk;
      omega;
  . -- rank maximality of the bottom of the grafted chain.
    rintro (y | i) hz hzr;
    . replace hz : y ≠ M.root.1 := by simpa using hz;
      rw [RootedModel.graftChain.rank_inl hz, RootedModel.graftChain.rank_inr hr];
      have : Model.World.rank y < M.height := RootedModel.rank_lt_height (M.root.2 y hz);
      show Model.World.rank y < M.height + 1 + 1 + Model.World.rank r;
      omega;
    . replace hzr : (i : ℕ) ≠ M.height + 1 := by simpa [Fin.ext_iff] using hzr;
      rw [RootedModel.graftChain.rank_inr hr, RootedModel.graftChain.rank_inr hr];
      have hik : (i : ℕ) < M.height + 2 := lt_of_lt_of_eq i.2 hk;
      show (i : ℕ) + 1 + Model.World.rank r < M.height + 1 + 1 + Model.World.rank r;
      omega;
  . -- the bottom of the chain sees the next chain world.
    show (M.height : ℕ) < M.height + 1;
    omega;
  . -- the next chain world forces exactly the same subformulas of `A`.
    intro B hB;
    exact ((RootedModel.graftChain.mainlemma hr ha hB).1 _).trans
      ((RootedModel.graftChain.mainlemma hr ha hB).1 _).symm;

/--
  The arithmetical fixed-point construction of the modified Solovay sentences: the
  primitive recursive function `h` of Theorem 2 in §6 of [Bek90], whose limit climbs
  by refutation proofs but never enters `r`, and jumps from the old root `b` to `r`
  as soon as a witness of the `𝚺₁` sentence `σ` is found. To be realized via the
  witness-comparison multi-fixed-point machinery of `SeqPL.ProvabilityLogic.Solovay`;
  the `𝚺₁`-ness of `σ` is needed for the provable `𝚺₁`-completeness arguments behind
  the conditions `SC3r`, `SC5` and `SC6`.
-/
theorem exists_modifiedSolovaySentences [DecidableEq α] {κ : Type u} [Nonempty κ] [Finite κ]
    {A : Formula α} (X : StrongReflexiveCountermodel κ A)
    {σ : FirstOrder.Sentence ℒₒᵣ} (hσ : Arithmetic.Hierarchy 𝚺 1 σ) :
    Nonempty (T.standardProvability.ModifiedSolovaySentences X σ) := by
  sorry

/--
  **Theorem 2 in §6 of [Bek90]** (the arithmetical core of Lemma 51 in [AB05]): if
  `A ∉ GLαω`, then for every `𝚺₁` sentence `σ` there are `n : ℕ` and a realization `f`
  such that, provably in `𝗜𝚺₁`, the `n`-times iterated consistency of `T` together with
  `f A` implies the `𝚺₁`-reflection instance `Pr_T(σ) 🡒 σ`. Obtained by the Solovay
  construction on the countermodel given by `StrongReflexiveCountermodel.ofReflexive`,
  modified so that the limit jumps from the root to the `A`-reflexive node `r` as soon
  as a witness of `σ` is found.
-/
theorem exists_realization_sigma1_reflection_of_not_mem_LogicA [DecidableEq α]
    {A : Formula α} (hA : A ∉ LogicA)
    {σ : FirstOrder.Sentence ℒₒᵣ} (hσ : Arithmetic.Hierarchy 𝚺 1 σ) :
    ∃ (n : ℕ) (f : StandardRealization α T),
      𝗜𝚺₁ ⊢ (f (((∼(□^[n]⊥)) ⋏ A : Formula α))) 🡒 ((T.standardProvability σ) 🡒 σ) := by
  obtain ⟨κ, hne, M, hfgl, hnA, r, hr, hrS⟩ := exists_reflexive_countermodel_of_not_mem_LogicA hA;
  haveI := hne;
  haveI := hfgl;
  let X := StrongReflexiveCountermodel.ofReflexive M hnA r hr hrS;
  obtain ⟨S⟩ := exists_modifiedSolovaySentences (T := T) X hσ;
  refine ⟨Model.World.rank X.r, S.realization, ?_⟩;
  have h := S.reflection;
  unfold LO.FirstOrder.ProvabilityAbstraction.Provability.conItr at h;
  have e : (Formula.interpret S.realization
        (((∼(□^[Model.World.rank X.r]⊥)) ⋏ A : Formula α)))
      = ((((T.standardProvability^[Model.World.rank X.r] ⊥) 🡒 ⊥)
          🡒 ((Formula.interpret S.realization A) 🡒 ⊥)) 🡒 ⊥) := by
    simp [Formula.interpret];
  rw [e];
  cl_prover [h];

/--
  If the provability logic of `T` relative to `U` has trace `ω` and contains some
  `A ∉ GLαω`, then `U` proves every `𝚺₁`-reflection instance for `T`. Assertion 2 in
  §6 of [Bek90] (cf. Lemma 51 in [AB05]).
-/
theorem provable_sigma1_reflection_of_mem_not_LogicA :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ∀ {A : Formula α}, A ∈ L → A ∉ LogicA →
    ∀ σ : FirstOrder.Sentence ℒₒᵣ, Arithmetic.Hierarchy 𝚺 1 σ →
      U ⊢ (T.standardProvability σ) 🡒 σ := by
  intro hT A hAL hAA σ hσ;
  classical
  obtain ⟨n, f, hf⟩ := exists_realization_sigma1_reflection_of_not_mem_LogicA (T := T) hAA hσ;
  have hmem : (((∼(□^[n]⊥)) ⋏ A : Formula α)) ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
    provabilityLogic_mdp
      (provabilityLogic_mdp (provabilityLogic_of_GL ProvableHilbert.andIntro)
        (subset_LogicA_of_univ_trace hT LogicA.provable_neg_boxItr_bot))
      hAL;
  exact (Entailment.WeakerThan.pbl hf) ⨀ (hmem f);

/--
  If the provability logic of `T` relative to `U` has trace `ω` and strictly contains
  `GLαω`, then it contains `D`. Corollary 52(2) in [AB05], via the modified Solovay
  construction of Lemma 51 (refugees jump to a reflexive node).
-/
theorem subset_LogicD_of_ssubset_LogicA_of_univ_trace :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → LogicA ⊂ L → LogicD ⊆ L := by
  intro hT h;
  obtain ⟨A, hAL, hAA⟩ := Set.exists_of_ssubset h;
  intro B hB;
  induction hB with
  | mem₁ hB => exact provabilityLogic_of_GL hB;
  | mem₂ hB =>
    rcases Set.mem_insert_iff.mp hB with (rfl | ⟨C, D, rfl⟩);
    . -- the axiom `P`, i.e. `∼□⊥`, is already a theorem of `GLαω`.
      exact subset_LogicA_of_univ_trace hT
        (Formula.boxItr_one (A := (⊥ : Formula α)) ▸ LogicA.provable_neg_boxItr_bot (n := 1));
    . -- the axiom `D`: its interpretation is a `𝚺₁`-reflection instance.
      intro f;
      exact provable_sigma1_reflection_of_mem_not_LogicA hT hAL hAA
        (f (((□C) ⋎ (□D) : Formula α)))
        (by simp [Formula.interpret, Arithmetic.standardProvability_def]);
  | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
  | subst _ ih => intro f; rw [Formula.interpret_subst]; exact ih _;

/--
  No provability logic lies strictly between `GLαω` and `D`. Corollary 55 in [AB05].
-/
theorem no_logic_between_LogicA_LogicD :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ¬((LogicA ⊂ L) ∧ (L ⊂ LogicD)) := by
  rintro hT ⟨h₁, h₂⟩;
  exact h₂.not_subset (subset_LogicD_of_ssubset_LogicA_of_univ_trace hT h₁);

end
