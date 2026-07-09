module

public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.Graft
public import SeqPL.Logic.A.Basic
public import SeqPL.ProvabilityLogic.ModifiedSolovaySentences
public import SeqPL.ProvabilityLogic.Classification.GeneralTrace

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

section

/-- A `Fintype` instance derived classically from `Finite`, local to this section: needed
to even state `M.height`/`Model.World.rank` for an arbitrary `Finite` carrier, whose
actual enumeration never matters. High priority so that it is always preferred over the
structural (e.g. `Sum`-compositional) instances Mathlib provides for compound types,
keeping `Fintype` resolution consistent with the classical instance baked into
`StrongReflexiveCountermodel`'s fields in `ModifiedSolovaySentences.lean` (which is
elaborated generically over an abstract carrier via the same `Fintype.ofFinite`
derivation) — mixing this classical derivation with the structural one for the same
compound type (e.g. `κ ⊕ Fin n`) would give two non-defeq `Fintype` instances and break
downstream `Model.World.rank` equalities. This whole development is already classical
(`open Classical` at the top of `ModifiedSolovaySentences.lean`) and noncomputable, so
deriving `Fintype` via choice here loses nothing; the section is scoped tightly around
the few declarations that actually touch `StrongReflexiveCountermodel`, so it cannot
affect unrelated `Fintype` resolution elsewhere in this file. -/
noncomputable local instance (priority := high) {κ : Type*} [Finite κ] : Fintype κ :=
  Fintype.ofFinite κ

/--
  **Corollary to Lemma 5 in §4 of [Bek90]**: any finite rooted `GL` countermodel of `A`
  whose root sees an `A`-reflexive node `r` yields a countermodel of `A` in the sense of
  `StrongReflexiveCountermodel`.
-/
noncomputable def StrongReflexiveCountermodel.ofReflexive [DecidableEq α] {κ : Type u} [Nonempty κ] [Finite κ]
    {A : Formula α} (M : RootedModel κ α) [M.IsFiniteGL]
    (hnA : M.root.1 ⊮ A) (r : M.World) (hr : M.root.1 ≺ r) (hrS : r ⊩ ⋀A.subfmlsS) :
    StrongReflexiveCountermodel (κ ⊕ Fin (M.height + 2)) A := by
  -- Both extra conditions (the reflexive node's unique predecessor being the root, and
  -- rank maximality) are achieved by grafting a chain of copies of `r` of length
  -- `M.height + 2` between the root and `r` (`RootedModel.graft`), which is
  -- forcing-preserving because `r` is `A`-reflexive.
  have ha : ∀ B, (□B) ∈ A.subfmls → r ⊩ ((□B) 🡒 B) := by
    intro B hB;
    exact Model.World.forces_fconj.mp hrS _
      (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hB));
  set k := M.height + 2 with hk;
  haveI hfgl' : (M.graft r k).IsFiniteGL := RootedModel.graft.isFiniteGL hr;
  refine ⟨M.graft r k, ?_, Sum.inr ⟨M.height + 1, by omega⟩, ?_, ?_, ?_, ?_,
    Sum.inr ⟨M.height, by omega⟩, ?_, ?_⟩;
  . -- the root still refutes `A`.
    exact (RootedModel.graft.mainlemma hr ha (by grind)).2 M.root.1 |>.not.mpr hnA;
  . -- the root sees the bottom of the grafted chain.
    show M.root.1 = M.root.1;
    rfl;
  . -- the bottom of the grafted chain is still `A`-reflexive.
    apply Model.World.forces_fconj.mpr;
    intro C hC;
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC;
    replace hB : (□B) ∈ A.subfmls := FormulaFinset.iff_mem_prebox_mem.mp hB;
    have hB' : B ∈ A.subfmls := by grind;
    have e₁ := (RootedModel.graft.mainlemma hr ha hB).1 (⟨M.height + 1, by omega⟩ : Fin k);
    have e₂ := (RootedModel.graft.mainlemma (k := k) hr ha hB).2 r;
    have e₃ := (RootedModel.graft.mainlemma hr ha hB').1 (⟨M.height + 1, by omega⟩ : Fin k);
    have e₄ := (RootedModel.graft.mainlemma (k := k) hr ha hB').2 r;
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
      rw [RootedModel.graft.rank_inl hz, RootedModel.graft.rank_inr hr];
      have : Model.World.rank y < M.height := RootedModel.rank_lt_height (M.root.2 y hz);
      show Model.World.rank y < M.height + 1 + 1 + Model.World.rank r;
      omega;
    . replace hzr : (i : ℕ) ≠ M.height + 1 := by simpa [Fin.ext_iff] using hzr;
      rw [RootedModel.graft.rank_inr hr, RootedModel.graft.rank_inr hr];
      have hik : (i : ℕ) < M.height + 2 := lt_of_lt_of_eq i.2 hk;
      show (i : ℕ) + 1 + Model.World.rank r < M.height + 1 + 1 + Model.World.rank r;
      omega;
  . -- the bottom of the chain sees the next chain world.
    show (M.height : ℕ) < M.height + 1;
    omega;
  . -- the next chain world forces exactly the same subformulas of `A`.
    intro B hB;
    exact ((RootedModel.graft.mainlemma hr ha hB).1 _).trans
      ((RootedModel.graft.mainlemma hr ha hB).1 _).symm;

/--
  The arithmetical fixed-point construction of the modified Solovay sentences: the
  primitive recursive function `h` of Theorem 2 in §6 of [Bek90], associated to a
  `StrongReflexiveCountermodel` of `A` and a `𝚺₁` sentence `σ`.
-/
theorem exists_modifiedSolovaySentences [DecidableEq α] {κ : Type u} [Nonempty κ] [Finite κ]
    {A : Formula α} (X : StrongReflexiveCountermodel κ A)
    {σ : FirstOrder.Sentence ℒₒᵣ} (hσ : Arithmetic.Hierarchy 𝚺 1 σ) :
    Nonempty (T.standardProvability.ModifiedSolovaySentences X σ) :=
  -- `h`'s limit climbs by refutation proofs but never enters `r`, and jumps from the
  -- old root `b` to `r` as soon as a witness of `σ` is found, realized via the
  -- witness-comparison multi-fixed-point machinery of `SeqPL.ProvabilityLogic.Solovay`;
  -- the `𝚺₁`-ness of `σ` is needed for the provable `𝚺₁`-completeness arguments behind
  -- the conditions `SC3r`, `SC5` and `SC6`.
  ⟨LO.FirstOrder.Theory.standardProvability.modifiedSolovaySentences T X hσ⟩

/--
  **Theorem 2 in §6 of [Bek90]** (the arithmetical core of Lemma 51 in [AB05]): if
  `A ∉ GLαω`, then for every `𝚺₁` sentence `σ` there are `n : ℕ` and a realization `f`
  such that, provably in `𝗜𝚺₁`, the `n`-times iterated consistency of `T` together with
  `f A` implies the `𝚺₁`-reflection instance `Pr_T(σ) 🡒 σ`.
-/
theorem exists_realization_sigma1_reflection_of_not_mem_LogicA [DecidableEq α]
    {A : Formula α} (hA : A ∉ LogicA)
    {σ : FirstOrder.Sentence ℒₒᵣ} (hσ : Arithmetic.Hierarchy 𝚺 1 σ) :
    ∃ (n : ℕ) (f : StandardRealization α T),
      𝗜𝚺₁ ⊢ (f (((∼(□^[n]⊥)) ⋏ A : Formula α))) 🡒 ((T.standardProvability σ) 🡒 σ) := by
  -- Obtained by the Solovay construction on the countermodel given by
  -- `StrongReflexiveCountermodel.ofReflexive`, modified so that the limit jumps from
  -- the root to the `A`-reflexive node `r` as soon as a witness of `σ` is found.
  obtain ⟨κ, hne, M, hfgl, hnA, r, hr, hrS⟩ := LogicA.exists_reflexive_countermodel_of_not_mem_LogicA hA;
  haveI := hne;
  haveI := hfgl;
  let X := StrongReflexiveCountermodel.ofReflexive M hnA r hr hrS;
  obtain ⟨S⟩ := exists_modifiedSolovaySentences (T := T) X hσ;
  use Model.World.rank X.r, S.realization;
  have h := S.reflection;
  unfold LO.FirstOrder.ProvabilityAbstraction.Provability.conItr at h;
  have e : (Formula.interpret S.realization
        (((∼(□^[Model.World.rank X.r]⊥)) ⋏ A : Formula α)))
      = ((((T.standardProvability^[Model.World.rank X.r] ⊥) 🡒 ⊥)
          🡒 ((Formula.interpret S.realization A) 🡒 ⊥)) 🡒 ⊥) := by
    simp [Formula.interpret];
  rw [e];
  cl_prover [h];

end

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
