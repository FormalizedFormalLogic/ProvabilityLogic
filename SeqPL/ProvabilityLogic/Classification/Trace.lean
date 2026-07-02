module

public import SeqPL.ProvabilityLogic.Classification.Full
public import SeqPL.ProvabilityLogic.Solovay

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/--
  If `n` is in the trace of the provability logic of `T` relative to `U`, then `TBB n`
  is a theorem of it. Lemma 46 and Corollary 47 in [AB05], stated directly for
  `provabilityLogicRelativeTo` via the Solovay construction.
-/
theorem provable_TBB_of_mem_trace {n : ℕ}
    (h : n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace) :
    (TBB n : Formula α) ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  obtain ⟨A, hA_L, hA_tr⟩ : ∃ A ∈ (T.provabilityLogicRelativeTo U : Logic α), n ∈ A.trace := by
    simpa [Logic.trace, FormulaSet.trace] using h;
  obtain ⟨κ, _, M, _, _, rfl, hr⟩ := Formula.iff_mem_trace.mp hA_tr;
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences T (M.extendRoot 1);
  -- Each Solovay sentence implies the interpretation of `A 🡒 TBB M.height`.
  have key : ∀ i : (M.extendRoot 1).World,
      𝗜𝚺₁ ⊢ S.σ i 🡒 ((A 🡒 TBB M.height).interpret S.realization) := by
    rintro (x | i);
    . -- original world: use the main lemma with the semantic claim
      apply S.mainlemma (i := Sum.inl x) (by simp [RootedModel.extendRoot, Fin.posLast]);
      intro hAx;
      by_cases hx : x = M.root.1;
      . subst hx;
        exact absurd (RootedModel.extendRoot.same_forces_embed.mp hAx) hr;
      . apply Model.iff_forces_TBB_neq_rank.mpr;
        rw [show Sum.inl x = RootedModel.extendRoot.embed (M := M) (n := 1) x from rfl,
          RootedModel.extendRoot.Ext1.eq_embed_original_rank_original_rank];
        exact fun hcon => hx (RootedModel.iff_eq_rank_height_is_root.mp hcon);
    . -- the new root: chain through `SC2` and the negative main lemma
      have b₁ : 𝗜𝚺₁ ⊢ S.σ (Sum.inr i) 🡒 T.standardProvability.dia (S.σ (Sum.inl M.root.1)) :=
        S.SC2 _ _ (by simp [Model.Rel]);
      have b₂ : 𝗜𝚺₁ ⊢ S.σ (Sum.inl M.root.1) 🡒
          ∼((□^[M.height]⊥ : Formula α).interpret S.realization) := by
        apply S.mainlemma_neg (by simp [RootedModel.extendRoot, Fin.posLast]);
        apply Model.iff_rank_lt_forces_boxItr_bot.not.mp;
        rw [show (Sum.inl M.root.1 : (M.extendRoot 1).World)
          = RootedModel.extendRoot.embed (M := M) (n := 1) M.root.1 from rfl,
          RootedModel.extendRoot.Ext1.eq_embed_original_rank_original_rank];
        exact lt_irrefl _;
      have b₃ : 𝗜𝚺₁ ⊢ T.standardProvability.dia (S.σ (Sum.inl M.root.1)) 🡒
          ∼(T.standardProvability ((□^[M.height]⊥ : Formula α).interpret S.realization)) :=
        contra! $ T.standardProvability.mono' $ CN!_of_CN!_right b₂;
      have b₄ : (□^[M.height + 1]⊥ : Formula α).interpret S.realization
          = T.standardProvability ((□^[M.height]⊥ : Formula α).interpret S.realization) := by
        simp only [Formula.interpret_boxItr, Function.iterate_succ_apply'];
      simp only [Formula.interpret, TBB, b₄];
      cl_prover [b₁, b₃];
  have main : 𝗜𝚺₁ ⊢ ((A 🡒 TBB M.height).interpret S.realization) := by
    have := left_Udisj!_intro _ key;
    cl_prover [this, S.SC4];
  intro f;
  have h₃ : U ⊢ ((TBB M.height : Formula α).interpret S.realization) := by
    have h₁ : U ⊢ (A.interpret S.realization) 🡒 ((TBB M.height : Formula α).interpret S.realization) :=
      WeakerThan.pbl main;
    exact h₁ ⨀ (hA_L S.realization);
  have e : ∀ g : StandardRealization α T,
      (TBB M.height : Formula α).interpret g
      = LetterlessFormula.interpret T.standardProvability (TBB M.height) := by
    intro g;
    rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  show U ⊢ (TBB M.height : Formula α).interpret f;
  rw [e f];
  rw [e S.realization] at h₃;
  exact h₃;

/--
  If the trace of the provability logic of `T` relative to `U` is coinfinite, then it
  equals `GLα` of its trace. Corollary 48 in [AB05].
-/
theorem eq_provabilityLogic_LogicGLAlpha_of_coinfinite_trace [DecidableEq α] [T ⪯ U]
    (hCi : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Infinite) :
    (T.provabilityLogicRelativeTo U : Logic α)
      = LogicGLAlpha (T.provabilityLogicRelativeTo U : Logic α).trace := by
  apply Set.Subset.antisymm;
  . exact subset_LogicGLAlpha_of_trace_coinfinite hCi;
  . intro A hA;
    induction hA with
    | mem₁ hA =>
      intro f;
      exact WeakerThan.pbl (LogicGL.arithmetical_soundness hA);
    | mem₂ hA =>
      obtain ⟨B, ⟨n, hn, rfl⟩, rfl⟩ := hA;
      rw [LetterlessFormula.eq_lift_TBB];
      exact provable_TBB_of_mem_trace hn;
    | mdp _ _ ihAB ihA =>
      intro f;
      exact (ihAB f) ⨀ (ihA f);
    | subst _ ihA =>
      intro f;
      rw [Formula.interpret_subst];
      exact ihA _;

/--
  If the provability logic of `T` relative to `U` is not contained in `S`,
  then its trace is cofinite (the first half of the proof of Lemma 49 in [AB05]).
-/
lemma cofinite_trace_of_not_subset_LogicS [DecidableEq α] [T ⪯ U]
    (hS : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ LogicS) :
    (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite := by
  by_contra hInf;
  apply hS;
  rw [eq_provabilityLogic_LogicGLAlpha_of_coinfinite_trace (by exact hInf)];
  exact subset_LogicGLAlpha_LogicS;


section

open LO.FirstOrder.ProvabilityAbstraction.Provability

variable {A B : Formula α}

omit [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] in
lemma provabilityLogic_mdp
    (h₁ : (A 🡒 B) ∈ (T.provabilityLogicRelativeTo U : Logic α))
    (h₂ : A ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    B ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun f => (h₁ f) ⨀ (h₂ f)

omit [𝗜𝚺₁ ⪯ U] in
lemma provabilityLogic_of_GL [T ⪯ U] (h : A ∈ LogicGL) :
    A ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun _ => WeakerThan.pbl (LogicGL.arithmetical_soundness h)

omit [𝗜𝚺₁ ⪯ U] in
lemma provabilityLogic_lconj [T ⪯ U] {Γ : FormulaList α}
    (h : ∀ B ∈ Γ, B ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    (⋀Γ) ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  match Γ with
  | [] => exact provabilityLogic_of_GL ProvableHilbert.top;
  | [B] => simpa using h B (by simp);
  | B :: C :: Γ =>
    exact provabilityLogic_mdp
      (provabilityLogic_mdp (provabilityLogic_of_GL ProvableHilbert.andIntro) (h B (by simp)))
      (provabilityLogic_lconj (Γ := C :: Γ) (by grind));

omit [𝗜𝚺₁ ⪯ U] in
lemma provabilityLogic_fconj [T ⪯ U] {Γ : FormulaFinset α}
    (h : ∀ B ∈ Γ, B ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    (⋀Γ) ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  provabilityLogic_lconj (by simpa)

private lemma spectrum_TBBMinus' {s : Set ℕ} (hs : s.Finite) :
    LetterlessFormula.spectrum (TBBMinus s) = s :=
  compl_inj_iff.mp (LetterlessFormula.trace_TBBMinus hs)

section

variable [DecidableEq α] [T ⪯ U]

/--
  If the provability logic `L` of `T` relative to `U` is not contained in `S`, then it
  proves the lifted `TBBMinus` axiom of its trace (the key step of Lemma 49 in [AB05],
  via the Solovay construction and the reflexive main lemma).
-/
theorem provable_TBBMinus_of_not_subset_LogicS
    (hS : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ LogicS) :
    (LetterlessFormula.lift (TBBMinus _ (cofinite_trace_of_not_subset_LogicS hS)) : Formula α)
      ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  set L := (T.provabilityLogicRelativeTo U : Logic α) with hL;
  have hcof := cofinite_trace_of_not_subset_LogicS hS;
  -- Take `A ∈ L` with `A ∉ S`; then `GL ⊬ ⋀A.subfmlsS 🡒 A`.
  obtain ⟨A, hA₁, hA₂⟩ := Set.not_subset.mp hS;
  replace hA₂ : ((⋀A.subfmlsS) 🡒 A) ∉ LogicGL :=
    fun hc => hA₂ (LogicS.iff_provable_S_provable_GL.mpr hc);
  -- Extract a finite rooted countermodel `M₁` whose root is `A`-reflexive but refutes `A`.
  have := LogicGL_semantical_TFAE (A := (⋀A.subfmlsS) 🡒 A) |>.out 2 0 |>.not.mpr hA₂;
  push Not at this;
  obtain ⟨κ₁, hne, M₁, hfgl, hroot⟩ := this;
  haveI := hne; haveI := hfgl;
  haveI : Fintype M₁.World := Fintype.ofFinite _;
  obtain ⟨hconj, hnA⟩ := Model.World.not_forces_imp.mp hroot;
  have ha : ∀ B, (□B) ∈ A.subfmls → M₁.root.1 ⊩ ((□B) 🡒 B) := by
    intro B hB;
    exact Model.World.forces_fconj.mp hconj _
      (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hB));
  -- `R`: the members of `L.trace` below the height of `M₁`; `B`: `A` with those `TBB`s.
  let R : Finset ℕ :=
    Set.Finite.inter_of_left (s := (Finset.range M₁.height : Set ℕ)) (t := L.trace)
      (Finset.finite_toSet _) |>.toFinset;
  let B : Formula α := A ⋏ ⋀(R.image (TBB (α := α)));
  have hB : B ∈ L := by
    apply provabilityLogic_mdp (provabilityLogic_mdp (provabilityLogic_of_GL ProvableHilbert.andIntro) hA₁);
    apply provabilityLogic_fconj;
    intro C hC;
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC;
    apply provable_TBB_of_mem_trace;
    have : i ∈ (Finset.range M₁.height : Set ℕ) ∩ L.trace := by simpa [R] using hi;
    exact this.2;
  -- The Solovay sentences of `M₁.extendRoot 1`.
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences T (M₁.extendRoot 1);
  -- Each Solovay sentence implies the interpretation of `B 🡒 lift (TBBMinus L.traceᶜ)`.
  have key : ∀ i : (M₁.extendRoot 1).World,
      𝗜𝚺₁ ⊢ S.σ i 🡒 ((B 🡒 (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α)).interpret S.realization) := by
    rintro (x | i);
    . -- original worlds: semantic claim through the main lemma
      apply S.mainlemma (i := Sum.inl x) (by simp [RootedModel.extendRoot, Fin.posLast]);
      intro hBx;
      apply Model.iff_forces_lift_rank_mem_spectrum.mpr;
      rw [spectrum_TBBMinus' hcof];
      rw [show Sum.inl x = RootedModel.extendRoot.embed (M := M₁) (n := 1) x from rfl,
        RootedModel.extendRoot.Ext1.eq_embed_original_rank_original_rank];
      intro hmem;
      replace hBx : x ⊩ B := RootedModel.extendRoot.same_forces_embed.mp hBx;
      obtain ⟨hAx, hTx⟩ := Model.World.forces_and.mp hBx;
      by_cases hx : x = M₁.root.1;
      . subst hx; exact hnA hAx;
      . have hlt : Model.World.rank x < M₁.height := RootedModel.rank_lt_height (M₁.root.2 x hx);
        have : x ⊩ TBB (Model.World.rank x) := by
          apply Model.World.forces_fconj.mp hTx;
          apply Finset.mem_image_of_mem;
          simp only [R, Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.coe_range, Set.mem_Iio];
          exact ⟨hlt, hmem⟩;
        exact Model.iff_forces_TBB_neq_rank.mp this rfl;
    . -- the new root: the reflexive main lemma kills `A`, hence `B`
      have H₁ : 𝗜𝚺₁ ⊢ S.σ (Sum.inr i) 🡒 ∼(A.interpret S.realization) := by
        rw [show (Sum.inr i : (M₁.extendRoot 1).World) = (M₁.extendRoot 1).root.1 by
          congr 1;
          apply Fin.ext;
          have := i.2;
          simp only [Fin.posLast, PNat.natPred, PNat.val_ofNat] at this ⊢;
          omega];
        exact SolovaySentences.rfl_mainlemma ha (Formula.mem_subfmls_self) |>.2 hnA;
      simp only [B, Formula.interpret];
      cl_prover [H₁];
  have main : 𝗜𝚺₁ ⊢ ((B 🡒 (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α)).interpret S.realization) := by
    have := left_Udisj!_intro _ key;
    cl_prover [this, S.SC4];
  -- Conclude membership in `L` via letterless independence of the realization.
  intro f;
  have h₃ : U ⊢ ((LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret S.realization) := by
    have h₁ : U ⊢ (B.interpret S.realization) 🡒
        ((LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret S.realization) :=
      WeakerThan.pbl main;
    exact h₁ ⨀ (hB S.realization);
  have e : ∀ g : StandardRealization α T,
      (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret g
      = LetterlessFormula.interpret T.standardProvability (TBBMinus _ hcof) := by
    intro g;
    rw [LetterlessFormula.interpret_lift];
  show U ⊢ (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret f;
  rw [e f];
  rw [e S.realization] at h₃;
  exact h₃;

/--
  **Lemma 49 in [AB05]**: if the provability logic `L` of `T` relative to `U` is not
  contained in `S`, then `L.trace` is cofinite and `L = GLβ⁻ (L.trace)`.
-/
theorem eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS
    (hS : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ LogicS) :
    (T.provabilityLogicRelativeTo U : Logic α)
      = LogicGLBetaMinus (T.provabilityLogicRelativeTo U : Logic α).trace
          (cofinite_trace_of_not_subset_LogicS hS) := by
  apply Set.Subset.antisymm;
  . exact subset_LogicGLBetaMinus_of_trace_cofinite _;
  . intro A hA;
    induction hA with
    | mem₁ hA =>
      exact provabilityLogic_of_GL hA;
    | mem₂ hA =>
      obtain ⟨B, hB, rfl⟩ := hA;
      rw [show B = TBBMinus _ (cofinite_trace_of_not_subset_LogicS hS) from hB];
      exact provable_TBBMinus_of_not_subset_LogicS hS;
    | mdp _ _ ihAB ihA =>
      exact provabilityLogic_mdp ihAB ihA;
    | subst _ ihA =>
      intro f;
      rw [Formula.interpret_subst];
      exact ihA _;

end

end

end
