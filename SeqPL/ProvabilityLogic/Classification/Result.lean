module

public import SeqPL.ProvabilityLogic.Classification.A_D
public import SeqPL.ProvabilityLogic.Classification.D_S
public import SeqPL.ProvabilityLogic.S.Basic

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

section univ_trace

/--
  If the provability logic of `T` relative to `U` has trace `ω` and is contained in `S`,
  then it is one of `GLαω`, `D`, and `S`. Assertion 3 in [Bek90].
-/
lemma classification_LogicS_sublogics_of_univ_trace :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → L ⊆ LogicS →
    L = LogicA ∨ L = LogicD ∨ L = LogicS := by
  intro hT hS;
  rcases Set.eq_or_ssubset_of_subset (subset_LogicA_of_univ_trace hT)
    with h | hGLαω;
  case inl => exact Or.inl h.symm;
  rcases Set.eq_or_ssubset_of_subset
    (subset_LogicD_of_ssubset_LogicA_of_univ_trace hT hGLαω) with h | hD;
  case inl => exact Or.inr (Or.inl h.symm);
  exact Or.inr (Or.inr (Set.Subset.antisymm hS
    (subset_LogicS_of_ssubset_LogicD_of_univ_trace hT hD)));

end univ_trace


section cofinite_trace

variable [DecidableEq α]

section modal

omit [DecidableEq α] in
/-- `GLα` is monotone in the trace set. -/
lemma LogicGLAlpha.mono {Alpha Alpha' : Set ℕ} (h : Alpha ⊆ Alpha') :
    (LogicGLAlpha Alpha : Logic α) ⊆ LogicGLAlpha Alpha' := by
  apply Logic.sumQuasiNormal.iff_subset.mpr;
  rintro A ⟨B, ⟨n, hn, rfl⟩, rfl⟩;
  exact Logic.sumQuasiNormal.mem₂ ⟨TBB n, ⟨n, h hn, rfl⟩, rfl⟩;

/-- `GLα Beta ⊆ GLβ⁻ Beta` for cofinite `Beta` (both have trace `Beta`, and `GLβ⁻` is the largest). -/
lemma LogicGLAlpha.subset_LogicGLBetaMinus {Beta : Set ℕ} (hCf : Betaᶜ.Finite) :
    (LogicGLAlpha Beta : Logic α) ⊆ LogicGLBetaMinus Beta hCf := by
  apply Logic.sumQuasiNormal.iff_subset.mpr;
  rintro A ⟨B, ⟨n, hn, rfl⟩, rfl⟩;
  apply iff_GL_sumQuasiNormal_proves_subset_spectrum (T := 𝗜𝚺₁)
    (Or.inr LetterlessFormula.regular_TBB) |>.mpr;
  intro k hk;
  have hk' : k ∈ LetterlessFormula.spectrum (TBBMinus _ hCf) := by
    simpa [LetterlessFormulaSet.eq_spectrum] using hk;
  have hsp : LetterlessFormula.spectrum (TBBMinus _ hCf) = Betaᶜ := by
    have h := LetterlessFormula.trace_TBBMinus (s := Betaᶜ) hCf;
    rw [LetterlessFormula.trace, compl_inj_iff] at h;
    exact h;
  rw [hsp] at hk';
  rw [LetterlessFormula.spectrum_TBB];
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff];
  rintro rfl;
  exact hk' hn;

/--
  `GLα Beta = GLαω ∩ GLβ⁻ Beta` for cofinite `Beta`: the `η`/`ξ` correspondence of [AB05]
  evaluated at `GLα Beta`, proved via the finite compactness
  `GL_sumQuasiNormal_finite_provable` (note `Betaᶜ` is finite).
-/
lemma eq_LogicGLAlpha_inter_LogicA_LogicGLBetaMinus {Beta : Set ℕ} (hCf : Betaᶜ.Finite) :
    (LogicGLAlpha Beta : Logic α) = LogicA ∩ LogicGLBetaMinus Beta hCf := by
  apply Set.Subset.antisymm;
  . exact Set.subset_inter (LogicGLAlpha.mono (Set.subset_univ Beta))
      (LogicGLAlpha.subset_LogicGLBetaMinus hCf);
  . rintro A ⟨h₁, h₂⟩;
    obtain ⟨Y₁, hY₁, hGL₁⟩ := GL_sumQuasiNormal_finite_provable h₁;
    obtain ⟨Y₂, hY₂, hGL₂⟩ := GL_sumQuasiNormal_finite_provable h₂;
    -- Recover the index set of `Y₁` and split it along `Beta`.
    obtain ⟨N, -, hN_cov⟩ := finite_preimage_choice Y₁ Set.univ TBB
      (fun C hC => by simpa using hY₁ C hC);
    let NBeta : Finset ℕ := N.filter (· ∈ Beta);
    let F : Finset ℕ := hCf.toFinset;
    have sub₁ : Y₁ ⊆ (NBeta.image TBB) ∪ (F.image TBB) := by
      intro C hC;
      obtain ⟨n, hnN, rfl⟩ := hN_cov C hC;
      by_cases hnBeta : n ∈ Beta;
      . exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (by simp [NBeta, hnN, hnBeta]));
      . exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (by simp [F, hnBeta]));
    -- `⊢ʰ ⋀TBB(NBeta) 🡒 ⋀TBB(F) 🡒 ⋀TBB(NBeta ∪-image F)` at the letterless level.
    have s₁ : (⊢ʰ ((LetterlessFormula.lift (⋀((NBeta.image TBB) ∪ (F.image TBB))) : Formula α)
        🡒 A)) := by
      have w₁ : (⊢ʰ ((LetterlessFormula.lift (⋀((NBeta.image TBB) ∪ (F.image TBB))) : Formula α)
          🡒 LetterlessFormula.lift (⋀Y₁))) := by
        simpa [LetterlessFormula.lift] using ProvableHilbert.lift (α := α)
          (ProvableHilbert.imp_fconj_fconj_of_subset sub₁);
      exact ProvableHilbert.impTrans w₁ hGL₁;
    -- Merge lemma for finite conjunctions, semantically.
    have merge : (⊢ʰ ((LetterlessFormula.lift (⋀(NBeta.image TBB)) : Formula α)
        🡒 (LetterlessFormula.lift (⋀(F.image TBB)) : Formula α)
        🡒 (LetterlessFormula.lift (⋀((NBeta.image TBB) ∪ (F.image TBB))) : Formula α))) := by
      have : (⊢ʰ ((⋀(NBeta.image TBB) : LetterlessFormula)
          🡒 (⋀(F.image TBB)) 🡒 (⋀((NBeta.image TBB) ∪ (F.image TBB))))) := by
        apply ProvableHilbert.Kripke.completeness;
        intro κ _ M _ x;
        simp only [Model.World.forces_imp];
        by_cases hx : x ⊩ (⋀(NBeta.image TBB) : LetterlessFormula);
        . by_cases hy : x ⊩ (⋀(F.image TBB) : LetterlessFormula);
          . right; right;
            apply Model.World.forces_fconj.mpr;
            intro C hC;
            rcases Finset.mem_union.mp hC with hC | hC;
            . exact Model.World.forces_fconj.mp hx C hC;
            . exact Model.World.forces_fconj.mp hy C hC;
          . right; left; exact hy;
        . left; exact hx;
      simpa [LetterlessFormula.lift] using ProvableHilbert.lift (α := α) this;
    -- Compose: `⊢ʰ ⋀TBB(NBeta) 🡒 ⋀TBB(F) 🡒 A`.
    have c₂ : (⊢ʰ ((LetterlessFormula.lift (⋀(NBeta.image TBB)) : Formula α)
        🡒 (LetterlessFormula.lift (⋀(F.image TBB)) : Formula α) 🡒 A)) := by
      have t : (⊢ʰ (((LetterlessFormula.lift (⋀(NBeta.image TBB)) : Formula α)
          🡒 (LetterlessFormula.lift (⋀(F.image TBB)) : Formula α)
          🡒 (LetterlessFormula.lift (⋀((NBeta.image TBB) ∪ (F.image TBB))) : Formula α))
          🡒 ((LetterlessFormula.lift (⋀((NBeta.image TBB) ∪ (F.image TBB))) : Formula α) 🡒 A)
          🡒 ((LetterlessFormula.lift (⋀(NBeta.image TBB)) : Formula α)
            🡒 (LetterlessFormula.lift (⋀(F.image TBB)) : Formula α) 🡒 A))) := by
        apply ProvableHilbert.Kripke.completeness;
        intro κ _ M _ x;
        simp only [Model.World.forces_imp];
        tauto;
      exact ProvableHilbert.mdp (ProvableHilbert.mdp t merge) s₁;
    -- The `GLβ⁻` axiom gives `⊢ʰ ∼⋀TBB(F) 🡒 A`.
    have c₃ : (⊢ʰ ((∼(LetterlessFormula.lift (⋀(F.image TBB)) : Formula α)) 🡒 A)) := by
      have w₂ : (⊢ʰ ((TBBMinus _ hCf : LetterlessFormula) 🡒 (⋀Y₂ : LetterlessFormula))) := by
        have := ProvableHilbert.imp_fconj_fconj_of_subset
          (Γ := ({TBBMinus _ hCf} : LetterlessFormulaFinset)) (Γ' := Y₂)
          (fun C hC => by simpa using hY₂ C hC);
        rwa [show ((⋀({TBBMinus _ hCf} : LetterlessFormulaFinset)) : LetterlessFormula)
          = TBBMinus _ hCf by simp] at this;
      have := ProvableHilbert.impTrans (ProvableHilbert.lift (α := α) w₂) hGL₂;
      simpa [LetterlessFormula.lift, TBBMinus] using this;
    -- Excluded middle on `⋀TBB(F)` finishes: `⊢ʰ ⋀TBB(NBeta) 🡒 A`.
    have final : (⊢ʰ ((LetterlessFormula.lift (⋀(NBeta.image TBB)) : Formula α) 🡒 A)) := by
      have t₂ : (⊢ʰ (((LetterlessFormula.lift (⋀(NBeta.image TBB)) : Formula α)
          🡒 (LetterlessFormula.lift (⋀(F.image TBB)) : Formula α) 🡒 A)
          🡒 ((∼(LetterlessFormula.lift (⋀(F.image TBB)) : Formula α)) 🡒 A)
          🡒 ((LetterlessFormula.lift (⋀(NBeta.image TBB)) : Formula α) 🡒 A))) := by
        apply ProvableHilbert.Kripke.completeness;
        intro κ _ M _ x;
        simp only [Model.World.forces_imp, Model.World.not_forces_imp];
        tauto;
      exact ProvableHilbert.mdp (ProvableHilbert.mdp t₂ c₂) c₃;
    exact GL_sumQuasiNormal_of_finite_provable
      (fun C hC => by
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hC;
        exact ⟨n, (Finset.mem_filter.mp hn).2, rfl⟩)
      final;

omit [DecidableEq α] in
/-- `S` proves every `TBB n`, as a substitution instance of the axiom `T`. -/
lemma LogicS.provable_TBB {n : ℕ} : (TBB n : Formula α) ∈ LogicS := by
  simpa [TBB, Formula.boxItr, Function.iterate_succ_apply'] using
    LogicS.provable_axiomT (A := (□^[n]⊥ : Formula α));


end modal


section addTBB

open LetterlessFormula

/-- `U` extended by the standard `T`-interpretations of `TBB n` for `n ∈ N`. -/
noncomputable abbrev _root_.LO.FirstOrder.ArithmeticTheory.addTBB
    (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] (N : Set ℕ) : FirstOrder.ArithmeticTheory :=
  U ∪ (N.image (fun n => LetterlessFormula.standardInterpret T (TBB n)))

variable {N : Set ℕ}

omit [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] in
/-- `U` is weaker than its extension by `TBB` interpretations. -/
lemma _root_.LO.FirstOrder.ArithmeticTheory.addTBB.weakerThan : U ⪯ T.addTBB U N :=
  inferInstance

omit [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [DecidableEq α] in
/-- The provability logic only grows when axioms are added to `U`. -/
lemma provabilityLogic_subset_addTBB :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    letI L' : Logic α := T.provabilityLogicRelativeTo (T.addTBB U N);
    L ⊆ L' := by
  intro A hA f;
  exact Entailment.WeakerThan.wk FirstOrder.ArithmeticTheory.addTBB.weakerThan (hA f);

omit [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [DecidableEq α] in
/-- The added `TBB` axioms are theorems of the extended provability logic. -/
lemma provable_TBB_addTBB_of_mem {n : ℕ} (hn : n ∈ N) :
    (TBB n : Formula α) ∈ (T.provabilityLogicRelativeTo (T.addTBB U N) : Logic α) := by
  intro f;
  rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  apply Entailment.by_axm;
  simp only [Set.mem_union];
  exact Or.inr ⟨n, hn, rfl⟩;

omit [DecidableEq α] in
/--
  Deduction: if `A` is in the provability logic relative to `U + TBB-axioms` for a
  finite `N`, then `⋀TBB(N) 🡒 A` is in the provability logic relative to `U`.
  Uses the finiteness of `N` and realization-independence of letterless interpretations.
-/
lemma imp_fconjTBB_mem_provabilityLogic_of_mem_addTBB (hN : N.Finite) :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    letI L' : Logic α := T.provabilityLogicRelativeTo (T.addTBB U N);
    ∀ {A : Formula α}, A ∈ L' →
      ((LetterlessFormula.lift (⋀(hN.toFinset.image TBB)) : Formula α) 🡒 A) ∈ L := by
  intro A hA f;
  obtain ⟨⟨s, hs_sub⟩, hs⟩ := LO.FirstOrder.Theory.compact_add_right (hA f);
  show U ⊢ (Formula.interpret f (LetterlessFormula.lift (⋀(hN.toFinset.image TBB)) : Formula α))
    🡒 (Formula.interpret f A);
  apply Entailment.C!_trans ?_ hs;
  apply right_Fconj!_intro;
  intro σ hσ;
  obtain ⟨n, hn, rfl⟩ := hs_sub hσ;
  have hGL : ((LetterlessFormula.lift ((⋀(hN.toFinset.image TBB)) 🡒 TBB n) : Formula α))
      ∈ LogicGL := by
    apply ProvableHilbert.lift;
    have := ProvableHilbert.imp_fconj_fconj_of_subset
      (Γ := hN.toFinset.image TBB) (Γ' := ({TBB n} : LetterlessFormulaFinset))
      (Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ (hN.mem_toFinset.mpr hn)));
    rwa [show ((⋀({TBB n} : LetterlessFormulaFinset)) : LetterlessFormula) = TBB n by simp]
      at this;
  have hU : U ⊢ Formula.interpret f
      ((LetterlessFormula.lift ((⋀(hN.toFinset.image TBB)) 🡒 TBB n) : Formula α)) :=
    WeakerThan.pbl (LogicGL.arithmetical_soundness hGL);
  have e : Formula.interpret f (LetterlessFormula.lift ((⋀(hN.toFinset.image TBB)) 🡒 TBB n) : Formula α)
      = (Formula.interpret f (LetterlessFormula.lift (⋀(hN.toFinset.image TBB)) : Formula α))
        🡒 (LetterlessFormula.standardInterpret T (TBB n)) := by
    rw [show (LetterlessFormula.lift ((⋀(hN.toFinset.image TBB)) 🡒 TBB n) : Formula α)
      = (LetterlessFormula.lift (⋀(hN.toFinset.image TBB)) : Formula α) 🡒 (LetterlessFormula.lift (TBB n)) from rfl];
    simp only [Formula.interpret, LetterlessFormula.interpret_lift];
  rwa [e] at hU;

end addTBB


section

variable (hCf : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite)

omit [DecidableEq α] in
/--
  Adjoining the missing `TBB` axioms yields a provability logic of trace `ω`.
-/
lemma trace_univ_addTBB_compl_trace :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    letI L' : Logic α := T.provabilityLogicRelativeTo (T.addTBB U L.traceᶜ);
    L'.trace = Set.univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_of_provable_TBB (α := α);
  by_cases hn : n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace;
  . exact provabilityLogic_subset_addTBB (provable_TBB_of_mem_trace hn);
  . exact provable_TBB_addTBB_of_mem hn;

include hCf in
/--
  If `L ⊆ S`, the extension by the missing `TBB` axioms is still contained in `S`
  (otherwise, by Lemma 49, it would equal `GLβ⁻ ω` which is inconsistent, contradicting
  the consistency of `S`).
-/
lemma subset_LogicS_addTBB_compl_trace_of_subset_LogicS :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    letI L' : Logic α := T.provabilityLogicRelativeTo (T.addTBB U L.traceᶜ);
    L ⊆ LogicS → L' ⊆ LogicS := by
  intro hS;
  by_contra hS';
  haveI hUW : U ⪯ T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ :=
    FirstOrder.ArithmeticTheory.addTBB.weakerThan;
  haveI : 𝗜𝚺₁ ⪯ T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ :=
    Entailment.WeakerThan.trans (inferInstanceAs (𝗜𝚺₁ ⪯ U)) hUW;
  -- By Lemma 49 the extended logic is `GLβ⁻` of its trace `ω`, hence inconsistent.
  have h49 := eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hS';
  set pf := cofinite_trace_of_not_subset_LogicS hS';
  have hτ : (T.provabilityLogicRelativeTo
      (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) : Logic α).trace
      = Set.univ := trace_univ_addTBB_compl_trace;
  have hbot : (⊥ : Formula α) ∈ (T.provabilityLogicRelativeTo
      (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) : Logic α) := by
    rw [h49];
    apply Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ ?_)
      (Logic.sumQuasiNormal.mem₂ ⟨TBBMinus _ pf, rfl, rfl⟩);
    have hD : (((TBBMinus _ pf : LetterlessFormula)) 🡒 ⊥) ∈ LogicGL := by
      apply iff_GL_proves_imp_GL_subset_spectrum.mpr;
      have hsp : LetterlessFormula.spectrum (TBBMinus _ pf) = ∅ := by
        have h := LetterlessFormula.trace_TBBMinus
          (s := (T.provabilityLogicRelativeTo
            (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) : Logic α).traceᶜ) pf;
        rw [LetterlessFormula.trace, compl_inj_iff] at h;
        rw [h, hτ];
        simp;
      rw [hsp];
      exact Set.empty_subset _;
    exact ProvableHilbert.lift (α := α) hD;
  -- Deduce `∼⋀TBB(traceᶜ) ∈ L ⊆ S`, while `⋀TBB(traceᶜ) ∈ S`: contradiction with consistency.
  have hded : ((LetterlessFormula.lift (⋀(hCf.toFinset.image TBB)) : Formula α) 🡒 ⊥)
      ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
    imp_fconjTBB_mem_provabilityLogic_of_mem_addTBB hCf hbot;
  have hC₀S : (LetterlessFormula.lift (⋀(hCf.toFinset.image TBB)) : Formula α)
      ∈ LogicS := by
    have hconj : (⋀(hCf.toFinset.image (TBB : ℕ → Formula α))) ∈ LogicS := by
      apply LogicS.provable_fconj_of_forall_provable;
      intro B hB;
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hB;
      exact LogicS.provable_TBB;
    have hbr : ((⋀(hCf.toFinset.image (TBB : ℕ → Formula α)))
        🡒 (LetterlessFormula.lift (⋀(hCf.toFinset.image TBB)) : Formula α))
        ∈ LogicGL := by
      apply LogicGL.iff_forces_root.mpr;
      intro κ _ M _;
      haveI : Fintype M.World := Fintype.ofFinite _;
      apply Model.World.forces_imp.mpr;
      by_cases hx : M.root.1 ⊩ ⋀(hCf.toFinset.image (TBB : ℕ → Formula α));
      . right;
        apply Model.iff_forces_lift_rank_mem_spectrum.mpr;
        rw [LetterlessFormula.spectrum_fconj];
        apply Set.mem_iInter₂.mpr;
        intro B hB;
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hB;
        rw [LetterlessFormula.spectrum_TBB];
        have : M.root.1 ⊩ (TBB n : Formula α) :=
          Model.World.forces_fconj.mp hx _ (Finset.mem_image_of_mem _ hn);
        simpa using Model.iff_forces_TBB_neq_rank.mp this;
      . left; exact hx;
    exact Logic.sumQuasiNormal.mdp (LogicS.provable_of_provable_GL hbr) hconj;
  exact LogicS.consistent (Logic.sumQuasiNormal.mdp (hS hded) hC₀S);

/--
  `L = L'' ∩ GLβ⁻ (L.trace)` where `L''` is the extension of `L` by the missing `TBB`
  axioms: the `η ∘ ξ = id` part of the correspondence in [AB05].
-/
lemma eq_provabilityLogic_inter_addTBB_LogicGLBetaMinus :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    letI L' : Logic α := T.provabilityLogicRelativeTo (T.addTBB U L.traceᶜ);
    L = L' ∩ LogicGLBetaMinus L.trace hCf := by
  apply Set.Subset.antisymm;
  . exact Set.subset_inter provabilityLogic_subset_addTBB
      (subset_LogicGLBetaMinus_of_trace_cofinite hCf);
  . rintro A ⟨h₁, h₂⟩;
    -- From membership in the extension: `⋀TBB(traceᶜ) 🡒 A ∈ L`.
    have d₁ : ((LetterlessFormula.lift (⋀(hCf.toFinset.image TBB)) : Formula α) 🡒 A)
        ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
      imp_fconjTBB_mem_provabilityLogic_of_mem_addTBB hCf h₁;
    -- From membership in `GLβ⁻`: `∼⋀TBB(traceᶜ) 🡒 A ∈ GL ⊆ L`.
    have d₂ : ((∼(LetterlessFormula.lift (⋀(hCf.toFinset.image TBB)) : Formula α)) 🡒 A)
        ∈ LogicGL := by
      obtain ⟨Y₂, hY₂, hGL₂⟩ := GL_sumQuasiNormal_finite_provable h₂;
      have w₂ : (⊢ʰ ((TBBMinus _ hCf : LetterlessFormula) 🡒 (⋀Y₂ : LetterlessFormula))) := by
        have := ProvableHilbert.imp_fconj_fconj_of_subset
          (Γ := ({TBBMinus _ hCf} : LetterlessFormulaFinset)) (Γ' := Y₂)
          (fun C hC => by simpa using hY₂ C hC);
        rwa [show ((⋀({TBBMinus _ hCf} : LetterlessFormulaFinset)) : LetterlessFormula)
          = TBBMinus _ hCf by simp] at this;
      have := ProvableHilbert.impTrans (ProvableHilbert.lift (α := α) w₂) hGL₂;
      simpa [LetterlessFormula.lift, TBBMinus] using this;
    -- Case split on `⋀TBB(traceᶜ)` in `L`.
    have lem : (((LetterlessFormula.lift (⋀(hCf.toFinset.image TBB)) : Formula α) 🡒 A)
        🡒 ((∼(LetterlessFormula.lift (⋀(hCf.toFinset.image TBB)) : Formula α)) 🡒 A) 🡒 A)
        ∈ LogicGL := by
      apply ProvableHilbert.Kripke.completeness;
      intro κ _ M _ x;
      simp only [Model.World.forces_imp, Model.World.not_forces_imp];
      tauto;
    exact provabilityLogic_mdp (provabilityLogic_mdp (provabilityLogic_of_GL lem) d₁)
      (provabilityLogic_of_GL d₂);

end

/--
  If the provability logic of `T` relative to `U` has cofinite trace `Beta` and is
  contained in `S`, then it is one of `GLα Beta`, `D ∩ GLβ⁻ Beta`, and `S ∩ GLβ⁻ Beta`.
  Obtained from the
  `ω`-trace classification by adjoining the missing `TBB` axioms (`αPL` in Foundation's
  `ProvabilityLogic.Classification.Result`) and intersecting back with `GLβ⁻ β`.
-/
lemma classification_LogicS_sublogics_of_cofinite_trace :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    ∀ (hCf : L.traceᶜ.Finite), L ⊆ LogicS →
      L = LogicGLAlpha L.trace ∨
      L = LogicD ∩ LogicGLBetaMinus L.trace hCf ∨
      L = LogicS ∩ LogicGLBetaMinus L.trace hCf := by
  intro hCf hS;
  haveI hUW : U ⪯ T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ :=
    FirstOrder.ArithmeticTheory.addTBB.weakerThan;
  haveI : 𝗜𝚺₁ ⪯ T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ :=
    Entailment.WeakerThan.trans (inferInstanceAs (𝗜𝚺₁ ⪯ U)) hUW;
  have hInter := eq_provabilityLogic_inter_addTBB_LogicGLBetaMinus (T := T) (U := U) (α := α) hCf;
  rcases classification_LogicS_sublogics_of_univ_trace
    (U := T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ)
    trace_univ_addTBB_compl_trace
    (subset_LogicS_addTBB_compl_trace_of_subset_LogicS hCf hS) with h | h | h;
  . left;
    conv_lhs => rw [hInter];
    rw [h];
    exact (eq_LogicGLAlpha_inter_LogicA_LogicGLBetaMinus hCf).symm;
  . right; left;
    conv_lhs => rw [hInter];
    rw [h];
  . right; right;
    conv_lhs => rw [hInter];
    rw [h];

end cofinite_trace


open Classical in
/--
  **The classification theorem of provability logics.**
  Let `L` be the provability logic of `T` relative to `U`.
  - If `L.trace` is coinfinite, then `L = GLα (L.trace)`.
  - Otherwise `L.trace` is cofinite (by `Formula.trace_finite_or_cofinite`), and:
    - if `L ⊄ S`, then `L = GLβ⁻ (L.trace)`;
    - if `L ⊆ S`, then `L` is one of `GLα (L.trace)`, `D ∩ GLβ⁻ (L.trace)`,
      and `S ∩ GLβ⁻ (L.trace)`.

  Assertion 6 in [Bek90]; Theorem 40 in [AB05].
-/
theorem classification_provability_logics [DecidableEq α] :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    if h_coinfinite : L.traceᶜ.Infinite then
      L = LogicGLAlpha L.trace
    else
      haveI h_cofinite : L.traceᶜ.Finite := Set.not_infinite.mp h_coinfinite;
      if ¬(L ⊆ LogicS) then
        L = LogicGLBetaMinus L.trace h_cofinite
      else
        L = LogicGLAlpha L.trace ∨
        L = LogicD ∩ LogicGLBetaMinus L.trace h_cofinite ∨
        L = LogicS ∩ LogicGLBetaMinus L.trace h_cofinite
    := by
  split_ifs with h_coinfinite h_S;
  . exact eq_provabilityLogic_LogicGLAlpha_of_coinfinite_trace h_coinfinite;
  . exact classification_LogicS_sublogics_of_cofinite_trace
      (Set.not_infinite.mp h_coinfinite) h_S;
  . exact eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS h_S;


/-!
# Classification of truth provability logics (Corollary 41 in [AB05])

The truth provability logics, i.e. the logics of the form `PL_T(𝗧𝗔)`, are precisely
`S`, `D`, `GLαω`, and `GLβ⁻ {n}ᶜ` (`= GL{∼TBB n}`), according to the soundness
properties of `T`:

- `PL_T(𝗧𝗔) = S` iff `T` is sound;
- `PL_T(𝗧𝗔) = D` iff `T` is `Σ₁`-sound but not sound;
- `PL_T(𝗧𝗔) = GLαω` iff `T` is not `Σ₁`-sound but of infinite characteristic;
- `PL_T(𝗧𝗔) = GLβ⁻ {n}ᶜ` iff `T` has characteristic `n` (i.e. `T.height = n`).
-/

section trueArith

/--
  Corollary 41(i) in [AB05], the `⇐` direction (Solovay's second theorem): the truth
  provability logic of a sound theory is `S`.
-/
theorem eq_provabilityLogic_TA_LogicS_of_sound [DecidableEq α] [ℕ↓[ℒₒᵣ] ⊧* T] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicS := by
  have hSL : (LogicS : Logic α) ⊆ T.provabilityLogicRelativeTo 𝗧𝗔 := fun A hA f =>
    Arithmetic.TA.provable_iff.mpr (LogicS.arithmetical_soundness hA f);
  have hLS : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ LogicS := fun A hA =>
    LogicS.arithmetical_completeness (fun f => Arithmetic.TA.provable_iff.mp (hA f));
  have hT : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ := by
    apply Set.eq_univ_of_forall;
    intro n;
    exact mem_trace_of_provable_TBB (hSL LogicS.provable_TBB);
  rcases classification_LogicS_sublogics_of_univ_trace (T := T) (U := 𝗧𝗔) hT hLS
    with h | h | h;
  . rw [h];
    exact Set.Subset.antisymm subset_LogicGLAlpha_LogicS (h ▸ hSL);
  . rw [h];
    exact Set.Subset.antisymm LogicS_subset_LogicD (h ▸ hSL);
  . exact h;

/--
  **Corollary 41(i) in [AB05]**: for a type of atoms with at least one element, the truth
  provability logic of `T` is `S` iff `T` is sound. (Some atom is needed for the forward
  direction: over `Empty` every theory of infinite characteristic has truth provability
  logic `S`, since all letterless logics between `GLαω` and `S` coincide.)
-/
theorem eq_provabilityLogic_TA_LogicS_iff [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicS ↔ ℕ↓[ℒₒᵣ] ⊧* T := by
  constructor;
  . intro h;
    apply LO.Semantics.modelsSet_iff.mpr;
    intro φ hφ;
    obtain ⟨p⟩ := ‹Nonempty α›;
    -- the reflection principle for `T` is true, and axioms of `T` are provable
    have hax : ((□(#p)) 🡒 (#p)) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
      rw [h];
      exact LogicS.provable_axiomT;
    have hrfl : ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability φ) 🡒 φ) :=
      Arithmetic.TA.provable_iff.mp
        (hax ⟨fun _ => φ⟩);
    have hprov : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability φ) :=
      models_of_provable inferInstance (T.standardProvability.D1 (Entailment.by_axm hφ));
    have himp : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability φ) → ℕ↓[ℒₒᵣ] ⊧ φ := by simpa using hrfl;
    exact himp hprov;
  . intro h;
    exact eq_provabilityLogic_TA_LogicS_of_sound;

/--
  **Corollary 41(ii) in [AB05]**: the truth provability logic of `T` is `D` iff `T` is
  `Σ₁`-sound but not sound.
-/
theorem eq_provabilityLogic_TA_LogicD_iff [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicD ↔ (T.SoundOnHierarchy 𝚺 1 ∧ ¬(ℕ↓[ℒₒᵣ] ⊧* T)) := by
  -- The following `have`s reprove (locally, to avoid an import cycle with the
  -- `HeightTrace*.lean` files, which import this file) facts needed for both directions.
  have models_standardProvability_iff : ∀ {σ : ArithmeticSentence},
      ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ ↔ T ⊢ σ := by
    intro σ;
    constructor;
    . intro h; exact T.standardProvability.sound_on h;
    . intro h; exact models_of_provable inferInstance (T.standardProvability.D1 h);
  have not_models_standardProvability_bot :
      ¬ ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[0] ⊥) := by simp;
  have bot_notMem : (⊥ : Formula α) ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
    intro h;
    exact not_models_standardProvability_bot
      (Arithmetic.TA.provable_iff.mp (h (⟨fun _ => ⊥⟩ : StandardRealization α T)));
  constructor;
  . intro h;
    have hSigma1Refl : ∀ {σ : ArithmeticSentence}, LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 σ →
        ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability σ) 🡒 σ) := by
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
    constructor;
    . constructor;
      intro σ hTσ hσ;
      exact (Semantics.Imp.models_imply.mp (hSigma1Refl hσ)) (models_standardProvability_iff.mpr hTσ);
    . intro hsound;
      haveI : ℕ↓[ℒₒᵣ] ⊧* T := hsound;
      have hS : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = LogicS :=
        eq_provabilityLogic_TA_LogicS_of_sound;
      obtain ⟨a⟩ := ‹Nonempty α›;
      have hT : ((□(#a) : Formula α) 🡒 #a) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) :=
        hS ▸ LogicS.provable_axiomT;
      exact LogicD.not_provable_axiomT (h ▸ hT);
  . rintro ⟨hSig, hsound⟩;
    haveI := hSig;
    -- `LogicD ⊆ L` (mirrors `LogicD_subset_provabilityLogicRelativeTo_TA`).
    have hDL : (LogicD : Logic α) ⊆ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
      intro A hA;
      induction hA using LogicD.substlessInduction with
      | provable_GL hGL => exact provabilityLogic_of_GL hGL;
      | axiomP =>
        intro f;
        apply Arithmetic.TA.provable_iff.mpr;
        have e : Formula.interpret f (∼□⊥ : Formula α)
            = (T.standardProvability (⊥ : ArithmeticSentence)) 🡒 ⊥ := by
          simp [Formula.interpret];
        rw [e, Semantics.Imp.models_imply];
        intro hh;
        exact absurd (models_standardProvability_iff.mp hh)
          (inferInstance : Entailment.Consistent T).not_bot;
      | @axiomD B C =>
        intro f;
        apply Arithmetic.TA.provable_iff.mpr;
        have hσ : LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 (f (((□B) ⋎ (□C) : Formula α))) := by
          simp [Formula.interpret, Arithmetic.standardProvability_def];
        have hrfl :
            ℕ↓[ℒₒᵣ] ⊧
              (T.standardProvability (f (((□B) ⋎ (□C) : Formula α))) 🡒
                f (((□B) ⋎ (□C) : Formula α))) := by
          rw [Semantics.Imp.models_imply];
          intro hh;
          exact ArithmeticTheory.soundOnHierarchy T 𝚺 1 (models_standardProvability_iff.mp hh) hσ;
        simpa [Formula.interpret] using hrfl;
      | mdp ihAB ihA => exact provabilityLogic_mdp ihAB ihA;
    have hheight : T.height = (⊤ : ℕ∞) := Arithmetic.height_eq_top_of_sigma1_sound T;
    -- `L.trace = ω` (mirrors `trace_provabilityLogicRelativeTo_TA_eq_univ_iff`).
    have models_iterate_standardProvability_bot_iff : ∀ {m : ℕ},
        ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m + 1] ⊥) ↔ T.height ≤ m := by
      intro m;
      rw [Function.iterate_succ_apply', models_standardProvability_iff];
      exact Provability.height_le_iff_boxBot.symm;
    have models_standardInterpret_TBB_iff : ∀ {m : ℕ},
        ℕ↓[ℒₒᵣ] ⊧ (LetterlessFormula.standardInterpret T (TBB m) : ArithmeticSentence) ↔
        T.height ≠ m := by
      intro m;
      have e : LetterlessFormula.standardInterpret T (TBB m)
          = ((T.standardProvability^[m + 1] ⊥) 🡒 (T.standardProvability^[m] ⊥)) := by
        dsimp only [TBB, LetterlessFormula.standardInterpret, LetterlessFormula.interpret];
        rw [LetterlessFormula.interpret_boxItr, LetterlessFormula.interpret_boxItr];
        rfl;
      rw [e];
      have himp :
          ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability^[m + 1] ⊥) 🡒 (T.standardProvability^[m] ⊥)) ↔
          (ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m + 1] ⊥) →
            ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m] ⊥)) := by
        simp;
      rw [himp];
      rcases m with _ | k;
      . simp only [not_models_standardProvability_bot, imp_false,
          models_iterate_standardProvability_bot_iff];
        simp;
      . rw [models_iterate_standardProvability_bot_iff, models_iterate_standardProvability_bot_iff];
        rcases eq_top_or_lt_top T.height with hh | hh;
        . simp [hh, eq_comm];
        . obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hh.ne_top;
          rw [← hj];
          simp only [Nat.cast_le, ne_eq, Nat.cast_inj];
          omega;
    have eq_interpret_TBB : ∀ (f : StandardRealization α T) (m : ℕ),
        Formula.interpret f (TBB m) = LetterlessFormula.standardInterpret T (TBB m) := by
      intro f m;
      rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
    have mem_TBB_iff : ∀ {m : ℕ},
        (TBB m : Formula α) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ↔ T.height ≠ m := by
      intro m;
      constructor;
      . intro hh;
        rw [← models_standardInterpret_TBB_iff, ← eq_interpret_TBB ⟨fun _ => ⊥⟩ m];
        exact Arithmetic.TA.provable_iff.mp (hh ⟨fun _ => ⊥⟩);
      . intro hh f;
        rw [eq_interpret_TBB f m];
        exact Arithmetic.TA.provable_iff.mpr (models_standardInterpret_TBB_iff.mpr hh);
    have mem_trace_iff : ∀ {m : ℕ},
        m ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace ↔ T.height ≠ m := by
      intro m;
      rw [← mem_TBB_iff];
      exact ⟨provable_TBB_of_mem_trace, mem_trace_of_provable_TBB⟩;
    have hUniv : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ := by
      apply Set.eq_univ_of_forall;
      intro n;
      rw [mem_trace_iff, hheight];
      exact (ENat.coe_lt_top n).ne';
    -- `L ⊆ S` (mirrors `provabilityLogicRelativeTo_TA_subset_LogicS_of_trace_eq_univ`).
    have hLS : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ LogicS := by
      by_contra hS;
      have hCf : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).traceᶜ.Finite :=
        cofinite_trace_of_not_subset_LogicS hS;
      have hCf' : (Set.univ : Set ℕ)ᶜ.Finite := by simp;
      have heq : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = LogicGLBetaMinus Set.univ hCf' := by
        rw [eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hS];
        exact LogicGLBetaMinus.congr hUniv hCf hCf';
      exact bot_notMem (heq ▸ LogicGLBetaMinus.bot_mem_of_eq_univ);
    rcases classification_LogicS_sublogics_of_univ_trace (T := T) (U := 𝗧𝗔) hUniv hLS
      with h | h | h;
    . obtain ⟨a⟩ := ‹Nonempty α›;
      exact absurd (h ▸ hDL) (not_LogicD_subset_LogicA (a := a));
    . exact h;
    . exact absurd (eq_provabilityLogic_TA_LogicS_iff.mp h) hsound;

/--
  **Corollary 41(iii) in [AB05]**: the truth provability logic of `T` is `GLαω` iff `T`
  is not `Σ₁`-sound but of infinite characteristic.
-/
theorem eq_provabilityLogic_TA_LogicA_iff [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicA ↔ (¬(T.SoundOnHierarchy 𝚺 1) ∧ T.height = (⊤ : ℕ∞)) := by
  -- The following `have`s reprove (locally, to avoid an import cycle with
  -- `HeightTrace.lean`/`HeightTrace2.lean`/`HeightTrace3.lean`, which import this file) the
  -- connection between `T.height` and `TBB`'s truth in the standard model, in the style of
  -- `eq_provabilityLogic_TA_LogicGLBetaMinus_iff` above.
  have models_standardProvability_iff : ∀ {σ : ArithmeticSentence},
      ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ ↔ T ⊢ σ := by
    intro σ;
    constructor;
    . intro hh; exact T.standardProvability.sound_on hh;
    . intro hh; exact models_of_provable inferInstance (T.standardProvability.D1 hh);
  have models_iterate_standardProvability_bot_iff : ∀ {m : ℕ},
      ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m + 1] ⊥) ↔ T.height ≤ m := by
    intro m;
    rw [Function.iterate_succ_apply', models_standardProvability_iff];
    exact Provability.height_le_iff_boxBot.symm;
  have not_models_standardProvability_bot :
      ¬ ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[0] ⊥) := by simp;
  have models_standardInterpret_TBB_iff : ∀ {m : ℕ},
      ℕ↓[ℒₒᵣ] ⊧ (LetterlessFormula.standardInterpret T (TBB m) : ArithmeticSentence) ↔
      T.height ≠ m := by
    intro m;
    have e : LetterlessFormula.standardInterpret T (TBB m)
        = ((T.standardProvability^[m + 1] ⊥) 🡒 (T.standardProvability^[m] ⊥)) := by
      dsimp only [TBB, LetterlessFormula.standardInterpret, LetterlessFormula.interpret];
      rw [LetterlessFormula.interpret_boxItr, LetterlessFormula.interpret_boxItr];
      rfl;
    rw [e];
    have himp :
        ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability^[m + 1] ⊥) 🡒 (T.standardProvability^[m] ⊥)) ↔
        (ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m + 1] ⊥) → ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m] ⊥)) := by
      simp;
    rw [himp];
    rcases m with _ | k;
    . simp only [not_models_standardProvability_bot, imp_false,
        models_iterate_standardProvability_bot_iff];
      simp;
    . rw [models_iterate_standardProvability_bot_iff, models_iterate_standardProvability_bot_iff];
      rcases eq_top_or_lt_top T.height with hh | hh;
      . simp [hh, eq_comm];
      . obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hh.ne_top;
        rw [← hj];
        simp only [Nat.cast_le, ne_eq, Nat.cast_inj];
        omega;
  have eq_interpret_TBB : ∀ (f : StandardRealization α T) (m : ℕ),
      Formula.interpret f (TBB m) = LetterlessFormula.standardInterpret T (TBB m) := by
    intro f m;
    rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  have mem_trace_iff : ∀ {m : ℕ},
      m ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace ↔ T.height ≠ m := by
    intro m;
    constructor;
    . intro hh hcontra;
      have h1 : (TBB m : Formula α) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) :=
        provable_TBB_of_mem_trace hh;
      have h2 : ℕ↓[ℒₒᵣ] ⊧ (LetterlessFormula.standardInterpret T (TBB m) : ArithmeticSentence) := by
        rw [← eq_interpret_TBB ⟨fun _ => ⊥⟩ m];
        exact Arithmetic.TA.provable_iff.mp (h1 ⟨fun _ => ⊥⟩);
      exact (models_standardInterpret_TBB_iff.mp h2) hcontra;
    . intro hh;
      apply mem_trace_of_provable_TBB;
      intro f;
      rw [eq_interpret_TBB f m];
      exact Arithmetic.TA.provable_iff.mpr (models_standardInterpret_TBB_iff.mpr hh);
  have hTraceUnivIff : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ ↔
      T.height = (⊤ : ℕ∞) := by
    rw [Set.eq_univ_iff_forall];
    constructor;
    . intro hh;
      by_contra hcontra;
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hcontra;
      exact (mem_trace_iff.mp (hh n)) hn.symm;
    . intro hh n;
      rw [mem_trace_iff, hh];
      simp;
  -- Local reproof of half of Corollary 41(ii) (`LogicD_subset_provabilityLogicRelativeTo_TA`
  -- in `HeightTrace2.lean`): `D ⊆ L` when `T` is `Σ₁`-sound.
  have hDsubset : T.SoundOnHierarchy 𝚺 1 → (LogicD : Logic α) ⊆ (T.provabilityLogicRelativeTo 𝗧𝗔) := by
    intro hSig;
    haveI := hSig;
    have hReflImp : ∀ {σ : ArithmeticSentence}, LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 σ →
        ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability σ) 🡒 σ) := by
      intro σ hσ;
      rw [Semantics.Imp.models_imply];
      intro hh;
      exact ArithmeticTheory.soundOnHierarchy T 𝚺 1 (models_standardProvability_iff.mp hh) hσ;
    intro A hA;
    induction hA using LogicD.substlessInduction with
    | provable_GL hgl => exact provabilityLogic_of_GL hgl;
    | axiomP =>
      intro f;
      apply Arithmetic.TA.provable_iff.mpr;
      have e : Formula.interpret f (∼□⊥ : Formula α) = (T.standardProvability (⊥ : ArithmeticSentence)) 🡒 ⊥ := by
        simp [Formula.interpret];
      rw [e, Semantics.Imp.models_imply];
      intro hh;
      exact absurd (models_standardProvability_iff.mp hh) (inferInstance : Entailment.Consistent T).not_bot;
    | @axiomD B C =>
      intro f;
      apply Arithmetic.TA.provable_iff.mpr;
      have hσ : LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 (f (((□B) ⋎ (□C) : Formula α))) := by
        simp [Formula.interpret, Arithmetic.standardProvability_def];
      have hrfl := hReflImp hσ;
      simpa [Formula.interpret] using hrfl;
    | mdp ihAB ihA => exact provabilityLogic_mdp ihAB ihA;
  -- Local reproof of a fact needed for `provabilityLogicRelativeTo_TA_subset_LogicS_of_trace_eq_univ`
  -- (`HeightTrace4.lean`, via `bot_notMem_provabilityLogicRelativeTo_TA` in `HeightTrace3.lean`).
  have hbotTA : (⊥ : Formula α) ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
    intro hh;
    have hb : ℕ↓[ℒₒᵣ] ⊧ Formula.interpret (⟨fun _ => ⊥⟩ : StandardRealization α T) (⊥ : Formula α) :=
      Arithmetic.TA.provable_iff.mp (hh ⟨fun _ => ⊥⟩);
    simp [Formula.interpret] at hb;
  constructor;
  . intro h;
    have hTrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ := by
      rw [h]; exact LogicGLAlpha.eq_trace;
    constructor;
    . intro hSig;
      exact not_LogicD_subset_LogicA (α := α) (a := Classical.arbitrary α)
        (h ▸ hDsubset hSig);
    . exact hTraceUnivIff.mp hTrace;
  . rintro ⟨hSig, hHeight⟩;
    have hTrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ :=
      hTraceUnivIff.mpr hHeight;
    have hLS : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ LogicS := by
      by_contra hnS;
      have hCf : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).traceᶜ.Finite :=
        cofinite_trace_of_not_subset_LogicS hnS;
      have hCf' : (Set.univ : Set ℕ)ᶜ.Finite := by simp;
      have heq : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = LogicGLBetaMinus Set.univ hCf' := by
        rw [eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hnS];
        exact LogicGLBetaMinus.congr hTrace hCf hCf';
      exact hbotTA (heq ▸ LogicGLBetaMinus.bot_mem_of_eq_univ);
    rcases classification_LogicS_sublogics_of_univ_trace (T := T) (U := 𝗧𝗔) hTrace hLS
      with h | h | h;
    . exact h;
    . exfalso;
      apply hSig;
      obtain ⟨a⟩ := ‹Nonempty α›;
      have hAL : ((□((□(#a) : Formula α) ⋎ □(#a))) 🡒 ((□(#a) : Formula α) ⋎ □(#a))) ∈
          (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
        rw [h]; exact LogicD.provable_axiomD;
      have hAA := LogicA.not_provable_axiomD (α := α) (a := a);
      have hTtrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ := by
        apply Set.eq_univ_of_forall;
        intro n;
        exact mem_trace_of_provable_TBB (h ▸ LogicD.provable_TBB);
      have hreflU : ∀ {σ : ArithmeticSentence}, LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 σ →
          ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability σ) 🡒 σ) := by
        intro σ hσ;
        exact Arithmetic.TA.provable_iff.mp
          (provable_sigma1_reflection_of_mem_not_LogicA hTtrace hAL hAA σ hσ);
      constructor;
      intro σ hTσ hσ;
      exact (Semantics.Imp.models_imply.mp (hreflU hσ)) (models_standardProvability_iff.mpr hTσ);
    . have hFull : ℕ↓[ℒₒᵣ] ⊧* T := eq_provabilityLogic_TA_LogicS_iff.mp h;
      haveI := hFull;
      exact absurd (inferInstance : T.SoundOnHierarchy 𝚺 1) hSig;

/--
  **Corollary 41(iv) in [AB05]**: the truth provability logic of `T` is
  `GLβ⁻ {n}ᶜ = GL{∼TBB n}` iff `T` has characteristic `n`, i.e. `T.height = n`.
-/
theorem eq_provabilityLogic_TA_LogicGLBetaMinus_iff [DecidableEq α] {n : ℕ} :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicGLBetaMinus {n}ᶜ (by simp) ↔ T.height = n := by
  -- The following `have`s reprove (locally, to avoid an import cycle with
  -- `HeightTrace.lean`, which imports this file) the connection between `T.height`
  -- and `TBB`'s truth in the standard model.
  have models_standardProvability_iff : ∀ {σ : ArithmeticSentence},
      ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ ↔ T ⊢ σ := by
    intro σ;
    constructor;
    . intro h; exact T.standardProvability.sound_on h;
    . intro h; exact models_of_provable inferInstance (T.standardProvability.D1 h);
  have models_iterate_standardProvability_bot_iff : ∀ {m : ℕ},
      ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m + 1] ⊥) ↔ T.height ≤ m := by
    intro m;
    rw [Function.iterate_succ_apply', models_standardProvability_iff];
    exact Provability.height_le_iff_boxBot.symm;
  have not_models_standardProvability_bot :
      ¬ ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[0] ⊥) := by simp;
  have models_standardInterpret_TBB_iff : ∀ {m : ℕ},
      ℕ↓[ℒₒᵣ] ⊧ (LetterlessFormula.standardInterpret T (TBB m) : ArithmeticSentence) ↔
      T.height ≠ m := by
    intro m;
    have e : LetterlessFormula.standardInterpret T (TBB m)
        = ((T.standardProvability^[m + 1] ⊥) 🡒 (T.standardProvability^[m] ⊥)) := by
      dsimp only [TBB, LetterlessFormula.standardInterpret, LetterlessFormula.interpret];
      rw [LetterlessFormula.interpret_boxItr, LetterlessFormula.interpret_boxItr];
      rfl;
    rw [e];
    have himp :
        ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability^[m + 1] ⊥) 🡒 (T.standardProvability^[m] ⊥)) ↔
        (ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m + 1] ⊥) → ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[m] ⊥)) := by
      simp;
    rw [himp];
    rcases m with _ | k;
    . simp only [not_models_standardProvability_bot, imp_false,
        models_iterate_standardProvability_bot_iff];
      simp;
    . rw [models_iterate_standardProvability_bot_iff, models_iterate_standardProvability_bot_iff];
      rcases eq_top_or_lt_top T.height with h | h;
      . simp [h, eq_comm];
      . obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp h.ne_top;
        rw [← hj];
        simp only [Nat.cast_le, ne_eq, Nat.cast_inj];
        omega;
  have eq_interpret_TBB : ∀ (f : StandardRealization α T) (m : ℕ),
      Formula.interpret f (TBB m) = LetterlessFormula.standardInterpret T (TBB m) := by
    intro f m;
    rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  have mem_provabilityLogicRelativeTo_TA_TBB_iff : ∀ {m : ℕ},
      (TBB m : Formula α) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ↔ T.height ≠ m := by
    intro m;
    constructor;
    . intro h;
      rw [← models_standardInterpret_TBB_iff, ← eq_interpret_TBB ⟨fun _ => ⊥⟩ m];
      exact Arithmetic.TA.provable_iff.mp (h ⟨fun _ => ⊥⟩);
    . intro h f;
      rw [eq_interpret_TBB f m];
      exact Arithmetic.TA.provable_iff.mpr (models_standardInterpret_TBB_iff.mpr h);
  have mem_trace_iff : ∀ {m : ℕ},
      m ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace ↔ T.height ≠ m := by
    intro m;
    rw [← mem_provabilityLogicRelativeTo_TA_TBB_iff];
    exact ⟨provable_TBB_of_mem_trace, mem_trace_of_provable_TBB⟩;
  constructor;
  . intro hL;
    have htrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = {n}ᶜ := by rw [hL]; simp;
    have hn : n ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace := by rw [htrace]; simp;
    rw [mem_trace_iff] at hn;
    exact not_not.mp hn;
  . intro hn;
    -- Step 1: `∼TBB n` is a theorem of `L`, since `T.height = n` makes `TBB n` false.
    have hnTBB : (∼(TBB n) : Formula α) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
      intro f;
      apply Arithmetic.TA.provable_iff.mpr;
      show ℕ↓[ℒₒᵣ] ⊧ ((Formula.interpret f (TBB n) : ArithmeticSentence) 🡒 ⊥);
      rw [Semantics.Imp.models_imply];
      intro hcontra;
      rw [eq_interpret_TBB f n] at hcontra;
      exact ((models_standardInterpret_TBB_iff.mp hcontra) hn).elim;
    -- Step 2: `L ⊄ S`, otherwise both `TBB n` and `∼TBB n` would be theorems of `S`,
    -- contradicting the consistency of `S`.
    have hnotS : ¬ ((T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ LogicS) := by
      intro hSub;
      have h1 : (∼(TBB n) : Formula α) ∈ LogicS := hSub hnTBB;
      have h2 : (TBB n : Formula α) ∈ LogicS := LogicS.provable_TBB;
      have htaut : (((∼(TBB n)) : Formula α) 🡒 (TBB n) 🡒 ⊥) ∈ LogicGL := by
        apply ProvableHilbert.Kripke.completeness;
        intro κ _ M _ x;
        simp only [Model.World.forces_imp, Model.World.not_forces_imp];
        tauto;
      exact LogicS.consistent
        (Logic.sumQuasiNormal.mdp
          (Logic.sumQuasiNormal.mdp (LogicS.provable_of_provable_GL htaut) h1) h2);
    -- Step 3: by Lemma 49, `L = GLβ⁻ L.trace`, and `L.trace = {n}ᶜ` since `T.height = n`.
    have htrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = {n}ᶜ := by
      ext m;
      rw [mem_trace_iff, hn];
      simp [eq_comm];
    rw [eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hnotS];
    exact LogicGLBetaMinus.congr htrace (cofinite_trace_of_not_subset_LogicS hnotS) (by simp);

/--
  **Corollary 41 in [AB05]** (exhaustiveness): every truth provability logic is one of
  `S`, `D`, `GLαω`, and `GLβ⁻ {n}ᶜ`.
-/
theorem classification_provabilityLogic_TA [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    (ℕ↓[ℒₒᵣ] ⊧* T ∧ L = LogicS) ∨
    (T.SoundOnHierarchy 𝚺 1 ∧ ¬(ℕ↓[ℒₒᵣ] ⊧* T) ∧ L = LogicD) ∨
    (¬(T.SoundOnHierarchy 𝚺 1) ∧ T.height = (⊤ : ℕ∞) ∧ L = LogicA) ∨
    ∃ n : ℕ, T.height = n ∧ L = LogicGLBetaMinus {n}ᶜ (by simp) := by
  by_cases hheight : T.height = (⊤ : ℕ∞);
  . by_cases hSig : T.SoundOnHierarchy 𝚺 1;
    . by_cases hsound : ℕ↓[ℒₒᵣ] ⊧* T;
      . exact Or.inl ⟨hsound, eq_provabilityLogic_TA_LogicS_of_sound⟩;
      . exact Or.inr (Or.inl ⟨hSig, hsound, eq_provabilityLogic_TA_LogicD_iff.mpr ⟨hSig, hsound⟩⟩);
    . exact Or.inr (Or.inr (Or.inl
        ⟨hSig, hheight, eq_provabilityLogic_TA_LogicA_iff.mpr ⟨hSig, hheight⟩⟩));
  . obtain ⟨n, hn⟩ : ∃ n : ℕ, T.height = n := by
      rcases eq_top_or_lt_top T.height with h | h;
      . exact absurd h hheight;
      . obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (LT.lt.ne_top h);
        exact ⟨n, hn.symm⟩;
    exact Or.inr (Or.inr (Or.inr ⟨n, hn, eq_provabilityLogic_TA_LogicGLBetaMinus_iff.mpr hn⟩));

end trueArith

end
