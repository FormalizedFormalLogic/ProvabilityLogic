module

public import ProvabilityLogic.ProvabilityLogic.Classification.A_D
public import ProvabilityLogic.ProvabilityLogic.Classification.D_S
public import ProvabilityLogic.ProvabilityLogic.S.Basic

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁]

section univ_trace

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/--
  If the provability logic of `T` relative to `U` has trace `ω` and is contained in `S`,
  then it is one of `LogicA`, `D`, and `S`.

- [Bek90, Assertion 3]
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

section without_decidableEq

/-- `LogicGLAlpha` is monotone in the trace set. -/
lemma LogicGLAlpha.mono {Alpha Alpha' : Set ℕ} (h : Alpha ⊆ Alpha') :
    (LogicGLAlpha Alpha : Logic α) ⊆ LogicGLAlpha Alpha' := by
  apply Logic.sumQuasiNormal.iff_subset.mpr;
  rintro A ⟨B, ⟨n, hn, rfl⟩, rfl⟩;
  exact Logic.sumQuasiNormal.mem₂ ⟨TBB n, ⟨n, h hn, rfl⟩, rfl⟩;

end without_decidableEq

section before_decidableEq_var

/-- `LogicS` proves every `TBB n`, as a substitution instance of axiom `T`. -/
lemma LogicS.provable_TBB {n : ℕ} : (TBB n : Formula α) ∈ LogicS := by
  simpa [TBB, Formula.boxItr, Function.iterate_succ_apply'] using
    LogicS.provable_axiomT (A := (□^[n]⊥ : Formula α));

end before_decidableEq_var

section addTBB_before_decidableEq

open LetterlessFormula

/--
  `U` extended by the standard `T`-interpretations of `TBB n` for `n ∈ N`.
-/
noncomputable abbrev _root_.LO.FirstOrder.ArithmeticTheory.addTBB
    (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] (N : Set ℕ) : FirstOrder.ArithmeticTheory :=
  U ∪ (N.image (fun n => LetterlessFormula.standardInterpret T (TBB n)))

section without_T_U_alpha

variable {N : Set ℕ}

/--
  `U` is weaker than its extension by `TBB` interpretations.
-/
lemma _root_.LO.FirstOrder.ArithmeticTheory.addTBB.weakerThan : U ⪯ T.addTBB U N :=
  inferInstance

end without_T_U_alpha

section

variable {N : Set ℕ}

/--
  The provability logic only grows when axioms are added to `U`.
-/
lemma provabilityLogic_subset_addTBB :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    letI L' : Logic α := T.provabilityLogicRelativeTo (T.addTBB U N);
    L ⊆ L' := by
  intro A hA f;
  exact Entailment.WeakerThan.wk FirstOrder.ArithmeticTheory.addTBB.weakerThan (hA f);

end

section only_formula_alpha

variable {N : Set ℕ}

/--
  The added `TBB` axioms are theorems of the extended provability logic.
-/
lemma provable_TBB_addTBB_of_mem {n : ℕ} (hn : n ∈ N) :
    (TBB n : Formula α) ∈ (T.provabilityLogicRelativeTo (T.addTBB U N) : Logic α) := by
  intro f;
  rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  apply Entailment.by_axm;
  simp only [Set.mem_union];
  exact Or.inr ⟨n, hn, rfl⟩;

end only_formula_alpha

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]
variable {N : Set ℕ}

/--
  Deduction: if `A` is in the provability logic relative to `U` extended with `TBB n` axioms for `n ∈ N` (where `N` is finite), then `⋀TBB(N) 🡒 A` is in the provability logic relative to `U`.
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

end

end addTBB_before_decidableEq

section modal

variable [DecidableEq α]

/-- `LogicGLAlpha Beta ⊆ LogicGLBetaMinus Beta` for cofinite `Beta` (both have trace `Beta`, and `LogicGLBetaMinus` is the largest). -/
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
  `LogicGLAlpha Beta = LogicA ∩ LogicGLBetaMinus Beta` for cofinite `Beta`: the `η`/`ξ` correspondence
  evaluated at `LogicGLAlpha Beta`, proved via the finite compactness
  `GL_sumQuasiNormal_finite_provable` (note `Betaᶜ` is finite).

- [AB05, η/ξ correspondence]
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

end modal

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]
variable (hCf : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite)

/--
  Adjoining the missing `TBB` axioms yields a provability logic of universal trace.
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

variable [DecidableEq α]

include hCf in
/--
  If `L ⊆ S`, the extension by the missing `TBB` axioms is still contained in `S`
  (otherwise it would be inconsistent, contradicting the consistency of `S`).
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
  `L = L'' ∩ LogicGLBetaMinus (L.trace)` where `L''` is the extension of `L` by the missing `TBB` axioms.

- [AB05, η ∘ ξ = id correspondence]
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

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] [DecidableEq α]

/--
  If the provability logic of `T` relative to `U` has cofinite trace `Beta` and is contained in `S`,
  then it is one of `LogicGLAlpha Beta`, `D ∩ LogicGLBetaMinus Beta`, and `S ∩ LogicGLBetaMinus Beta`.
  Obtained from the universal-trace classification by adjoining the missing `TBB` axioms and intersecting back.
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


section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

open Classical in
/--
  **The classification theorem of provability logics.**
  Let `L` be the provability logic of `T` relative to `U`.
  - If `L.trace` is coinfinite, then `L = LogicGLAlpha (L.trace)`.
  - Otherwise `L.trace` is cofinite (by `Formula.trace_finite_or_cofinite`), and:
    - if `L ⊄ S`, then `L = LogicGLBetaMinus (L.trace)`;
    - if `L ⊆ S`, then `L` is one of `LogicGLAlpha (L.trace)`, `D ∩ LogicGLBetaMinus (L.trace)`,
      and `S ∩ LogicGLBetaMinus (L.trace)`.

- [Bek90, Assertion 6]
- [AB05, Theorem 40]
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

end


/-!
# Classification of truth provability logics

The truth provability logics, i.e. the logics of the form `PL_T(𝗧𝗔)`, are precisely
`S`, `D`, `LogicA`, and `LogicGLBetaMinus {n}ᶜ`, according to the soundness properties of `T`:

- `PL_T(𝗧𝗔) = S` iff `T` is sound;
- `PL_T(𝗧𝗔) = D` iff `T` is `Σ₁`-sound but not sound;
- `PL_T(𝗧𝗔) = LogicA` iff `T` is not `Σ₁`-sound but of infinite characteristic;
- `PL_T(𝗧𝗔) = LogicGLBetaMinus {n}ᶜ` iff `T` has characteristic `n` (i.e. `T.height = n`).

References:
- [AB05, Corollary 41]
-/

section trueArith

section heightTrace

section without_alpha

/--
  The standard provability predicate of `T` holds in the standard model iff `T` proves it.
-/
lemma models_standardProvability_iff {σ : ArithmeticSentence} :
    ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ ↔ T ⊢ σ := by
  constructor;
  . intro h;
    exact T.standardProvability.sound_on h;
  . intro h;
    exact models_of_provable inferInstance (T.standardProvability.D1 h);

/--
  Falsum itself never holds in the standard model.
-/
lemma not_models_standardProvability_bot :
    ¬ ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[0] ⊥) := by
  simp;

end without_alpha

section

variable [𝗜𝚺₁ ⪯ T]

/--
  The `(n + 1)`-th iterated standard provability of falsum holds in the standard model iff `T`'s height is at most `n`.
-/
lemma models_iterate_standardProvability_bot_iff {n : ℕ} :
    ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[n + 1] ⊥) ↔ T.height ≤ n := by
  rw [Function.iterate_succ_apply', models_standardProvability_iff];
  exact Provability.height_le_iff_boxBot.symm;

/--
  The standard interpretation of `TBB n` holds in the standard model iff `T`'s height is not `n`.
-/
lemma models_standardInterpret_TBB_iff {n : ℕ} :
    ℕ↓[ℒₒᵣ] ⊧ (LetterlessFormula.standardInterpret T (TBB n) : ArithmeticSentence) ↔ T.height ≠ n := by
  have e : LetterlessFormula.standardInterpret T (TBB n)
      = ((T.standardProvability^[n + 1] ⊥) 🡒 (T.standardProvability^[n] ⊥)) := by
    dsimp only [TBB, LetterlessFormula.standardInterpret, LetterlessFormula.interpret];
    rw [LetterlessFormula.interpret_boxItr, LetterlessFormula.interpret_boxItr];
    rfl;
  rw [e];
  have himp :
      ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability^[n + 1] ⊥) 🡒 (T.standardProvability^[n] ⊥)) ↔
      (ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[n + 1] ⊥) → ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[n] ⊥)) := by
    simp;
  rw [himp];
  rcases n with _ | m;
  . simp only [not_models_standardProvability_bot, imp_false, models_iterate_standardProvability_bot_iff];
    simp;
  . rw [models_iterate_standardProvability_bot_iff, models_iterate_standardProvability_bot_iff];
    rcases eq_top_or_lt_top T.height with h | h;
    . simp [h, eq_comm];
    . obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne_top;
      rw [← hk];
      simp only [Nat.cast_le, ne_eq, Nat.cast_inj];
      omega;

/--
  `TBB n` is a theorem of the truth provability logic of `T` iff `T`'s height is not `n`.
-/
lemma mem_provabilityLogicRelativeTo_TA_TBB_iff {n : ℕ} :
    (TBB n : Formula α) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ↔ T.height ≠ n := by
  have e : ∀ f : StandardRealization α T,
      Formula.interpret f (TBB n) = LetterlessFormula.standardInterpret T (TBB n) := by
    intro f;
    rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  constructor;
  . intro h;
    rw [← models_standardInterpret_TBB_iff, ← e ⟨fun _ => ⊥⟩];
    exact Arithmetic.TA.provable_iff.mp (h ⟨fun _ => ⊥⟩);
  . intro h f;
    rw [e f];
    exact Arithmetic.TA.provable_iff.mpr (models_standardInterpret_TBB_iff.mpr h);

/--
  `n` is in the trace of the truth provability logic of `T` iff `T`'s height is not `n`.
-/
lemma mem_trace_provabilityLogicRelativeTo_TA_iff {n : ℕ} :
    n ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace ↔ T.height ≠ n := by
  rw [← mem_provabilityLogicRelativeTo_TA_TBB_iff];
  exact ⟨provable_TBB_of_mem_trace, mem_trace_of_provable_TBB⟩;

/--
  The trace of the truth provability logic of `T` is all of `ℕ` iff `T` has infinite height.
-/
lemma trace_provabilityLogicRelativeTo_TA_eq_univ_iff [DecidableEq α] [Nonempty α] :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ ↔ T.height = (⊤ : ℕ∞) := by
  rw [Set.eq_univ_iff_forall];
  constructor;
  . intro h;
    by_contra hh;
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hh;
    exact (mem_trace_provabilityLogicRelativeTo_TA_iff.mp (h n)) hn.symm;
  . intro h n;
    rw [mem_trace_provabilityLogicRelativeTo_TA_iff, h];
    exact (ENat.coe_lt_top n).ne';

/--
  The trace of the truth provability logic of `T` is the complement of `{n}` iff `T` has height `n`.
-/
lemma trace_provabilityLogicRelativeTo_TA_eq_compl_singleton_iff [DecidableEq α] [Nonempty α]
  {n : ℕ}
  : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = {n}ᶜ ↔ T.height = n := by
  constructor;
  . intro h;
    have hn : n ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace := by rw [h]; simp;
    rw [mem_trace_provabilityLogicRelativeTo_TA_iff] at hn;
    exact not_not.mp hn;
  . intro h;
    ext m;
    rw [mem_trace_provabilityLogicRelativeTo_TA_iff (n := m), h];
    simp [eq_comm];

end

/--
  If `T` is `Σ₁`-sound, then the `Σ₁`-reflection instance for `T` is true in the standard model for any `Σ₁` sentence `σ`.
-/
lemma models_standardProvability_imp_of_soundOnHierarchy [T.SoundOnHierarchy 𝚺 1]
    {σ : ArithmeticSentence} (hσ : LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 σ) :
    ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability σ) 🡒 σ) := by
  rw [Semantics.Imp.models_imply];
  intro h;
  exact ArithmeticTheory.soundOnHierarchy T 𝚺 1 (models_standardProvability_iff.mp h) hσ;

/--
  Converse of `models_standardProvability_imp_of_soundOnHierarchy`: if every `Σ₁`-reflection instance for `T` is true in the standard model, then `T` is `Σ₁`-sound.
-/
lemma soundOnHierarchy_of_models_standardProvability_imp
    (h : ∀ {σ : ArithmeticSentence}, LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 σ →
      ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability σ) 🡒 σ)) :
    T.SoundOnHierarchy 𝚺 1 := by
  constructor;
  intro σ hTσ hσ;
  exact (Semantics.Imp.models_imply.mp (h hσ)) (models_standardProvability_iff.mpr hTσ);

section

variable [𝗜𝚺₁ ⪯ T]

/--
  If `T` is `Σ₁`-sound, then `D` is contained in the truth provability logic of `T`.
  Mimics the case split on the generators of `D` (`GL`-fragment, axiom `P`, axiom `D`, `mdp`)
  used for `subset_LogicD_of_ssubset_LogicA_of_univ_trace`, but derives truth in the standard model
  directly in each case rather than provability in an extended theory.

- [AB05, Corollary 41(ii)]
-/
lemma LogicD_subset_provabilityLogicRelativeTo_TA [T.SoundOnHierarchy 𝚺 1] :
    (LogicD : Logic α) ⊆ T.provabilityLogicRelativeTo 𝗧𝗔 := by
  intro A hA;
  induction hA using LogicD.substlessInduction with
  | provable_GL h => exact provabilityLogic_of_GL h;
  | axiomP =>
    intro f;
    apply Arithmetic.TA.provable_iff.mpr;
    have e : Formula.interpret f (∼□⊥ : Formula α)
        = (T.standardProvability (⊥ : ArithmeticSentence)) 🡒 ⊥ := by
      simp [Formula.interpret];
    rw [e, Semantics.Imp.models_imply];
    intro h;
    exact absurd (models_standardProvability_iff.mp h)
      (inferInstance : Entailment.Consistent T).not_bot;
  | @axiomD B C =>
    intro f;
    apply Arithmetic.TA.provable_iff.mpr;
    have hσ : LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 (f (((□B) ⋎ (□C) : Formula α))) := by
      simp [Formula.interpret, Arithmetic.standardProvability_def];
    have hrfl := models_standardProvability_imp_of_soundOnHierarchy (T := T) hσ;
    simpa [Formula.interpret] using hrfl;
  | mdp ihAB ihA => exact provabilityLogic_mdp ihAB ihA;

end

/--
  `⊥` is never a theorem of the truth provability logic of `T`.
-/
lemma bot_notMem_provabilityLogicRelativeTo_TA :
    (⊥ : Formula α) ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
  intro h;
  exact not_models_standardProvability_bot (T := T)
    (Arithmetic.TA.provable_iff.mp (h (⟨fun _ => ⊥⟩ : StandardRealization α T)));

section

variable [𝗜𝚺₁ ⪯ T] [DecidableEq α]

/--
  If the trace of the truth provability logic of `T` is universal (i.e. all of `ℕ`), then the truth provability logic of `T` is contained in `S`.
  A truth provability logic outside `S` has a cofinite trace, which when combined with the trace being universal would force `⊥ ∈ L`, contradicting soundness of `𝗧𝗔`.
-/
lemma provabilityLogicRelativeTo_TA_subset_LogicS_of_trace_eq_univ
    (h : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ) :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ LogicS := by
  by_contra hS;
  have hCf : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).traceᶜ.Finite :=
    cofinite_trace_of_not_subset_LogicS hS;
  have hCf' : (Set.univ : Set ℕ)ᶜ.Finite := by simp;
  have heq : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = LogicGLBetaMinus Set.univ hCf' := by
    rw [eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hS];
    exact LogicGLBetaMinus.congr h hCf hCf';
  exact bot_notMem_provabilityLogicRelativeTo_TA (heq ▸ LogicGLBetaMinus.bot_mem_of_eq_univ);

end

section

variable [𝗜𝚺₁ ⪯ T]

/--
  If the truth provability logic of `T` is `D`, then `T` is `Σ₁`-sound.
  Uses `provable_sigma1_reflection_of_mem_not_LogicA` applied to axiom `D` itself, which lies in `D` but not in `LogicA`.

- [AB05, Corollary 41(ii)]
-/
lemma soundOnHierarchy_of_eq_provabilityLogicRelativeTo_TA_LogicD [DecidableEq α] [Nonempty α]
    (h : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) = LogicD) :
    T.SoundOnHierarchy 𝚺 1 := by
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

end heightTrace

variable [𝗜𝚺₁ ⪯ T]

/--
  The truth provability logic of a sound theory is `S`.

- [AB05, Corollary 41(i)]
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
  For a type of atoms with at least one element, the truth provability logic of `T` is `S` iff `T` is sound.
  (Some atom is needed for the forward direction: over `Empty` every theory of infinite characteristic
  has truth provability logic `S`, since all letterless logics between `LogicA` and `S` coincide.)

- [AB05, Corollary 41(i)]
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
  The truth provability logic of `T` is `D` iff `T` is `Σ₁`-sound but not sound.

- [AB05, Corollary 41(ii)]
-/
theorem eq_provabilityLogic_TA_LogicD_iff [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicD ↔ (T.SoundOnHierarchy 𝚺 1 ∧ ¬(ℕ↓[ℒₒᵣ] ⊧* T)) := by
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
    have hDL := LogicD_subset_provabilityLogicRelativeTo_TA (T := T) (α := α);
    have hheight : T.height = (⊤ : ℕ∞) := Arithmetic.height_eq_top_of_sigma1_sound T;
    have hUniv := trace_provabilityLogicRelativeTo_TA_eq_univ_iff (α := α).mpr hheight;
    have hLS := provabilityLogicRelativeTo_TA_subset_LogicS_of_trace_eq_univ hUniv;
    rcases classification_LogicS_sublogics_of_univ_trace (T := T) (U := 𝗧𝗔) hUniv hLS
      with h | h | h;
    . obtain ⟨a⟩ := ‹Nonempty α›;
      exact absurd (h ▸ hDL) (not_LogicD_subset_LogicA (a := a));
    . exact h;
    . exact absurd (eq_provabilityLogic_TA_LogicS_iff.mp h) hsound;

/--
  The truth provability logic of `T` is `LogicA` iff `T` is not `Σ₁`-sound but of infinite characteristic.

- [AB05, Corollary 41(iii)]
-/
theorem eq_provabilityLogic_TA_LogicA_iff [DecidableEq α] [Nonempty α] :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicA ↔ (¬(T.SoundOnHierarchy 𝚺 1) ∧ T.height = (⊤ : ℕ∞)) := by
  constructor;
  . intro h;
    have hTrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ := by
      rw [h]; exact LogicGLAlpha.eq_trace;
    constructor;
    . intro hSig;
      haveI := hSig;
      exact not_LogicD_subset_LogicA (α := α) (a := Classical.arbitrary α)
        (h ▸ LogicD_subset_provabilityLogicRelativeTo_TA);
    . exact trace_provabilityLogicRelativeTo_TA_eq_univ_iff.mp hTrace;
  . rintro ⟨hSig, hHeight⟩;
    have hTrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ :=
      trace_provabilityLogicRelativeTo_TA_eq_univ_iff.mpr hHeight;
    have hLS : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ⊆ LogicS :=
      provabilityLogicRelativeTo_TA_subset_LogicS_of_trace_eq_univ hTrace;
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
  The truth provability logic of `T` is `LogicGLBetaMinus {n}ᶜ` iff `T` has characteristic `n`, i.e. `T.height = n`.

- [AB05, Corollary 41(iv)]
-/
theorem eq_provabilityLogic_TA_LogicGLBetaMinus_iff [DecidableEq α] {n : ℕ} :
    letI L : Logic α := T.provabilityLogicRelativeTo 𝗧𝗔;
    L = LogicGLBetaMinus {n}ᶜ (by simp) ↔ T.height = n := by
  constructor;
  . intro hL;
    have htrace : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = {n}ᶜ := by rw [hL]; simp;
    have hn : n ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace := by rw [htrace]; simp;
    rw [mem_trace_provabilityLogicRelativeTo_TA_iff] at hn;
    exact not_not.mp hn;
  . intro hn;
    -- Step 1: `∼TBB n` is a theorem of `L`, since `T.height = n` makes `TBB n` false.
    have hnTBB : (∼(TBB n) : Formula α) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) := by
      intro f;
      apply Arithmetic.TA.provable_iff.mpr;
      show ℕ↓[ℒₒᵣ] ⊧ ((Formula.interpret f (TBB n) : ArithmeticSentence) 🡒 ⊥);
      rw [Semantics.Imp.models_imply];
      intro hcontra;
      have e : Formula.interpret f (TBB n) = LetterlessFormula.standardInterpret T (TBB n) := by
        rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
      rw [e] at hcontra;
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
      rw [mem_trace_provabilityLogicRelativeTo_TA_iff, hn];
      simp [eq_comm];
    rw [eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hnotS];
    exact LogicGLBetaMinus.congr htrace (cofinite_trace_of_not_subset_LogicS hnotS) (by simp);

/--
  Every truth provability logic is one of `S`, `D`, `LogicA`, and `LogicGLBetaMinus {n}ᶜ` for some `n`.

- [AB05, Corollary 41]
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
