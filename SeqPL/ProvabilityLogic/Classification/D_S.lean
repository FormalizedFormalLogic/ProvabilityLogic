module

public import SeqPL.ProvabilityLogic.Classification.Transfer

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/--
  **Lemma 56 in [AB05]** (Lemma 1 in §5 of [Bek90]): if `D ⊬ A` then there is `B` over
  the atoms of `A` such that `S ⊬ B` and `GLαω{A} ⊢ B ⋎ (□p 🡒 p)` for an atom `p`
  not occurring in `A`. Proved via the Kripke-model analysis of `D` (`q`-simplification
  and almost defining formulas, [Bek90] §4).
-/
lemma exists_lemma56 [DecidableEq α] {A : Formula α} {p : α} (hp : p ∉ A.atoms)
    (hA : A ∉ LogicD) :
    ∃ B : Formula α, B ∉ LogicS ∧ B.atoms ⊆ A.atoms ∧
      (B ⋎ ((□(#p)) 🡒 (#p))) ∈ (LogicA +ᴸ A) := by
  sorry

/--
  **Theorem 1 in §5 of [Bek90]** (cf. Lemma 57 in [AB05]): if the provability logic of
  `T` relative to `U` has trace `ω` and contains some `A ∉ D`, then `U` proves the local
  reflection schema for `T`. The fresh atom is manufactured by passing to `Option α`.
-/
theorem provable_reflection_of_mem_not_LogicD :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ∀ {A : Formula α}, A ∈ L → A ∉ LogicD →
    ∀ σ : FirstOrder.Sentence ℒₒᵣ, U ⊢ (T.standardProvability σ) 🡒 σ := by
  intro hT A hAL hAD σ;
  classical
  -- Pass to `Option α`, where `none` is a fresh atom.
  have hAD' : (A.map some) ∉ LogicD := LogicD.not_provable_map_some hAD;
  have hT' : (T.provabilityLogicRelativeTo U : Logic (Option α)).trace = Set.univ := by
    apply Set.eq_univ_of_forall;
    intro n;
    apply mem_trace_of_provable_TBB (α := Option α);
    have hTBBα : (TBB n : Formula α) ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
      provable_TBB_of_mem_trace (hT ▸ Set.mem_univ n);
    intro g;
    rw [← LetterlessFormula.eq_lift_TBB (α := Option α), LetterlessFormula.interpret_lift];
    have := hTBBα ⟨g.val ∘ some⟩;
    rwa [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift] at this;
  have hAL' : (A.map some) ∈ (T.provabilityLogicRelativeTo U : Logic (Option α)) := by
    intro g;
    rw [Formula.interpret_map];
    exact hAL _;
  -- The Lemma 56 disjunction is a theorem of the provability logic at `Option α`.
  obtain ⟨B, hBS, hBatoms, hBGL⟩ := exists_lemma56 (p := (none : Option α))
    (by simp [Formula.atoms_map]) hAD';
  have hsub : (LogicA +ᴸ (A.map some))
      ⊆ (T.provabilityLogicRelativeTo U : Logic (Option α)) := by
    intro B hB;
    induction hB with
    | mem₁ hB => exact subset_LogicA_of_univ_trace hT' hB;
    | mem₂ hB => obtain rfl := hB; exact hAL';
    | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
    | subst _ ih => intro g; rw [Formula.interpret_subst]; exact ih _;
  have hdisj : (B ⋎ ((□(#(none : Option α))) 🡒 (#(none : Option α))))
      ∈ (T.provabilityLogicRelativeTo U : Logic (Option α)) := hsub hBGL;
  -- The completion of `GL{B}`: the provability logic relative to `U₁ := T + {g(B)}`.
  set U₁ : FirstOrder.ArithmeticTheory :=
    𝗜𝚺₁ ∪ (Set.range (fun g : StandardRealization (Option α) T => Formula.interpret g B))
    with hU₁;
  haveI : 𝗜𝚺₁ ⪯ U₁ := inferInstance;
  have hBI : B ∈ (T.provabilityLogicRelativeTo U₁ : Logic (Option α)) := by
    intro g;
    apply Entailment.by_axm;
    simp only [hU₁, Set.mem_union];
    exact Or.inr ⟨g, rfl⟩;
  have hnotS : ¬((T.provabilityLogicRelativeTo U₁ : Logic (Option α)) ⊆ LogicS) :=
    fun hc => hBS (hc hBI);
  -- Lemma 49: this completion is `GLβ⁻` of a cofinite trace; its axiom is provable.
  have h49 := eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS hnotS;
  set pf := cofinite_trace_of_not_subset_LogicS hnotS with hpf;
  have hs₀I : (LetterlessFormula.lift (TBBMinus _ pf) : Formula (Option α))
      ∈ (T.provabilityLogicRelativeTo U₁ : Logic (Option α)) := by
    have : (LetterlessFormula.lift (TBBMinus _ pf) : Formula (Option α))
        ∈ LogicGLBetaMinus (T.provabilityLogicRelativeTo U₁ : Logic (Option α)).trace pf :=
      Logic.sumQuasiNormal.mem₂ ⟨TBBMinus _ pf, rfl, rfl⟩;
    rwa [← h49] at this;
  set f₀ : StandardRealization (Option α) T := ⟨fun _ => ⊥⟩ with hf₀;
  obtain ⟨⟨s, hs_sub⟩, hs⟩ := LO.FirstOrder.Theory.compact_add_right (hs₀I f₀);
  obtain ⟨G, -, hG_cov⟩ := finite_preimage_choice s Set.univ
    (fun g : StandardRealization (Option α) T => Formula.interpret g B)
    (fun σ' hσ' => by
      obtain ⟨g, hg⟩ := hs_sub hσ';
      exact ⟨g, Set.mem_univ g, hg⟩);
  -- `∼TBBMinus` is a theorem of the trace-`ω` provability logic.
  have hnots₀ : ((∼(LetterlessFormula.lift (TBBMinus _ pf)) : Formula (Option α)))
      ∈ (T.provabilityLogicRelativeTo U : Logic (Option α)) := by
    have hconj : ((⋀(pf.toFinset.image (TBB : ℕ → Formula (Option α)))) : Formula (Option α))
        ∈ (T.provabilityLogicRelativeTo U : Logic (Option α)) := by
      apply provabilityLogic_fconj;
      intro B hB;
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hB;
      exact provable_TBB_of_mem_trace (hT' ▸ Set.mem_univ n);
    have hbr : ((⋀(pf.toFinset.image (TBB : ℕ → Formula (Option α))))
        🡒 (LetterlessFormula.lift (⋀(pf.toFinset.image TBB)) : Formula (Option α)))
        ∈ LogicGL := by
      apply LogicGL.iff_forces_root.mpr;
      intro κ _ M _;
      haveI : Fintype M.World := Fintype.ofFinite _;
      apply Model.World.forces_imp.mpr;
      by_cases hx : M.root.1 ⊩ ⋀(pf.toFinset.image (TBB : ℕ → Formula (Option α)));
      . right;
        apply Model.iff_forces_lift_rank_mem_spectrum.mpr;
        rw [LetterlessFormula.spectrum_fconj];
        apply Set.mem_iInter₂.mpr;
        intro B hB;
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hB;
        rw [LetterlessFormula.spectrum_TBB];
        have : M.root.1 ⊩ (TBB n : Formula (Option α)) :=
          Model.World.forces_fconj.mp hx _ (Finset.mem_image_of_mem _ hn);
        simpa using Model.iff_forces_TBB_neq_rank.mp this;
      . left; exact hx;
    have hdn : ((LetterlessFormula.lift (⋀(pf.toFinset.image TBB)) : Formula (Option α))
        🡒 (∼(LetterlessFormula.lift (TBBMinus _ pf)) : Formula (Option α)))
        ∈ LogicGL := by
      apply ProvableHilbert.Kripke.completeness;
      intro κ _ M _ x;
      simp only [Model.World.forces_imp];
      tauto;
    exact provabilityLogic_mdp (provabilityLogic_of_GL hdn)
      (provabilityLogic_mdp (provabilityLogic_of_GL hbr) hconj);
  -- Combine everything at the arithmetical level.
  have w₂ : U ⊢ s.conj 🡒 Formula.interpret f₀
      (LetterlessFormula.lift (TBBMinus _ pf) : Formula (Option α)) :=
    Entailment.WeakerThan.pbl hs;
  have w₃ : U ⊢ (Formula.interpret f₀
      (LetterlessFormula.lift (TBBMinus _ pf) : Formula (Option α))) 🡒 ⊥ :=
    hnots₀ f₀;
  have w₁ : U ⊢ (∼((T.standardProvability σ) 🡒 σ)) 🡒 s.conj := by
    apply right_Fconj!_intro;
    intro σ' hσ';
    obtain ⟨g, -, rfl⟩ := hG_cov σ' hσ';
    set g' : StandardRealization (Option α) T :=
      ⟨fun x => match x with | none => σ | some a => g.val (some a)⟩ with hg';
    have hfact := hdisj g';
    have e₁ : Formula.interpret g' B = Formula.interpret g B := by
      apply Formula.interpret_congr_atoms;
      intro a ha;
      have := hBatoms ha;
      rw [Formula.atoms_map] at this;
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp this;
      rfl;
    have e₂ : Formula.interpret g' (B ⋎ ((□(#(none : Option α))) 🡒 (#(none : Option α))))
        = ((Formula.interpret g' B 🡒 ⊥) 🡒 ((T.standardProvability σ) 🡒 σ)) := rfl;
    rw [e₂, e₁] at hfact;
    cl_prover [hfact];
  cl_prover [w₁, w₂, w₃];

/--
  If the provability logic of `T` relative to `U` has trace `ω` and strictly contains
  `D`, then it contains `S`. Assertion 1 in [Bek90] (Lemma 56 and 57 in [AB05]).
-/
theorem subset_LogicS_of_ssubset_LogicD_of_univ_trace :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → LogicD ⊂ L → LogicS ⊆ L := by
  intro hT h;
  obtain ⟨A, hAL, hAD⟩ := Set.exists_of_ssubset h;
  intro B hB;
  induction hB with
  | mem₁ hB => exact provabilityLogic_of_GL hB;
  | mem₂ hB =>
    obtain ⟨C, rfl⟩ := hB;
    intro f;
    exact provable_reflection_of_mem_not_LogicD hT hAL hAD (Formula.interpret f C);
  | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
  | subst _ ih => intro f; rw [Formula.interpret_subst]; exact ih _;

/--
  No provability logic lies strictly between `D` and `S`. Corollary 58 in [AB05].
-/
theorem no_logic_between_LogicD_LogicS :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ¬((LogicD ⊂ L) ∧ (L ⊂ LogicS)) := by
  rintro hT ⟨h₁, h₂⟩;
  exact h₂.not_subset (subset_LogicS_of_ssubset_LogicD_of_univ_trace hT h₁);

end
