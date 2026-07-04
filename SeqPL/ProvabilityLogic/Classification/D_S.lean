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
  The `p ↔ q` substitution used in the proof of Lemma 1, [Bek90] §5, p.266: for a
  finite set of atoms `S`, replace every `q ∈ S` by `#p 🡘 #q`, leaving other atoms
  (in particular `p` itself) untouched.
-/
noncomputable def Formula.Substitution.pIffOn (p : α) (S : Finset α) : Formula.Substitution α :=
  fun q => if q ∈ S then (#p 🡘 #q) else #q

@[simp]
lemma Formula.atoms_pIffOn (p a : α) (S : Finset α) :
    (Formula.Substitution.pIffOn p S a).atoms ⊆ insert p {a} := by
  unfold Formula.Substitution.pIffOn;
  split;
  . intro x hx;
    simp only [Formula.atoms, Finset.mem_union] at hx;
    simp only [Finset.mem_insert, Finset.mem_singleton];
    grind;
  . simp [Formula.atoms];

/--
  The conjunction `Δ` of Lemma 1, [Bek90] §5, p.266: over all `2^n` subsets `S` of
  `A`'s atoms, the substitution instance of `A` obtained by replacing every atom in
  `S` with `p ↔ (that atom)`.
-/
noncomputable def Formula.deltaPIff [DecidableEq α] (A : Formula α) (p : α) : Formula α :=
  ⋀(A.atoms.powerset.image (fun S => A⟦Formula.Substitution.pIffOn p S⟧))

/--
  **Lemma 1.1 in [Bek90] §5, p.266**: transfer of forcing along a bisimulation-under-`P`
  `Bi` (our surrogate for the paper's "`q̄`-isomorphism", see `Model.BisimulationUnder`)
  combined with the `p ↔ q` substitution. If `Bi` "reflects the root" (a `Bi`-related
  pair has its `N`-component equal to `N`'s root iff its `M`-component equals `M`'s
  root -- automatic for an actual isomorphism of rooted trees) and `N`'s root forces
  `□p` but not `p` itself (`p` a fresh atom, not in `P`), then for any `Bi`-related pair
  `(x, x')` and any formula `θ` depending on `P`, forcing of `θ` at `x` agrees with
  forcing, at `x'`, of `θ` with every atom in `γ` replaced by `p ↔ (that atom)` --
  where `γ` records exactly the atoms on which the two roots' valuations disagree.

  The mechanism: away from the roots, `N`'s root forces `□p`, so `x' ⊩ p` holds
  outright (`x' ≠ N.root.1`), making the substituted atom `p ↔ q` forcing-equivalent
  to plain `q`, so the bisimulation's atomic clause suffices directly. At the roots
  themselves `x' ⊩ p` is not `True` in general (`N`'s root additionally satisfies `¬p`
  by hypothesis), so the compensating substitution is exactly needed there, and `γ` is
  defined precisely to make it work out.
-/
theorem BisimulationUnder.forces_iff_subst_pIffOn {κ₁ κ₂ : Type u} [Nonempty κ₁] [Nonempty κ₂]
    {M : RootedModel κ₁ α} {N : RootedModel κ₂ α} {P : Finset α} {p : α}
    (Bi : Model.BisimulationUnder P M.toModel N.toModel)
    (hroot_reflect : ∀ {x : M.World} {x' : N.World}, Bi x x' → (x' = N.root.1 ↔ x = M.root.1))
    (hp_box : N.root.1 ⊩ (□(#p))) (hp_root : N.root.1 ⊮ (#p)) {γ : Finset α}
    (hγ_root : ∀ q ∈ P, (q ∈ γ ↔ ¬ (M.Val M.root.1 q ↔ N.Val N.root.1 q))) :
    ∀ {x : M.World} {x' : N.World}, Bi x x' →
      ∀ {θ : Formula α}, θ.atoms ⊆ P → (x ⊩ θ ↔ x' ⊩ θ⟦Formula.Substitution.pIffOn p γ⟧) := by
  intro x x' hxx' θ;
  induction θ generalizing x x' with
  | atom q =>
    intro hq;
    replace hq : q ∈ P := hq (Finset.mem_singleton_self q);
    show (M.Val x q ↔ x' ⊩ (Formula.Substitution.pIffOn p γ q));
    simp only [Formula.Substitution.pIffOn];
    split;
    case isTrue hqγ =>
      rw [forces_iff];
      by_cases hxroot : x' = N.root.1;
      . obtain rfl : x = M.root.1 := (hroot_reflect hxx').mp hxroot;
        subst hxroot;
        have hγq := (hγ_root q hq).mp hqγ;
        show (M.Val M.root.1 q ↔ (N.Val N.root.1 p ↔ N.Val N.root.1 q));
        have hnp : ¬ N.Val N.root.1 p := hp_root;
        tauto;
      . have hx'p : N.Val x' p := hp_box x' (N.root.2 x' hxroot);
        show (M.Val x q ↔ (N.Val x' p ↔ N.Val x' q));
        have := Bi.atomic hq hxx';
        tauto;
    case isFalse hqγ =>
      exact Bi.atomic hq hxx';
  | bot => intro _; exact Iff.rfl;
  | imp A B ihA ihB =>
    intro hAB;
    simp only [Formula.atoms, Finset.union_subset_iff] at hAB;
    replace ihA := ihA hxx' hAB.1;
    replace ihB := ihB hxx' hAB.2;
    rw [Formula.subst_imp];
    constructor;
    . intro h hA; exact ihB.mp (h (ihA.mpr hA));
    . intro h hA; exact ihB.mpr (h (ihA.mp hA));
  | box A ihA =>
    intro hA;
    replace hA : A.atoms ⊆ P := by simpa [Formula.atoms] using hA;
    simp only [Formula.subst_box, forces_box];
    constructor;
    . intro h y' Rx'y';
      obtain ⟨y, hyy', Rxy⟩ := Bi.back hxx' Rx'y';
      exact (ihA hyy' hA).mp (h y Rxy);
    . intro h y Rxy;
      obtain ⟨y', hyy', Rx'y'⟩ := Bi.forth hxx' Rxy;
      exact (ihA hyy' hA).mpr (h y' Rx'y');

section

open scoped FormulaFinset

private lemma provable_lconj_LogicA_add [DecidableEq α] {A₀ : Formula α} {Γ : FormulaList α}
    (h : ∀ B ∈ Γ, B ∈ (LogicA +ᴸ A₀)) : (⋀Γ) ∈ (LogicA +ᴸ A₀) := by
  match Γ with
  | [] => exact Logic.sumQuasiNormal.mem₁ (Logic.sumQuasiNormal.mem₁ ProvableHilbert.top);
  | [B] => exact h B (by simp);
  | B :: C :: Γ =>
    exact Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mdp
        (Logic.sumQuasiNormal.mem₁ (Logic.sumQuasiNormal.mem₁ ProvableHilbert.andIntro))
        (h B (by simp)))
      (provable_lconj_LogicA_add (Γ := C :: Γ) (by grind));

private lemma provable_fconj_LogicA_add [DecidableEq α] {A₀ : Formula α} {Γ : FormulaFinset α}
    (h : ∀ B ∈ Γ, B ∈ (LogicA +ᴸ A₀)) : (⋀Γ) ∈ (LogicA +ᴸ A₀) :=
  provable_lconj_LogicA_add (by simpa using h)

/-- Every substitution instance of `A` -- in particular every conjunct of `A.deltaPIff p`
-- lies in the quasi-normal extension `LogicA +ᴸ A`, since `A` itself does (`mem₂`) and
quasi-normal extensions are closed under substitution. -/
lemma provable_deltaPIff [DecidableEq α] {A : Formula α} {p : α} :
    A.deltaPIff p ∈ (LogicA +ᴸ A) := by
  apply provable_fconj_LogicA_add;
  intro B hB;
  obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hB;
  exact Logic.sumQuasiNormal.subst (Logic.sumQuasiNormal.mem₂ rfl);

end

/--
  **The semantic core of Lemma 1, [Bek90] §5, p.266** (combining Lemmas 3, 4, 7, 8, 9
  of §4): if `D ⊬ A`, there is a formula `B` over the atoms of `A`, not provable in
  `S`, such that `GLαω ⊢ A.deltaPIff p → B ⋎ (□p → p)`.

  **Not proved in this session.** Two of the five sub-dependencies originally listed
  here are now available as standalone, sorry-free lemmas (`Lemma 1.1` -- see
  `BisimulationUnder.forces_iff_subst_pIffOn` above -- and, modulo one remaining
  bookkeeping sorry, most of `Lemma 8` -- see `RootedModel.exists_simplificationUnder_omega`
  in `SeqPL/Kripke/Simplification.lean`). What remains genuinely open:
  - **Lemma 3 of §4** (cited there from [14]): existence of a `D`-model countermodel to
    `A`. SeqPL's actual `LogicD` semantics (`Model.toPseudoTail`, see
    `SeqPL/Kripke/PseudoTail.lean` and `LogicD.provability_TFAE` in
    `SeqPL/Logic/D/Basic.lean`) does **not** literally match [Bek90]'s "D-model" Kripke
    class (a chain glued *at* the root, forced to see the *entire* base model
    unconditionally) -- discovered in a previous session by comparing `toPseudoTail`'s
    relation clauses against `RootedModel.graftChainOmega`'s. They are provably
    equivalent for theorem-hood purposes (both characterize `LogicD` sensibly) but are
    not isomorphic as frames, so results about one do not transfer to the other for
    free. Bridging this (either by building [Bek90]'s literal "D-model"/"tail model"
    Kripke classes from scratch, or by proving a direct forcing-preserving
    correspondence between `toPseudoTail`-shaped and `graftChainOmega`-shaped models)
    is itself a substantial, multi-day undertaking that was not attempted.
  - **Lemma 8 of §4**: `exists_simplificationUnder_omega` is still `sorry`, but *only*
    for a single, precisely-identified bookkeeping gap (an order-isomorphism between
    `removeCone`-of-an-embedded-point and `graftChainOmega`-of-a-smaller-base-model,
    see that lemma's docstring); the structural obstructions (`graftChainOmega.isTree`
    failing without the "covers the root" hypothesis, chain/embed points never being
    redundant) are fully resolved.
  - **Lemma 7 of §4** (existence of defining formulas): stated as
    `RootedModel.exists_isDefiningFormula` in `SeqPL/Kripke/DefiningFormula.lean`, left
    `sorry` **by explicit user instruction** (not proved inline in [Bek90] itself
    either, and cited there from Artemov 1986 / Boolos 1980's simple-model theory,
    which does not have a directly transcribable construction).
  - **Lemma 9 of §4** (the "almost defining" formula `Φ₀`, p.264-266): not formalized;
    would build on Lemma 7 plus the depth-bound (`□^[N+1]⊥`-style) machinery of
    `SeqPL/Kripke/Rank.lean`. Blocked on Lemma 7.

  Even with Lemma 3's bridge and Lemma 8's last gap closed, this theorem would still be
  blocked on Lemma 7/9 (excluded from this session's scope by the user). See
  `.direct/exists-lemma56.md` for the detailed session notes on scope.
-/
theorem exists_not_mem_LogicS_provable_LogicA_deltaPIff_imp_of_not_mem_LogicD [DecidableEq α]
    {A : Formula α} {p : α} (hp : p ∉ A.atoms) (hA : A ∉ LogicD) :
    ∃ B : Formula α, B.atoms ⊆ A.atoms ∧ B ∉ LogicS ∧
      (A.deltaPIff p 🡒 (B ⋎ ((□(#p)) 🡒 (#p)))) ∈ LogicA := by
  sorry

/--
  **Lemma 56 in [AB05]** (Lemma 1 in §5 of [Bek90]): if `D ⊬ A` then there is `B` over
  the atoms of `A` such that `S ⊬ B` and `GLαω{A} ⊢ B ⋎ (□p 🡒 p)` for an atom `p`
  not occurring in `A`. The semantic content (Kripke-model analysis of `D` via
  `q`-simplification and almost defining formulas, [Bek90] §4) is isolated in
  `exists_not_mem_LogicS_provable_LogicA_deltaPIff_imp_of_not_mem_LogicD` above; this
  lemma is the elementary propositional assembly on top of it: `A.deltaPIff p` is a
  finite conjunction of substitution instances of `A`, hence provable in `LogicA +ᴸ A`
  by the substitution rule, so modus ponens with the semantic core's implication gives
  the result directly.
-/
theorem exists_not_mem_LogicS_disj_boxImp_mem_LogicA_add_of_not_mem_LogicD [DecidableEq α]
    {A : Formula α} {p : α} (hp : p ∉ A.atoms) (hA : A ∉ LogicD) :
    ∃ B : Formula α, B ∉ LogicS ∧ B.atoms ⊆ A.atoms ∧
      (B ⋎ ((□(#p)) 🡒 (#p))) ∈ (LogicA +ᴸ A) := by
  obtain ⟨B, hBatoms, hBS, hImp⟩ :=
    exists_not_mem_LogicS_provable_LogicA_deltaPIff_imp_of_not_mem_LogicD hp hA;
  exact ⟨B, hBS, hBatoms,
    Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ hImp) provable_deltaPIff⟩;

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
  -- The Lemma 1 (§5) disjunction is a theorem of the provability logic at `Option α`.
  obtain ⟨B, hBS, hBatoms, hBGL⟩ :=
    exists_not_mem_LogicS_disj_boxImp_mem_LogicA_add_of_not_mem_LogicD (p := (none : Option α))
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
