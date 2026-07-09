module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.GL.Basic
public import SeqPL.Logic.S.Basic
public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.Rank
public import SeqPL.Kripke.GraftOmega
public import SeqPL.ProvabilityLogic.Classification.Letterless
public import SeqPL.ProvabilityLogic.Classification.Full

@[expose]
public section

universe u
variable {α : Type u}

namespace LogicA

section

/-- Intrinsic definition of `LogicA` avoiding `subst` (for `LogicA.substlessInductionTBB`). -/
protected inductive substlessTBB : Logic α
  | GL {A} : A ∈ LogicGL → LogicA.substlessTBB A
  | TBB (n : ℕ) : LogicA.substlessTBB (TBB n)
  | mdp {A B} : LogicA.substlessTBB (A 🡒 B) → LogicA.substlessTBB A → LogicA.substlessTBB B

variable {A : Formula α}

@[grind →]
lemma provable_of_provable_GL (h : A ∈ LogicGL) : A ∈ LogicA := Logic.sumQuasiNormal.mem₁ h

/-- Every instance `TBB n` of the axiom scheme is a theorem of `LogicA`. -/
lemma provable_axiomTBB (n : ℕ) : (TBB n : Formula α) ∈ LogicA :=
  Logic.sumQuasiNormal.mem₂ ⟨TBB n, ⟨n, by simp, rfl⟩, by simp⟩

private lemma substlessTBB.eq_LogicA : LogicA.substlessTBB (α := α) = LogicA := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | GL h => exact provable_of_provable_GL h;
    | TBB n => exact provable_axiomTBB n;
    | mdp _ _ ihAB ihA => exact Logic.sumQuasiNormal.mdp ihAB ihA;
  . intro h;
    induction h with
    | mem₁ h => exact LogicA.substlessTBB.GL h;
    | mem₂ h =>
      obtain ⟨B, ⟨n, -, rfl⟩, hB⟩ := h;
      obtain rfl : _root_.TBB n = _ := by simpa using hB;
      exact LogicA.substlessTBB.TBB n;
    | mdp _ _ ihAB ihA => exact LogicA.substlessTBB.mdp ihAB ihA;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | GL h => exact LogicA.substlessTBB.GL (ProvableHilbert.subst h);
      | TBB n =>
        simp only [_root_.TBB, Formula.subst_imp, Formula.subst_boxItr, Formula.subst_bot];
        exact LogicA.substlessTBB.TBB n;
      | mdp _ _ ihAB ihA => exact LogicA.substlessTBB.mdp ihAB ihA;

private lemma substlessTBB.toLogicA (h : LogicA.substlessTBB A) : A ∈ LogicA :=
  LogicA.substlessTBB.eq_LogicA ▸ h

private lemma substlessTBB.ofLogicA (h : A ∈ LogicA) : LogicA.substlessTBB A :=
  LogicA.substlessTBB.eq_LogicA.symm ▸ h

/-- Induction principle for `LogicA` avoiding `subst` (GL part, axiom `TBB n`, mdp). -/
protected lemma substlessInductionTBB
  {motive : (A : Formula α) → A ∈ LogicA → Prop}
  (GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (TBB : ∀ (n : ℕ), motive (TBB n) (provable_axiomTBB n))
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicA} → {hA : A ∈ LogicA} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : A ∈ LogicA) → motive A h := by
  intro A h;
  induction LogicA.substlessTBB.ofLogicA h with
  | GL hg => exact GL hg;
  | TBB n => exact TBB n;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := LogicA.substlessTBB.toLogicA hAB) (hA := LogicA.substlessTBB.toLogicA hA)
      (ihAB _) (ihA _);

end


variable [DecidableEq α] {A B : Formula α} {n : ℕ}

/-- `LogicA` proves the iterated consistency statement `∼□^[n]⊥` for every `n`. -/
lemma provable_neg_boxItr_bot : ∼□^[n]⊥ ∈ @LogicA α := by
  -- Chain the axioms `TBB 0, …, TBB (n - 1)`.
  induction n with
  | zero =>
    apply provable_of_provable_GL;
    apply ProvableHilbert.Kripke.completeness;
    intro κ _ M _ x;
    simp only [Formula.boxItr, Model.World.forces_neg];
    exact fun h => h;
  | succ n ih =>
    have hTBB : (TBB n : Formula α) ∈ LogicA := provable_axiomTBB n;
    have hK : (TBB n 🡒 ∼□^[n]⊥ 🡒 ∼□^[n + 1]⊥ : Formula α) ∈ LogicGL := by
      apply ProvableHilbert.Kripke.completeness;
      intro κ _ M _ x;
      simp only [TBB, Model.World.forces_imp];
      tauto;
    exact Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mdp (provable_of_provable_GL hK) hTBB) ih;

/-- The deduction-theorem direction: if `GL ⊢ ∼□^[n]⊥ 🡒 A` for some `n`, then `A ∈ LogicA`. -/
lemma provable_of_provable_GL_neg_boxItr_bot_imp (h : ((∼□^[n]⊥) 🡒 A) ∈ LogicGL) :
    A ∈ LogicA :=
  Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_neg_boxItr_bot


section

/--
  Intrinsic definition of `LogicA` avoiding `subst` (for `substlessInductionGP`).
  Corresponds to the alternative axiomatization of `LogicA` as `LogicGL` extended with
  `∼□^[n]⊥` (for every `n`) instead of `TBB n`.
-/
protected inductive substlessGP : Logic α
  | GL {C : Formula α} : C ∈ LogicGL → LogicA.substlessGP C
  | GP (m : ℕ) : LogicA.substlessGP (∼□^[m]⊥)
  | mdp {C D : Formula α} : LogicA.substlessGP (C 🡒 D) → LogicA.substlessGP C →
      LogicA.substlessGP D

private lemma substlessGP.eq_LogicA : LogicA.substlessGP (α := α) = LogicA := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | GL h => exact provable_of_provable_GL h;
    | GP n => exact provable_neg_boxItr_bot;
    | mdp _ _ ihAB ihA => exact Logic.sumQuasiNormal.mdp ihAB ihA;
  . intro h;
    induction h using LogicA.substlessInductionTBB with
    | GL h => exact LogicA.substlessGP.GL h;
    | TBB n =>
      have h₁ : LogicA.substlessGP (∼□^[n + 1]⊥ : Formula α) :=
        LogicA.substlessGP.GP (n + 1);
      have h₂ : LogicA.substlessGP ((∼□^[n + 1]⊥) 🡒 TBB n : Formula α) := by
        apply LogicA.substlessGP.GL;
        apply ProvableHilbert.Kripke.completeness;
        intro κ _ M _ x;
        simp only [TBB, Model.World.forces_imp];
        tauto;
      exact LogicA.substlessGP.mdp h₂ h₁;
    | mdp ihAB ihA => exact LogicA.substlessGP.mdp ihAB ihA;

private lemma substlessGP.toLogicA (h : LogicA.substlessGP A) : A ∈ LogicA := by
  rw [← LogicA.substlessGP.eq_LogicA]; exact h

private lemma substlessGP.ofLogicA (h : A ∈ LogicA) : LogicA.substlessGP A := by
  rw [LogicA.substlessGP.eq_LogicA]; exact h

/--
  Alternative induction principle for `LogicA`, taking `∼□^[n]⊥` (for every `n`) as the
  axioms instead of `TBB n`, reflecting that `LogicA` is also `LogicGL` extended with
  `∼□^[n]⊥` (`n ∈ ℕ`).
-/
protected lemma substlessInductionGP
  {motive : (A : Formula α) → A ∈ LogicA → Prop}
  (GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (GP : ∀ (n : ℕ), motive (∼□^[n]⊥) provable_neg_boxItr_bot)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicA} → {hA : A ∈ LogicA} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : A ∈ LogicA) → motive A h := by
  intro A h;
  induction LogicA.substlessGP.ofLogicA h with
  | GL hg => exact GL hg;
  | GP n => exact GP n;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := LogicA.substlessGP.toLogicA hAB) (hA := LogicA.substlessGP.toLogicA hA)
      (ihAB _) (ihA _);

end


open Model Model.World

/--
  A theorem of `LogicA` is forced at any world of any finite GL model at which
  `TBB 0, …, TBB (N-1)` hold, for some `N`.
-/
lemma exists_forces_of_forces_instancesBelow_of_provable (h : A ∈ LogicA) :
  ∃ N : ℕ, ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (x : M.World),
  (∀ n < N, x ⊩ TBB n) → x ⊩ A := by
  -- No frame construction (pseudo-tail / tail model / graftOmega) is needed: it suffices
  -- to follow the Hilbert derivation semantically.
  induction h using LogicA.substlessInductionTBB with
  | GL h =>
    use 0;
    intro κ _ M _ x _;
    exact ProvableHilbert.Kripke.soundness h M x;
  | TBB n =>
    use n + 1;
    grind;
  | mdp ihAB ihA =>
    obtain ⟨N₁, ihAB⟩ := ihAB;
    obtain ⟨N₂, ihA⟩ := ihA;
    use max N₁ N₂;
    intro κ _ M _ x hx;
    replace ihAB := ihAB M x (by grind);
    replace ihA := ihA M x (by grind);
    grind;

omit [DecidableEq α] in
/-- From world-level forcing, the root of any finite rooted GL model forces `∼□^[N]⊥ 🡒 A`. -/
lemma root_forces_neg_boxItr_bot_imp
  (h : ∃ N : ℕ, ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] →
    ∀ (x : M.World), (∀ n < N, x ⊩ TBB n) → x ⊩ A)
  : ∃ N : ℕ, ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
  M.root.1 ⊩ ((∼□^[N]⊥) 🡒 A) := by
  obtain ⟨N, hN⟩ := h;
  use N;
  intro κ _ M _;
  -- Bridge via `Kripke.Rank`: `x ⊩ ∼□^[N]⊥ ↔ ∀ n < N, x ⊩ TBB n`, both being `x.rank ≥ N`.
  haveI : Fintype M.World := Fintype.ofFinite _;
  by_contra hC;
  obtain ⟨h₁, h₂⟩ := Model.World.not_forces_imp.mp hC;
  apply h₂;
  apply hN M.toModel M.root.1;
  intro n hn;
  apply Model.iff_forces_TBB_neq_rank.mpr;
  have hge : ¬ M.root.1.rank < N :=
    fun hc => (Model.World.forces_neg.mp h₁) (Model.iff_rank_lt_forces_boxItr_bot.mp hc);
  omega;

/--
  Deduction-theorem-style GL-characterization of `LogicA` (Artemov's logic `A`, `GLαω`):
  `A ∈ LogicA` iff `GL ⊢ ∼□^[n]⊥ 🡒 A` for some `n`. Proved purely from the rank semantics
  of `Kripke.Rank`, without `graftOmega` or `Trace`.
-/
theorem iff_provable_provable_GL_neg_boxItr_bot_imp :
  A ∈ LogicA ↔ ∃ n : ℕ, ((∼□^[n]⊥) 🡒 A) ∈ LogicGL := by
  constructor;
  . intro h;
    obtain ⟨N, hN⟩ := root_forces_neg_boxItr_bot_imp (exists_forces_of_forces_instancesBelow_of_provable h);
    exact ⟨N, LogicGL.iff_forces_root.mpr hN⟩;
  . rintro ⟨n, h⟩;
    exact provable_of_provable_GL_neg_boxItr_bot_imp h;

/--
  If `A ∉ GLαω`, then `GL ⊬ ◇(⋀A.subfmlsS) 🡒 A`. This is the modal input of Lemma 51
  in [AB05], obtained from the chain lemma
  `LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS` and `LogicA.provable_neg_boxItr_bot`.
-/
lemma not_GL_provable_dia_subfmlsS_imp_of_not_mem_LogicA (h : A ∉ LogicA) :
  ((◇(⋀A.subfmlsS)) 🡒 A) ∉ LogicGL := by
  contrapose! h;
  have h₁ : (∼□^[A.subfmls.prebox.card + 1]⊥ : Formula α) ∈ LogicA := LogicA.provable_neg_boxItr_bot;
  have h₂ : ((◇(⋀A.subfmlsS)) : Formula α) ∈ LogicA :=
    Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mem₁ LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS) h₁;
  exact Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ h) h₂;

/--
  A formula outside `GLαω` has a finite rooted `GL` countermodel whose root refutes `A`
  and sees an `A`-reflexive node (the model `K₀` in the proof of Lemma 51 in [AB05]).
-/
lemma exists_reflexive_countermodel_of_not_mem_LogicA (h : A ∉ LogicA) :
  ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
  M.root.1 ⊮ A ∧ ∃ r : M.World, M.root.1 ≺ r ∧ r ⊩ ⋀A.subfmlsS := by
  have := (LogicGL.iff_forces_root (A := (◇(⋀A.subfmlsS)) 🡒 A)).not.mp
    (not_GL_provable_dia_subfmlsS_imp_of_not_mem_LogicA h);
  push Not at this;
  obtain ⟨κ, hne, M, hfgl, hroot⟩ := this;
  obtain ⟨hdia, hnA⟩ := Model.World.not_forces_imp.mp hroot;
  obtain ⟨r, hr, hrS⟩ := Model.World.forces_dia.mp hdia;
  exact ⟨κ, hne, M, hfgl, hnA, r, hr, hrS⟩;

/--
  **ω-model completeness of `GLαω`** (Lemma 5 in §3 of [Bek90], "On the classification
  of propositional provability logics"). The ω-models are realized as `M.graftOmega a`
  for finite rooted GL models `M` and points `a` above the root. The middle item is the
  deduction-theorem form used in the paper's proof.
-/
theorem provability_TFAE : [
  A ∈ LogicA,
  ∃ n : ℕ, ((∼□^[n]⊥) 🡒 A) ∈ LogicGL,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ a : M.World, M.root.1 ≺ a →
    (M.graftOmega a).root.1 ⊩ A
].TFAE := by
  tfae_have 1 → 2 := LogicA.iff_provable_provable_GL_neg_boxItr_bot_imp.mp;
  tfae_have 2 → 3 := by
    rintro ⟨n, hGL⟩ κ _ M _ a Rra;
    haveI := RootedModel.graftOmega.isGL (M := M) (a := a) Rra;
    exact ProvableHilbert.Kripke.soundness hGL ((M.graftOmega a).toModel)
      (M.graftOmega a).root.1
      (Model.World.forces_neg.mpr RootedModel.graftOmega.root_not_forces_boxItr_bot);
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
    exact RootedModel.graftOmega.mainlemma Rrr ha Formula.mem_subfmls_self
      |>.2 M.root.1 |>.mp (h M r Rrr);
  tfae_finish;

/--
  A formula is a `GLαω` theorem iff it is forced at the root of every ω-model
  (Lemma 5 in §3 of [Bek90]).
-/
theorem iff_provable_forces_graftOmega_root :
  A ∈ LogicA ↔
  (∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ a : M.World, M.root.1 ≺ a →
    (M.graftOmega a).root.1 ⊩ A) :=
  LogicA.provability_TFAE.out 0 2

end LogicA

end
