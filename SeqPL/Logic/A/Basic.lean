module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.GL.Basic
public import SeqPL.Logic.S.Basic
public import SeqPL.Logic.D.Basic
public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.Rank
public import SeqPL.Kripke.GraftOmega
public import SeqPL.ProvabilityLogic.Classification.LetterlessTrace
public import SeqPL.ProvabilityLogic.Classification.GeneralTrace

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
  Deduction-theorem-style GL-characterization of `LogicA`:
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
  If `A ∉ LogicA`, then `GL ⊬ ◇(⋀A.subfmlsS) 🡒 A`. Obtained from the chain lemma
  `LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS` and `LogicA.provable_neg_boxItr_bot`.

  - [AB05, Lemma 51]
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
  A formula outside `LogicA` has a finite rooted `GL` countermodel whose root refutes `A`
  and sees an `A`-reflexive node.

  - [AB05, Lemma 51]
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
  ω-model completeness of `LogicA`. The ω-models are realized as `M.graftOmega a`
  for finite rooted GL models `M` and points `a` above the root. The middle item is the
  deduction-theorem form.

  - [Bek90, Lemma 5]
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
    exact RootedModel.graftOmega.mainlemma ⟨r, fun hB => ha _ hB⟩ Rrr Formula.mem_subfmls_self
      |>.2 M.root.1 |>.mp (h M r Rrr);
  tfae_finish;

/--
  A formula is a `LogicA` theorem iff it is forced at the root of every ω-model.

  - [Bek90, Lemma 5]
-/
theorem iff_provable_forces_graftOmega_root :
  A ∈ LogicA ↔
  (∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ a : M.World, M.root.1 ≺ a →
    (M.graftOmega a).root.1 ⊩ A) :=
  LogicA.provability_TFAE.out 0 2

end LogicA


section axiomD

open Model Model.World

variable {a : α} {n : ℕ}

/-- The single point immediately below the root, at which `a` is false. -/
abbrev axiomDCountermodel.bad (n : ℕ) : Fin (n + 2) := ⟨1, by omega⟩

/--
  The `ULift`-lifted chain frame `Fin (n + 2)` refuting `∼□^[n]⊥ 🡒 (□(□a ⋎ □a) 🡒 (□a ⋎ □a))`:
  `a` is false exactly at the single point immediately below the root (`axiomDCountermodel.bad n`)
  and true everywhere else, so every point other than the root forces `□a` (its successors,
  if any, all lie strictly below that single point), while the root itself sees that point
  directly and hence fails `□a`. Lifted to `ULift.{u} (Fin (n + 2))` (as in
  `uLiftFiniteLineModel`) so it can be plugged into `LogicGL.iff_forces_root` at any `α : Type u`.
-/
abbrev axiomDCountermodel (n : ℕ) (_a : α) : RootedModel (ULift.{u} (Fin (n + 2))) α where
  Rel' x y := x.down < y.down
  Val' x _ := x.down ≠ axiomDCountermodel.bad n
  root := ⟨ULift.up 0, by
    rintro ⟨x⟩ hx;
    apply Fin.pos_of_ne_zero;
    intro h;
    apply hx;
    congr 1;
  ⟩

namespace axiomDCountermodel

instance : Fintype (axiomDCountermodel n a).World := inferInstance
instance : (axiomDCountermodel n a).IsFiniteGL where
  finite := inferInstance
instance : (axiomDCountermodel n a).IsGL := Model.instIsGLOfIsFiniteGL

/-- The universe-lifting equivalence between the worlds of `finiteLineModel (n + 1)` and
`axiomDCountermodel n a`, carrying the frame relation `<` to `≺`. -/
def worldEquiv : (finiteLineModel (n + 1)).World ≃ (axiomDCountermodel n a).World := Equiv.ulift.symm

lemma worldEquiv_rel_iff {i j : (finiteLineModel (n + 1)).World} :
  i < j ↔ (worldEquiv (a := a) i : (axiomDCountermodel n a).World) ≺ worldEquiv j := Iff.rfl

lemma rank_eq (x : (axiomDCountermodel n a).World) : x.rank = (n + 1) - x.down := by
  haveI : IsConverseWellFounded (finiteLineModel (n + 1)).World (finiteLineModel (n + 1)).Rel :=
    ⟨(inferInstance : (finiteLineModel (n + 1)).IsGL).cwf⟩;
  haveI : IsConverseWellFounded (axiomDCountermodel n a).World (axiomDCountermodel n a).Rel :=
    ⟨(inferInstance : (axiomDCountermodel n a).IsGL).cwf⟩;
  obtain ⟨i, rfl⟩ := worldEquiv.surjective x;
  show cwfHeight (axiomDCountermodel n a).Rel (worldEquiv i) = (n + 1 - i);
  rw [← cwfHeight_congr (R := (finiteLineModel (n + 1)).Rel) worldEquiv (fun a b => worldEquiv_rel_iff) i];
  exact finiteLineModel.rank_eq i;

lemma root_rank_eq : (axiomDCountermodel n a).root.1.rank = n + 1 := by
  simpa using rank_eq (a := a) (axiomDCountermodel n a).root.1;

/-- Every point other than the root forces `□a`: any of its successors has `down`-value
strictly past `bad n`, hence is not `bad n` itself. -/
lemma forces_box_atom_of_ne_root {x : (axiomDCountermodel n a).World} (hx : 0 < x.down) :
    x ⊩ (□(#a) : Formula α) := by
  apply Model.World.forces_box.mpr;
  intro z hz;
  show z.down ≠ bad n;
  intro hzbad;
  replace hz : x.down < z.down := hz;
  rw [hzbad] at hz;
  simp only [bad, Fin.lt_def] at hx hz;
  omega;

/-- The root fails `□a`: it sees `bad n` directly, at which `a` is false. -/
lemma root_not_forces_box_atom : ¬(axiomDCountermodel n a).root.1 ⊩ (□(#a) : Formula α) := by
  apply Model.World.not_forces_box.mpr;
  refine ⟨ULift.up (bad n), ?_, ?_⟩;
  . show (0 : Fin (n + 2)) < bad n;
    simp [bad];
  . show ¬(bad n ≠ bad n);
    simp;

/-- The root fails the consequent `□a ⋎ □a` of axiom `D` at `A = B = a`. -/
lemma root_not_forces_axiomD_consequent :
    ¬(axiomDCountermodel n a).root.1 ⊩ ((□(#a) : Formula α) ⋎ □(#a)) := by
  apply Model.World.not_forces_or.mpr;
  exact ⟨root_not_forces_box_atom, root_not_forces_box_atom⟩;

/-- The root forces the antecedent `□(□a ⋎ □a)` of axiom `D` at `A = B = a`. -/
lemma root_forces_axiomD_antecedent :
    (axiomDCountermodel n a).root.1 ⊩ (□((□(#a) : Formula α) ⋎ □(#a))) := by
  apply Model.World.forces_box.mpr;
  intro y hy;
  apply Model.World.forces_or.mpr;
  left;
  apply forces_box_atom_of_ne_root;
  exact hy;

end axiomDCountermodel

/--
  Axiom `D` (`□(□A ⋎ □B) 🡒 (□A ⋎ □B)`), specialized to `A = B = #a`, is not a theorem of
  `LogicA`: for every `n`, `axiomDCountermodel n a` refutes `(∼□^[n]⊥) 🡒 axiomD(a, a)` at
  its root.
-/
theorem LogicA.not_provable_axiomD [DecidableEq α] {a : α} :
    ((□((□(#a) : Formula α) ⋎ □(#a))) 🡒 ((□(#a) : Formula α) ⋎ □(#a))) ∉ (LogicA : Logic α) := by
  rw [LogicA.iff_provable_provable_GL_neg_boxItr_bot_imp];
  rintro ⟨n, hGL⟩;
  have hant : (axiomDCountermodel n a).root.1 ⊩ (∼(□^[n]⊥ : Formula α)) := by
    apply Model.World.forces_neg.mpr;
    intro hc;
    have hlt := Model.iff_rank_lt_forces_boxItr_bot.mpr hc;
    rw [axiomDCountermodel.root_rank_eq] at hlt;
    omega;
  have hcons := (LogicGL.iff_forces_root.mp hGL (M := axiomDCountermodel n a)) hant;
  rcases Model.World.forces_imp.mp hcons with h | h;
  · exact h axiomDCountermodel.root_forces_axiomD_antecedent;
  · exact axiomDCountermodel.root_not_forces_axiomD_consequent h;

/-- `LogicD`, which proves axiom `D`, is not contained in `LogicA` (Artemov's `GLαω`),
since `LogicA.not_provable_axiomD` shows axiom `D` is not a theorem of `LogicA`. -/
theorem not_LogicD_subset_LogicA [DecidableEq α] {a : α} : ¬((LogicD : Logic α) ⊆ LogicA) := by
  intro h;
  exact LogicA.not_provable_axiomD (a := a) (h (LogicD.provable_axiomD (A := #a) (B := #a)));

end axiomD

end
