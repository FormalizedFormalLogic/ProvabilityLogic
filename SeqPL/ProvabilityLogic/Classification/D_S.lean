module

public import SeqPL.Logic.D.Basic
public import SeqPL.ProvabilityLogic.Classification.GeneralTrace
public import SeqPL.Kripke.AlmostDefiningFormula
public import SeqPL.Logic.A.Basic
public import SeqPL.Kripke.DModelTree
public import SeqPL.Kripke.Unravelling

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/--
  The `p ↔ q` substitution used in the proof of Lemma 1: for a finite set of atoms
  `S`, replace every `q ∈ S` by `#p 🡘 #q`, leaving other atoms (in particular `p`
  itself) untouched.

  - [Bek90, Lemma 1]
-/
noncomputable def Formula.Substitution.pIffOn (p : α) (S : Finset α) : Formula.Substitution α α :=
  fun q => if q ∈ S then (#p 🡘 #q) else #q

@[simp]
lemma Formula.atoms_pIffOn [DecidableEq α] (p a : α) (S : Finset α) :
    (Formula.Substitution.pIffOn p S a).atoms ⊆ insert p {a} := by
  unfold Formula.Substitution.pIffOn;
  split;
  . intro x hx;
    simp only [Formula.atoms, Finset.mem_union] at hx;
    simp only [Finset.mem_insert, Finset.mem_singleton];
    grind;
  . simp [Formula.atoms];

/--
  The conjunction `Δ` of Lemma 1: over all `2^n` subsets `S` of `A`'s atoms, the
  substitution instance of `A` obtained by replacing every atom in `S` with
  `p ↔ (that atom)`.

  - [Bek90, Lemma 1]
-/
noncomputable def Formula.deltaPIff [DecidableEq α] (A : Formula α) (p : α) : Formula α :=
  ⋀(A.atoms.powerset.image (fun S => A⟦.pIffOn p S⟧))

/--
  Transfer of forcing along a *stabilized* bisimulation-under-`P` `Bi` (our surrogate
  for the paper's "the stabilizations are `q̄`-isomorphic", see
  `RootedModel.StabilizedBisimulationUnder` -- the atomic clause is waived at the
  roots, whose valuations may genuinely disagree on `P`) combined with the `p ↔ q`
  substitution. If `M₂`'s root forces `□p` but not `p` itself (`p` a fresh atom, not
  in `P`), then for any `Bi`-related pair `(x, x')` and any formula `C` depending on
  `P`, forcing of `C` at `x` agrees with forcing, at `x'`, of `C` with every atom in
  `γ` replaced by `p ↔ (that atom)` -- where `γ` records exactly the atoms on which
  the two roots' valuations disagree.

  - [Bek90, Lemma 1.1]
-/
theorem RootedModel.StabilizedBisimulationUnder.forces_iff_subst_pIffOn [DecidableEq α]
    {κ₁ κ₂ : Type u} [Nonempty κ₁] [Nonempty κ₂]
    {M₁ : RootedModel κ₁ α} {M₂ : RootedModel κ₂ α} {P : Finset α} {p : α}
    (Bi : RootedModel.StabilizedBisimulationUnder P M₁ M₂)
    (hp_box : M₂.root.1 ⊩ (□(#p))) (hp_root : M₂.root.1 ⊮ (#p)) {γ : Finset α}
    (hγ_root : ∀ q ∈ P, (q ∈ γ ↔ ¬ (M₁.Val M₁.root.1 q ↔ M₂.Val M₂.root.1 q))) :
    ∀ {x₁ : M₁.World} {x₂ : M₂.World}, Bi x₁ x₂ →
      ∀ {C : Formula α}, C.atoms ⊆ P → (x₁ ⊩ C ↔ x₂ ⊩ C⟦.pIffOn p γ⟧) := by
  -- Away from the roots, `M₂`'s root forces `□p`, so `x₂ ⊩ p` holds outright
  -- (`x₂ ≠ M₂.root.1`), making the substituted atom `p ↔ q` forcing-equivalent to plain
  -- `q`, so the bisimulation's atomic clause suffices directly. At the roots themselves
  -- `x₂ ⊩ p` is not `True` in general (`M₂`'s root additionally satisfies `¬p` by
  -- hypothesis), so the compensating substitution is exactly needed there, and `γ` is
  -- defined precisely to make it work out.
  intro x₁ x₂ Bx₁x₂ C;
  induction C generalizing x₁ x₂ with
  | atom q =>
    intro hq;
    replace hq : q ∈ P := hq (Finset.mem_singleton_self q);
    show (M₁.Val x₁ q ↔ x₂ ⊩ (Formula.Substitution.pIffOn p γ q));
    simp only [Formula.Substitution.pIffOn];
    split;
    case isTrue hqγ =>
      rw [forces_iff];
      by_cases hxroot : x₂ = M₂.root.1;
      . obtain rfl : x₁ = M₁.root.1 := (Bi.root_reflect Bx₁x₂).mp hxroot;
        subst hxroot;
        have hγq := (hγ_root q hq).mp hqγ;
        show (M₁.Val M₁.root.1 q ↔ (M₂.Val M₂.root.1 p ↔ M₂.Val M₂.root.1 q));
        have hnp : ¬ M₂.Val M₂.root.1 p := hp_root;
        tauto;
      . have hx₂p : M₂.Val x₂ p := hp_box x₂ (M₂.root.2 x₂ hxroot);
        show (M₁.Val x₁ q ↔ (M₂.Val x₂ p ↔ M₂.Val x₂ q));
        have := Bi.atomic hq Bx₁x₂ hxroot;
        tauto;
    case isFalse hqγ =>
      by_cases hxroot : x₂ = M₂.root.1;
      . obtain rfl : x₁ = M₁.root.1 := (Bi.root_reflect Bx₁x₂).mp hxroot;
        subst hxroot;
        show (M₁.Val M₁.root.1 q ↔ M₂.Val M₂.root.1 q);
        have hnn : ¬¬(M₁.Val M₁.root.1 q ↔ M₂.Val M₂.root.1 q) :=
          fun hne => hqγ ((hγ_root q hq).mpr hne);
        exact not_not.mp hnn;
      . exact Bi.atomic hq Bx₁x₂ hxroot;
  | bot => intro _; exact Iff.rfl;
  | imp A B ihA ihB =>
    intro hAB;
    simp only [Formula.atoms, Finset.union_subset_iff] at hAB;
    replace ihA := ihA Bx₁x₂ hAB.1;
    replace ihB := ihB Bx₁x₂ hAB.2;
    rw [Formula.subst_imp];
    constructor;
    . intro h hA; exact ihB.mp (h (ihA.mpr hA));
    . intro h hA; exact ihB.mpr (h (ihA.mp hA));
  | box A ihA =>
    intro hA;
    replace hA : A.atoms ⊆ P := by simpa [Formula.atoms] using hA;
    simp only [Formula.subst_box, forces_box];
    constructor;
    . intro h y₂ Rxy₂;
      obtain ⟨y₁, hyy, Rxy₁⟩ := Bi.back Bx₁x₂ Rxy₂;
      exact (ihA hyy hA).mp (h y₁ Rxy₁);
    . intro h y₁ Rxy₁;
      obtain ⟨y₂, hyy, Rxy₂⟩ := Bi.forth Bx₁x₂ Rxy₁;
      exact (ihA hyy hA).mpr (h y₂ Rxy₂);

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
-- lies in the quasi-normal extension `LogicA +ᴸ A`. -/
lemma provable_deltaPIff [DecidableEq α] {A : Formula α} {p : α} :
    A.deltaPIff p ∈ (LogicA +ᴸ A) := by
  -- `A` itself lies in `LogicA +ᴸ A` (`mem₂`), and quasi-normal extensions are closed
  -- under substitution, so every conjunct of `A.deltaPIff p` does too.
  apply provable_fconj_LogicA_add;
  intro B hB;
  obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hB;
  exact Logic.sumQuasiNormal.subst (Logic.sumQuasiNormal.mem₂ rfl);

end

section

open RootedModel

/--
  If `D ⊬ A`, there is a D-model refuting `A`, realized as a tree-shaped ω-model: a
  finite GL tree `M` and a point `a` covering the root with no lateral cones such
  that `A` fails at the root of `M.graftOmega a`.

  - [Bek90, Lemma 3]
-/
theorem LogicD.exists_graftOmega_countermodel_of_not_mem [DecidableEq α]
    {A : Formula α} (hA : A ∉ LogicD) :
    ∃ (κ : Type u) (_ : Nonempty κ)
      (M : RootedModel κ α) (a : M.World),
      M.IsFiniteGL ∧
      M.IsTree ∧
      M.root.1 ≺ a ∧
      (∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1) ∧
      (∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a) ∧
      (M.graftOmega a).root.1 ⊮ A := by
  -- Obtained by combining the pseudo-tail semantics of `D` (`LogicD.provability_TFAE`)
  -- with the D-model tree realization (`Model.dModelTree`).
  obtain ⟨κ, hne, M, hgl, r, o, hno⟩ := LogicD.exists_not_forces_toPseudoTail_of_not_mem hA;
  use (Model.dModelTree.World M), inferInstance, M.dModelTree r o, Model.dModelTree.tailPoint;
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩;
  . infer_instance;
  . infer_instance;
  . exact Model.dModelTree.root_rel_tailPoint;
  . exact Model.dModelTree.tailPoint_covers_root;
  . exact Model.dModelTree.isInConeOf_tailPoint_of_root_rel;
  . contrapose! hno;
    exact Model.dModelTree.graftOmega_root_forces_iff.mp hno;

/--
  A modalized formula forced at the root of a (tree-shaped) D-model has an
  `S`-unprovable negation.

  - [Bek90, Lemma 4]
-/
lemma not_mem_LogicS_neg_of_graftOmega_root_forces_modalized [DecidableEq α]
    {κ : Type u} [Nonempty κ] {M : RootedModel κ α} [M.IsFiniteGL] {a : M.World}
    (Rra : M.root.1 ≺ a) (hlat : ∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a)
    {C : Formula α} (hmod : C.Modalized) (hC : (M.graftOmega a).root.1 ⊩ C) :
    (∼C) ∉ LogicS := by
  -- The stabilization of the D-model is a tail model, on whose chain the formula is
  -- eventually forced (realized by
  -- `graftOmega.eventually_coneTail_chainPoint_forces_iff_of_modalized`), so the
  -- tail-model semantics of `S` (`LogicS.provability_TFAE`) refutes the negation.
  intro hS;
  have hall := LogicS.provability_TFAE (A := ∼C) |>.out 0 1 |>.mp hS;
  obtain ⟨k₀, h₀⟩ :=
    hall (Model.toRootedModel M.toModel a).toModel (Model.toRootedModel M.toModel a).root.1;
  obtain ⟨k₁, h₁⟩ :=
    graftOmega.eventually_coneTail_chainPoint_forces_iff_of_modalized Rra hlat hmod;
  have h₂ := (h₁ (max k₀ k₁) (le_max_right _ _)).mpr hC;
  have h₃ := h₀ (max k₀ k₁) (le_max_left _ _);
  exact (forces_neg.mp h₃) h₂;

/-- The atoms of `A.deltaPIff p` are contained in `A.atoms ∪ {p}`. -/
lemma Formula.atoms_deltaPIff_subset [DecidableEq α] {A : Formula α} {p : α} :
    (A.deltaPIff p).atoms ⊆ insert p A.atoms := by
  intro q hq;
  have h₁ := FormulaFinset.atoms_conj_subset _ hq;
  simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at h₁;
  obtain ⟨B, ⟨S, -, rfl⟩, hqB⟩ := h₁;
  obtain ⟨b, hb, hqb⟩ := Finset.mem_biUnion.mp (Formula.atoms_subst_subset hqB);
  rcases Finset.mem_insert.mp (Formula.atoms_pIffOn p b S hqb) with rfl | h₂;
  . exact Finset.mem_insert_self _ _;
  . exact Finset.mem_insert_of_mem (Finset.mem_singleton.mp h₂ ▸ hb);

/--
  The semantic core: if `D ⊬ A`, there is a formula `B` over the atoms of `A`, not
  provable in `S`, such that `LogicA ⊢ A.deltaPIff p → B ⋎ (□p → p)`.

  - [Bek90, Lemma 1, Lemma 3, Lemma 4, Lemma 7, Lemma 8, Lemma 9]
-/
theorem exists_not_mem_LogicS_provable_LogicA_deltaPIff_imp_of_not_mem_LogicD [DecidableEq α]
    {A : Formula α} {p : α} (hp : p ∉ A.atoms) (hA : A ∉ LogicD) :
    ∃ B : Formula α, B.atoms ⊆ A.atoms ∧ B ∉ LogicS ∧
      (A.deltaPIff p 🡒 (B ⋎ ((□(#p)) 🡒 (#p)))) ∈ LogicA := by
  classical
  -- **Lemma 3**: a D-model countermodel to `A`, realized as a tree-shaped ω-model.
  obtain ⟨κ₁, hne₁, M₁, hgl₁, htree₁, a₁, Rra₁, hcov₁, hlat₁, hnA₁⟩ :=
    LogicD.exists_graftOmega_countermodel_of_not_mem hA;
  haveI := hne₁; haveI := hgl₁; haveI := htree₁;
  -- **Lemma 8**: `A.atoms`-simplification, staying a tree-shaped D-model.
  obtain ⟨κ₂, hne₂, M₂, hgl₂, htree₂, a₂, Rra₂, hcov₂, hlatimp₂, hsimple₂, htrans₂⟩ :=
    exists_simplificationUnder_omega' Rra₁ hcov₁ A.atoms;
  haveI := hne₂; haveI := hgl₂; haveI := htree₂;
  have hlat₂ := hlatimp₂ hlat₁;
  have hnA₂ : (M₂.graftOmega a₂).root.1 ⊮ A :=
    fun h => hnA₁ ((htrans₂ A (Finset.Subset.refl _)).mpr h);
  -- **Lemma 9**: the almost defining formula of the simplified D-model.
  obtain ⟨B, hBatoms, hBmod, hBroot, hBdef⟩ :=
    graftOmega.exists_almostDefiningFormula Rra₂ hcov₂ hlat₂ hsimple₂;
  refine ⟨∼B, by rw [Formula.atoms_neg]; exact hBatoms, ?_, ?_⟩;
  . -- `S ⊬ ∼B` (Lemma 4 of [Bek90] §4 + the tail-model semantics of `S`)
    exact not_mem_LogicS_neg_of_graftOmega_root_forces_modalized Rra₂ hlat₂ hBmod hBroot;
  . -- `GLαω ⊢ Δ 🡒 ∼B ⋎ (□p 🡒 p)`, by the ω-model semantics of `GLαω`.
    apply LogicA.iff_provable_forces_graftOmega_root.mpr;
    intro κ₃ hne₃ N hgl₃ c Rrc;
    haveI := hne₃; haveI := hgl₃;
    by_contra hcon;
    -- Pass to the tree unravelling, where the grafted point covers the root.
    rw [← unravelling.graftOmega_root_forces_iff Rrc] at hcon;
    -- **Lemma 8** again: `(A.atoms ∪ {p})`-simplification of the putative countermodel.
    obtain ⟨κ₄, hne₄, L, hgl₄, htree₄, c₄, Rrc₄, hcov₄, -, hsimple₄, htrans₄⟩ :=
      exists_simplificationUnder_omega' (unravelling.root_rel_coverPoint Rrc)
        (unravelling.coverPoint_covers_root Rrc) (insert p A.atoms);
    haveI := hne₄; haveI := hgl₄; haveI := htree₄;
    haveI hLgl : (L.graftOmega c₄).IsGL := graftOmega.isGL Rrc₄;
    haveI : IsTrans _ (L.graftOmega c₄).Rel := hLgl.toIsTrans;
    haveI : IsConverseWellFounded _ (L.graftOmega c₄).Rel := hLgl.toIsConverseWellFounded;
    haveI : Std.Irrefl (L.graftOmega c₄).Rel := ConverseWellFounded.irrefl;
    -- Unpack the countermodel and transport each part along the simplification.
    obtain ⟨hΔT, hdisjT⟩ := not_forces_imp.mp hcon;
    obtain ⟨hnBT, hnTT⟩ := not_forces_or.mp hdisjT;
    obtain ⟨hboxT, hnpT⟩ := not_forces_imp.mp hnTT;
    have hpin : ((#p : Formula α)).atoms ⊆ insert p A.atoms := by
      simp [Formula.atoms];
    have hΔ := (htrans₄ _ Formula.atoms_deltaPIff_subset).mp hΔT;
    have hBL : (L.graftOmega c₄).root.1 ⊩ B :=
      (htrans₄ B (hBatoms.trans (Finset.subset_insert _ _))).mp (not_forces_neg.mp hnBT);
    have hboxp : (L.graftOmega c₄).root.1 ⊩ (□(#p)) :=
      (htrans₄ (□(#p)) (by rwa [Formula.atoms_box])).mp hboxT;
    have hnp : (L.graftOmega c₄).root.1 ⊮ (#p) :=
      fun hc => hnpT ((htrans₄ (#p) hpin).mpr hc);
    -- `□p` at the root downgrades `(A.atoms ∪ {p})`-simplicity to `A.atoms`-simplicity.
    have hsimpleP : (L.graftOmega c₄).IsSimpleUnder A.atoms :=
      hsimple₄.of_insert_of_root_forces_box hboxp;
    -- The almost-defining property yields a stabilized bisimulation to the D-model.
    obtain ⟨Bi⟩ := hBdef L c₄ Rrc₄ hcov₄ hsimpleP hBL;
    -- `γ` records the atoms on which the two roots disagree.
    set γ : Finset α := A.atoms.filter
      (fun q => ¬((M₂.graftOmega a₂).Val (M₂.graftOmega a₂).root.1 q ↔
        (L.graftOmega c₄).Val (L.graftOmega c₄).root.1 q)) with hγdef;
    have hγ_root : ∀ q ∈ A.atoms,
        (q ∈ γ ↔ ¬((M₂.graftOmega a₂).Val (M₂.graftOmega a₂).root.1 q ↔
          (L.graftOmega c₄).Val (L.graftOmega c₄).root.1 q)) := by
      intro q hq;
      simp [hγdef, Finset.mem_filter, hq];
    -- **Lemma 1.1**: transport `¬A` along the `p ↔ q` substitution at `γ`.
    have htransport :=
      Bi.forces_iff_subst_pIffOn hboxp hnp hγ_root Bi.root_rel (Finset.Subset.refl A.atoms);
    -- The `γ`-conjunct of `Δ` is forced at the root, contradiction.
    have hconj : (L.graftOmega c₄).root.1 ⊩ (A⟦Formula.Substitution.pIffOn p γ⟧) := by
      apply forces_fconj.mp hΔ;
      exact Finset.mem_image_of_mem _ (Finset.mem_powerset.mpr (Finset.filter_subset _ _));
    exact hnA₂ (htransport.mpr hconj);

end

/--
  If `D ⊬ A` then there is `B` over the atoms of `A` such that `S ⊬ B` and
  `LogicA +ᴸ A ⊢ B ⋎ (□p 🡒 p)` for an atom `p` not occurring in `A`.

  - [AB05, Lemma 56]
  - [Bek90, Lemma 1]
-/
theorem exists_not_mem_LogicS_disj_boxImp_mem_LogicA_add_of_not_mem_LogicD [DecidableEq α]
    {A : Formula α} {p : α} (hp : p ∉ A.atoms) (hA : A ∉ LogicD) :
    ∃ B : Formula α, B ∉ LogicS ∧ B.atoms ⊆ A.atoms ∧
      (B ⋎ ((□(#p)) 🡒 (#p))) ∈ (LogicA +ᴸ A) := by
  -- The semantic content (Kripke-model analysis of `D` via `q`-simplification and
  -- almost defining formulas, [Bek90] §4) is isolated in
  -- `exists_not_mem_LogicS_provable_LogicA_deltaPIff_imp_of_not_mem_LogicD` above; this
  -- is the elementary propositional assembly on top of it: `A.deltaPIff p` is a finite
  -- conjunction of substitution instances of `A`, hence provable in `LogicA +ᴸ A` by
  -- the substitution rule, so modus ponens with the semantic core's implication gives
  -- the result directly.
  obtain ⟨B, hBatoms, hBS, hImp⟩ :=
    exists_not_mem_LogicS_provable_LogicA_deltaPIff_imp_of_not_mem_LogicD hp hA;
  exact ⟨B, hBS, hBatoms,
    Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ hImp) provable_deltaPIff⟩;

/--
  If the provability logic of `T` relative to `U` has trace `ω` and contains some
  `A ∉ D`, then `U` proves the local reflection schema for `T`. The fresh atom is
  manufactured by passing to `Option α`.

  - [Bek90, Theorem 1]
  - [AB05, Lemma 57]
-/
theorem provable_reflection_of_mem_not_LogicD :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ∀ {A : Formula α}, A ∈ L → A ∉ LogicD →
    ∀ σ : ArithmeticSentence, U ⊢ (T.standardProvability σ) 🡒 σ := by
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
  `D`, then it contains `S`.

  - [Bek90, Assertion 1]
  - [AB05, Lemma 56, Lemma 57]
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
  No provability logic lies strictly between `D` and `S`.

  - [AB05, Corollary 58]
-/
theorem no_logic_between_LogicD_LogicS :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → ¬((LogicD ⊂ L) ∧ (L ⊂ LogicS)) := by
  rintro hT ⟨h₁, h₂⟩;
  exact h₂.not_subset (subset_LogicS_of_ssubset_LogicD_of_univ_trace hT h₁);

end
