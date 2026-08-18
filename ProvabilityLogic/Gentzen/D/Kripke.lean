module

public import ProvabilityLogic.Gentzen.D.Basic
public import ProvabilityLogic.Gentzen.S.Kripke
public import ProvabilityLogic.Kripke.PseudoTail
public import ProvabilityLogic.Kripke.Cone

/-!
Semantic cut-elimination for the sequent calculus for the provability logic `D`, restricted
to the limit ordinal ω: cut-free `LogicD.ProofGentzen`-provability of a level-`2` sequent
coincides with `LogicD.GentzenWithCutProof`-provability, with validity at the root of every
constant, respectively free, ω-extension of every `GL`-model as the semantic bridge between
the two.

- [KKIM25, Theorem 5.8]
-/

@[expose]
public section

open LogicGL Model
open scoped LogicS FormulaFinset

universe u v

variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
/--
  A finite pigeonhole principle: if a predicate `P D j` has a witness `D` in a fixed finite
  set `Γ'` for every `j` beyond some `i`, then some single `D ∈ Γ'` witnesses it cofinally
  often.

  Folklore.
-/
private lemma exists_mem_forall_exists_ge {Γ' : FormulaFinset α} {P : Formula α → ℕ → Prop} {i : ℕ}
    (h : ∀ j ≥ i, ∃ D ∈ Γ', P D j) : ∃ D ∈ Γ', ∀ n, ∃ j ≥ n, P D j := by
  by_contra hcon;
  push Not at hcon;
  choose! n_D hn_D using hcon;
  obtain ⟨D, hD, hPD⟩ := h (max i (Γ'.sup n_D)) (le_max_left _ _);
  exact hn_D D hD (max i (Γ'.sup n_D)) (le_trans (Finset.le_sup hD) (le_max_right _ _)) hPD;

namespace LogicD

open ProvableGentzen

namespace GentzenWithCutProvable

/--
  Soundness of `LogicD.GentzenWithCutProof` at level `2`: every proof of a level-`2` sequent
  is forced at the root (ω) of every free ω-extension of every `GL`-model.

  - [KKIM25, Theorem 5.8]
-/
theorem soundness_aux {S : ThreeLayeredSequent α} (h : ⊢ᵍᶜ[D] S) (hl : S.level = 2) :
    ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (V : ℕ∞ → α → Prop),
    (M.toFreeTail V).root.1 ⊩[_] S.toSequent := by
  revert hl;
  induction h using LogicD.GentzenWithCutProvable.rec with
  | axm l A => intro _ κ _ M _ V; exact Model.World.forces_sequent_axm;
  | botL l => intro _ κ _ M _ V; exact Model.World.forces_sequent_botL;
  | wkL h h' ih => intro hl κ _ M _ V; exact Model.World.forces_sequent_wkL (ih hl M V) h';
  | wkR h h' ih => intro hl κ _ M _ V; exact Model.World.forces_sequent_wkR (ih hl M V) h';
  | impL h₁ h₂ ih₁ ih₂ =>
    intro hl κ _ M _ V;
    exact Model.World.forces_sequent_impL (ih₁ hl M V) (ih₂ hl M V);
  | impR h ih => intro hl κ _ M _ V; exact Model.World.forces_sequent_impR (ih hl M V);
  | liftUp₀₁ h ih => intro hl; exact absurd (show (1 : Fin 3) = 2 from hl) (by decide);
  | boxGL h ih => intro hl; exact absurd (show (0 : Fin 3) = 2 from hl) (by decide);
  | boxL h ih => intro hl; exact absurd (show (1 : Fin 3) = 2 from hl) (by decide);
  | liftUp₁₂ h₁ ih =>
    rename_i Γ Δ;
    intro _ κ _ M _ V hΓ;
    have hS := toGentzenWithCutProvableS h₁;
    obtain ⟨X, hX⟩ := LogicS.GentzenWithCutProvable.soundness hS;
    have hw : ∀ n : ℕ, (toFreeTail.chainPoint ((n + 1 : ℕ) : ℕ∞) : (M.toFreeTail V).World) ≺
        toFreeTail.chainPoint ((n : ℕ) : ℕ∞) :=
      fun n => toFreeTail.rel_chainPoint_chainPoint.mpr (by exact_mod_cast Nat.lt_succ_self n);
    obtain ⟨i, hi⟩ :=
      eventually_forces_of_exists_isReflexive_forces
        (fun {κ} [Nonempty κ] (M : Model κ α) [M.IsGL] => ⟨X, hX M⟩)
        (M.toFreeTail V).toModel (fun n => toFreeTail.chainPoint (n : ℕ∞)) hw;
    have hΓ' : ∀ n : ℕ, ∀ C ∈ □Γ,
        toFreeTail.chainPoint (n : ℕ∞) ⊩[(M.toFreeTail V).toModel] C := by
      intro n C hC;
      obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC;
      exact toFreeTail.forces_box_of_root_forces_box (hΓ _ hC);
    obtain ⟨D, hD, hfreq⟩ :=
      exists_mem_forall_exists_ge (Γ' := □Δ)
        (P := fun D j => toFreeTail.chainPoint (j : ℕ∞) ⊩[(M.toFreeTail V).toModel] D)
        (i := i) (fun j hj => hi j hj (hΓ' j));
    obtain ⟨D₀, hD₀, rfl⟩ := Finset.mem_image.mp hD;
    exact ⟨□D₀, Finset.mem_image.mpr ⟨D₀, hD₀, rfl⟩,
      toFreeTail.root_forces_box_of_frequently_chainPoint_forces hfreq⟩;
  | cut h₁ h₂ ih₁ ih₂ =>
    intro hl κ _ M _ V;
    exact Model.World.forces_sequent_cut (ih₁ hl M V) (ih₂ hl M V);

/--
  Soundness of `LogicD.GentzenWithCutProof` for level-`2` sequents `Γ ⟹[2] Δ`, against the
  class of free ω-extensions of `GL`-models.

  - [KKIM25, Theorem 5.8]
-/
theorem soundness {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[D] (Γ ⟹[2] Δ)) :
    ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (V : ℕ∞ → α → Prop),
    (M.toFreeTail V).root.1 ⊩[_] (Γ ⟹ Δ) :=
  soundness_aux h rfl

end GentzenWithCutProvable

namespace ProvableGentzen

/--
  If a level-`2` sequent is `LogicD.ProvableGentzen`-unprovable then the underlying plain
  sequent is `LogicGL.ProvableGentzen`-unprovable.

  - [KKIM25, Theorem 5.8]
-/
lemma not_provable_GL_of_not_provable_2 {Γ Δ : FormulaFinset α} (h : ⊬ᵍ[D] (Γ ⟹[2] Δ)) :
    ⊬ᵍ[GL] (Γ ⟹ Δ) :=
  fun hGL => h (provable_2_of_provableGentzen_GL hGL)

/--
  If a level-`2` sequent is `LogicD.ProvableGentzen`-unprovable then the boxed sequent
  `□(Γ.prebox) ⟹ □(Δ.prebox)` is `LogicS.ProvableGentzen`-unprovable at level `1`.

  - [KKIM25, Theorem 5.8]
-/
lemma not_provable_S_box_prebox_of_not_provable_2 {Γ Δ : FormulaFinset α} (h : ⊬ᵍ[D] (Γ ⟹[2] Δ)) :
    ¬ LogicS.ProvableGentzen ((□(Γ.prebox)) ⟹[1] (□(Δ.prebox))) :=
  fun hS => h (wkR
    (wkL (liftUp₁₂ (iff_provableGentzenS_provable_1.mp hS)) FormulaFinset.box_prebox_subset)
    FormulaFinset.box_prebox_subset)

end ProvableGentzen

/--
  A sequent saturated for the level-`2` fragment of `LogicD.ProofGentzen`: besides the
  implicational saturation conditions of `Sequent.Saturated`, all formulas come from the
  subformulas of the base sequent `BS`, and the associated level-`2` sequent is
  `LogicD.ProvableGentzen`-unprovable.

  - [KKIM25, Definition 5.2, Lemma 5.3]
-/
structure ExpandedLayeredSequent (BS : Sequent α) extends Sequent α where
  saturated      : toSequent.Saturated
  subset_subfmls : toSequent.ant ∪ toSequent.suc ⊆ BS.subfmls
  unprovable     : ⊬ᵍ[D] (toSequent.ant ⟹[2] toSequent.suc)

namespace ExpandedLayeredSequent

attribute [grind .] saturated subset_subfmls unprovable

variable {BS : Sequent α} {S : ExpandedLayeredSequent BS} {A B : Formula α}

lemma not_mem_both : ¬(A ∈ S.1.1 ∧ A ∈ S.1.2) := by
  push Not;
  intro h₁ h₂;
  exact S.unprovable (ProvableGentzen.union' 2 A h₁ h₂);

lemma not_mem_bot_ant : ⊥ ∉ S.1.1 := by
  intro h;
  exact S.unprovable (ProvableGentzen.botL_mem 2 h);

open Classical in
/--
  One step of the Lindenbaum-style saturation for level-`2` sequents of
  `LogicD.ProofGentzen`: process the given list of formulas, saturating the sequent for
  `impL` and `impR` while preserving level-`2` unprovability.

  - [KKIM25, Definition 5.2, Lemma 5.3]
-/
noncomputable def lindenbaum_indexed (S₀ : Sequent α) (S₀_unprovable : ⊬ᵍ[D] (S₀.ant ⟹[2] S₀.suc)) :
    FormulaList α → { S : Sequent α // ⊬ᵍ[D] (S.ant ⟹[2] S.suc) }
  | [] => ⟨S₀, S₀_unprovable⟩
  | (A 🡒 B) :: Γ =>
    let ⟨S, hS⟩ := lindenbaum_indexed S₀ S₀_unprovable Γ;
    if h : (A 🡒 B) ∈ S.1 then
      if h : ⊬ᵍ[D] ((S.1) ⟹[2] (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
      else ⟨((insert B S.1) ⟹ S.2), by
        push Not at h;
        contrapose! hS;
        have := ProvableGentzen.impL h hS;
        rwa [(show insert (A 🡒 B) S.1 = S.1 by grind)] at this;
      ⟩
    else if h : (A 🡒 B) ∈ S.2 then ⟨
      ((insert A S.1) ⟹ (insert B S.2)),
      by
        contrapose! hS;
        have := ProvableGentzen.impR hS;
        rwa [(show insert (A 🡒 B) S.2 = S.2 by grind)] at this;
    ⟩
    else ⟨S, hS⟩
  | _ :: Γ => lindenbaum_indexed S₀ S₀_unprovable Γ

variable {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[D] (S₀.ant ⟹[2] S₀.suc)} {Γ : FormulaList α}

lemma subset_lindenbaum_indexed : S₀ ⊆ (lindenbaum_indexed S₀ S₀_unprovable Γ).1 := by
  induction Γ with
  | nil => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons A Γ ih =>
    match A with
    | #a | Formula.box _ | ⊥ => exact ih
    | A 🡒 B =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2.trans (Finset.subset_insert _ _)⟩
      · exact ⟨ih.1, ih.2⟩;

lemma subfmls_lindenbaum_indexed (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls) (hΓ : ∀ C ∈ Γ, C ∈ BS.subfmls) :
    (lindenbaum_indexed S₀ S₀_unprovable Γ).1.1 ∪ (lindenbaum_indexed S₀ S₀_unprovable Γ).1.2 ⊆ BS.subfmls := by
  induction Γ with
  | nil => exact S₀sub
  | cons A Γ ih =>
    replace ih := ih (by grind);
    match A with
    | #a | Formula.box _ | ⊥ => exact ih
    | (A 🡒 B) =>
      dsimp only [lindenbaum_indexed];
      have : (A 🡒 B) ∈ BS.subfmls := hΓ _ (by simp)
      have : A ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind;
      have : B ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind;
      split_ifs;
      all_goals
      . intro;
        grind;

/--
  Saturation of the level-`2` Lindenbaum construction: the resulting sequent is `impL`- and
  `impR`-saturated for the formulas listed in `Γ`.

  - [KKIM25, Definition 5.2, Lemma 5.3]
-/
lemma saturated_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
    let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
    (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.1 → A ∈ S.1.2 ∨ B ∈ S.1.1) ∧
    (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.2 → A ∈ S.1.1 ∧ B ∈ S.1.2) := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil => intro _; constructor <;> intro A B hmem _ <;> simp at hmem
  | cons x Γ' ih =>
    intro hΓ
    rw [List.pairwise_cons] at hΓ
    obtain ⟨hhead, htail⟩ := hΓ
    obtain ⟨ihL, ihR⟩ := ih htail
    match x with
    | #a | Formula.box _ | ⊥ =>
      constructor
      · intro A B hmem hx
        refine ihL ?_ hx
        rcases List.mem_cons.mp hmem with h | h
        · simp at h
        · exact h
      · intro A B hmem hx
        refine ihR ?_ hx
        rcases List.mem_cons.mp hmem with h | h
        · simp at h
        · exact h
    | C 🡒 D =>
      have hunp : ⊬ᵍ[D] ((lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ⟹[2]
          (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc) :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2
      dsimp only [lindenbaum_indexed]
      split_ifs with h1 h2 h3 <;>
        refine ⟨?_, ?_⟩ <;>
        intro A B hmem hx <;>
        simp only [List.mem_cons] at hmem <;>
        grind [ProvableGentzen.union']

/--
  Lindenbaum-style saturation for level-`2` sequents of `LogicD.ProofGentzen`: every level-`2`
  unprovable sequent within the subformulas of `BS` extends to a saturated, level-`2`
  unprovable sequent.

  - [KKIM25, Definition 5.2, Lemma 5.3]
-/
noncomputable def lindenbaum (BS : Sequent α) (S₀ : Sequent α)
    (S₀_unprovable : ⊬ᵍ[D] (S₀.ant ⟹[2] S₀.suc)) (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls) :
    ExpandedLayeredSequent BS :=
  letI Γ := BS.subfmls.toList.insertionSort (·.complexity ≤ ·.complexity);
  letI S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  haveI hΓsorted : (Γ.map (·.complexity)).SortedLE := by
    rw [List.map_insertionSort (f := Formula.complexity) (l := BS.subfmls.toList)
      (r := λ A B => ((A.complexity) ≤ (B.complexity))) (s := (· ≤ ·)) (by grind)];
    exact List.sortedLE_insertionSort (l := BS.subfmls.toList.map (·.complexity));
  haveI hsub : S.1.1 ∪ S.1.2 ⊆ BS.subfmls := subfmls_lindenbaum_indexed ‹_› (by
    intro _ hB;
    exact Finset.mem_toList.mp $ List.mem_insertionSort _ |>.mp hB);
  {
    toSequent := S.1,
    unprovable := S.2,
    subset_subfmls := hsub,
    saturated := {
      impL := by
        intro A B h;
        apply (saturated_lindenbaum_indexed hΓsorted).1 ?_ h;
        apply List.mem_insertionSort _ |>.mpr;
        exact Finset.mem_toList.mpr $ hsub $ Finset.mem_union.mpr $ Or.inl h;
      impR := by
        intro A B h;
        apply (saturated_lindenbaum_indexed hΓsorted).2 ?_ h;
        apply List.mem_insertionSort _ |>.mpr;
        exact Finset.mem_toList.mpr $ hsub $ Finset.mem_union.mpr $ Or.inr h;
    },
  }

lemma subset_lindenbaum {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[D] (S₀.ant ⟹[2] S₀.suc)}
    {S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls} : S₀ ⊆ (lindenbaum BS S₀ S₀_unprovable S₀sub).1 :=
  subset_lindenbaum_indexed

end ExpandedLayeredSequent


namespace ProvableGentzen.Kripke

open _root_.LogicGL.ProvableGentzen.Kripke

variable {BS : Sequent α} [Fact (⊬ᵍ[GL] BS)]

/--
  The countermodel for the level-`2` completeness argument, restricted to the limit ordinal
  ω: the cone of `t` in the finite `GL`-countermodel
  `LogicGL.ProvableGentzen.Kripke.countermodelOf BS`, extended by a constant ω-chain sharing
  the valuation of the cone's root.

  - [KKIM25, Theorem 5.8]
-/
noncomputable def bottomModel (BS : Sequent α) [Fact (⊬ᵍ[GL] BS)] (t : ExpandedSequent BS) (o : α → Prop) :
    RootedModel (((countermodelOf BS)↾t) ⊕ ℕ∞) α :=
  (((countermodelOf BS).toRootedModel t).toModel).toPseudoTail
    ((countermodelOf BS).toRootedModel t).root.1 o

namespace bottomModel

variable {t : ExpandedSequent BS} {o : α → Prop} {A : Formula α}

/--
  Forcing at an embedded cone point of `bottomModel` agrees with forcing in the original
  `GL`-countermodel.

  - [KKIM25, Theorem 5.8]
-/
lemma forces_embed_iff {x : (countermodelOf BS)↾t} :
    toPseudoTail.embed x ⊩[(bottomModel BS t o).toModel] A ↔ x.1 ⊩[countermodelOf BS] A :=
  toPseudoTail.forces_inl.trans Model.toRootedModel.forces_same_at_cone_point

/--
  Truth lemma for the chain part of `bottomModel`: provided the antecedent of `t` is
  `boxL`-closed, every formula in the antecedent of `t` is forced at every chain world, and
  every formula in the succedent is not forced there.

  - [KKIM25, Theorem 5.8]
-/
lemma truthlemma_chainPoint (hbox : ∀ {A : Formula α}, □A ∈ t.1.1 → A ∈ t.1.1) {n : ℕ} {A : Formula α} :
    (A ∈ t.1.1 → toPseudoTail.chainPoint (n : ℕ∞) ⊩[(bottomModel BS t o).toModel] A) ∧
    (A ∈ t.1.2 → toPseudoTail.chainPoint (n : ℕ∞) ⊮[(bottomModel BS t o).toModel] A) := by
  induction A generalizing n with
  | atom a =>
    constructor
    · intro h
      show (if ((n : ℕ∞) = (⊤ : ℕ∞)) then o a else _)
      rw [if_neg (by simp)]
      exact h
    · intro h hf
      revert hf
      show (if ((n : ℕ∞) = (⊤ : ℕ∞)) then o a else _) → False
      rw [if_neg (by simp)]
      exact fun hf => ExpandedSequent.not_mem_both ⟨hf, h⟩
  | bot =>
    constructor
    · intro h; exact absurd h ExpandedSequent.not_mem_bot_ant
    · intro _ hf; exact hf
  | imp A B ihA ihB =>
    constructor
    · intro h hsA
      rcases t.saturated.impL h with hA | hB
      · exact absurd hsA ((ihA (n := n)).2 hA)
      · exact (ihB (n := n)).1 hB
    · intro h hf
      obtain ⟨hA, hB⟩ := t.saturated.impR h
      exact ((ihB (n := n)).2 hB) (hf ((ihA (n := n)).1 hA))
  | box A ih =>
    constructor
    · intro h
      rintro (y | m) Rny
      · rcases y.2 with hy | Rty
        · exact forces_embed_iff.mpr (by rw [hy]; exact truthlemma_ant (hbox h))
        · exact forces_embed_iff.mpr (truthlemma_ant (Rty.2 (FormulaFinset.iff_mem_prebox_mem.mpr h)))
      · have hm : m < (n : ℕ∞) := toPseudoTail.rel_chainPoint_chainPoint.mp Rny
        obtain ⟨m₀, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hm)
        exact (ih (n := m₀)).1 (hbox h)
    · intro h hf
      obtain ⟨y, Rty, hy⟩ := Model.World.not_forces_box.mp (truthlemma_suc (x := t) h)
      exact (forces_embed_iff.not.mpr hy)
        (hf (toPseudoTail.embed ⟨y, Or.inr Rty⟩) toPseudoTail.rel_chainPoint_embed)

/--
  Truth lemma for the root of `bottomModel BS t (#· ∈ U.1.1)`, at every level-`2` saturated
  sequent `U` whose boxed formulas trace back to `t`: every formula of the antecedent of `U`
  is forced at the root, and every formula of the succedent is not forced there.

  - [KKIM25, Theorem 5.8]
-/
lemma truthlemma_root (U : ExpandedLayeredSequent BS)
    (hbox : ∀ {A : Formula α}, □A ∈ t.1.1 → A ∈ t.1.1)
    (hant : ∀ {C : Formula α}, □C ∈ U.1.1 → □C ∈ t.1.1)
    (hsuc : ∀ {C : Formula α}, □C ∈ U.1.2 → □C ∈ t.1.2) {A : Formula α} :
    (A ∈ U.1.1 →
      (bottomModel BS t (#· ∈ U.1.1)).root.1 ⊩[(bottomModel BS t (#· ∈ U.1.1)).toModel] A) ∧
    (A ∈ U.1.2 →
      (bottomModel BS t (#· ∈ U.1.1)).root.1 ⊮[(bottomModel BS t (#· ∈ U.1.1)).toModel] A) := by
  induction A with
  | atom a =>
    constructor
    · intro h
      simp only [Model.World.Forces, bottomModel, toPseudoTail, toFreeTail]
      exact h
    · intro h hf
      simp only [Model.World.Forces, bottomModel, toPseudoTail, toFreeTail] at hf
      exact ExpandedLayeredSequent.not_mem_both ⟨hf, h⟩
  | bot =>
    constructor
    · intro h; exact absurd h ExpandedLayeredSequent.not_mem_bot_ant
    · intro _ hf; exact hf
  | imp A B ihA ihB =>
    constructor
    · intro h hsA
      rcases U.saturated.impL h with hA | hB
      · exact absurd hsA (ihA.2 hA)
      · exact ihB.1 hB
    · intro h hf
      obtain ⟨hA, hB⟩ := U.saturated.impR h
      exact (ihB.2 hB) (hf (ihA.1 hA))
  | box C _ =>
    constructor
    · intro h
      rintro (y | m) Rny
      · rcases y.2 with hy | Rty
        · exact forces_embed_iff.mpr (by rw [hy]; exact truthlemma_ant (hbox (hant h)))
        · exact forces_embed_iff.mpr (truthlemma_ant (Rty.2 (FormulaFinset.iff_mem_prebox_mem.mpr (hant h))))
      · have hm : m < (⊤ : ℕ∞) := toPseudoTail.rel_chainPoint_chainPoint.mp Rny
        obtain ⟨m₀, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hm)
        exact (truthlemma_chainPoint hbox (n := m₀)).1 (hbox (hant h))
    · intro h hf
      obtain ⟨y, Rty, hy⟩ := Model.World.not_forces_box.mp (truthlemma_suc (hsuc h))
      exact (forces_embed_iff.not.mpr hy)
        (hf (toPseudoTail.embed ⟨y, Or.inr Rty⟩) toPseudoTail.rel_chainPoint_embed)

end bottomModel

/--
  Cut-free completeness of `LogicD.ProofGentzen` for level-`2` sequents, restricted to
  constant ω-extensions of finite `GL`-models.

  - [KKIM25, Theorem 5.8]
-/
theorem completeness_finite {Γ Δ : FormulaFinset α}
    (h :
      ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] →
      ∀ (tail : M.World) (o : α → Prop), (M.toPseudoTail tail o).root.1 ⊩[_] (Γ ⟹ Δ)
    ) :
    ⊢ᵍ[D] (Γ ⟹[2] Δ) := by
  by_contra hp;
  haveI : Fact (⊬ᵍ[GL] (Γ ⟹ Δ)) := ⟨not_provable_GL_of_not_provable_2 hp⟩;
  have hsub : (Γ ⟹ Δ).1 ∪ (Γ ⟹ Δ).2 ⊆ (Γ ⟹ Δ).subfmls := by grind;
  let U : ExpandedLayeredSequent (Γ ⟹ Δ) := ExpandedLayeredSequent.lindenbaum (Γ ⟹ Δ) (Γ ⟹ Δ) hp hsub;
  have hsubU : (Γ ⟹ Δ) ⊆ U.toSequent :=
    ExpandedLayeredSequent.subset_lindenbaum (S₀_unprovable := hp) (S₀sub := hsub);
  have hS₀ : ¬ LogicS.ProvableGentzen ((□(U.1.1.prebox)) ⟹[1] (□(U.1.2.prebox))) :=
    not_provable_S_box_prebox_of_not_provable_2 U.unprovable;
  have hsubS₀ : (□(U.1.1.prebox)) ∪ (□(U.1.2.prebox)) ⊆ (Γ ⟹ Δ).subfmls :=
    Finset.union_subset
      (FormulaFinset.box_prebox_subset.trans (Finset.subset_union_left.trans U.subset_subfmls))
      (FormulaFinset.box_prebox_subset.trans (Finset.subset_union_right.trans U.subset_subfmls));
  let T : LogicS.ExpandedLayeredSequent (Γ ⟹ Δ) :=
    LogicS.ExpandedLayeredSequent.lindenbaum (Γ ⟹ Δ) ((□(U.1.1.prebox)) ⟹ (□(U.1.2.prebox))) hS₀ hsubS₀;
  let t : ExpandedSequent (Γ ⟹ Δ) := T.toExpandedSequent;
  have hsubT : ((□(U.1.1.prebox)) ⟹ (□(U.1.2.prebox))) ⊆ T.toSequent :=
    LogicS.ExpandedLayeredSequent.subset_lindenbaum (S₀_unprovable := hS₀) (S₀sub := hsubS₀);
  have hant : ∀ {C : Formula α}, □C ∈ U.1.1 → □C ∈ t.1.1 := fun hC =>
    hsubT.1 (Finset.mem_image_of_mem Formula.box (FormulaFinset.iff_mem_prebox_mem.mpr hC));
  have hsuc : ∀ {C : Formula α}, □C ∈ U.1.2 → □C ∈ t.1.2 := fun hC =>
    hsubT.2 (Finset.mem_image_of_mem Formula.box (FormulaFinset.iff_mem_prebox_mem.mpr hC));
  have hle := h ((countermodelOf (Γ ⟹ Δ)).toRootedModel t).toModel
    ((countermodelOf (Γ ⟹ Δ)).toRootedModel t).root.1 (#· ∈ U.1.1);
  obtain ⟨D, hD, hfD⟩ :=
    hle (fun C hC => (bottomModel.truthlemma_root U T.boxL_closed hant hsuc).1 (hsubU.1 hC));
  exact (bottomModel.truthlemma_root U T.boxL_closed hant hsuc).2 (hsubU.2 hD) hfD;

/--
  Cut-free completeness of `LogicD.ProofGentzen` for level-`2` sequents, restricted to
  constant ω-extensions of `GL`-models.

  - [KKIM25, Theorem 5.8]
-/
theorem completeness {Γ Δ : FormulaFinset α}
    (h :
      ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∀ (tail : M.World) (o : α → Prop), (M.toPseudoTail tail o).root.1 ⊩[_] (Γ ⟹ Δ)
    ) :
    ⊢ᵍ[D] (Γ ⟹[2] Δ) :=
  completeness_finite (fun M _ tail o => h M tail o)

end ProvableGentzen.Kripke

/--
  The four equivalent characterizations of `Γ ⟹ Δ` being a theorem of the level-`2` sequent
  calculus for `D`, restricted to the limit ordinal ω.

  - [KKIM25, Theorem 5.8]
-/
theorem sequent_TFAE {Γ Δ : FormulaFinset α} : [
    -- condition 1
    ⊢ᵍᶜ[D] (Γ ⟹[2] Δ),
    -- condition 2
    ⊢ᵍ[D] (Γ ⟹[2] Δ),
    -- condition 3
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∀ (tail : M.World) (o : α → Prop), (M.toPseudoTail tail o).root.1 ⊩[_] (Γ ⟹ Δ),
    -- condition 4
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∀ (V : ℕ∞ → α → Prop), (M.toFreeTail V).root.1 ⊩[_] (Γ ⟹ Δ)
  ].TFAE := by
  tfae_have 2 → 1 := GentzenWithCutProvable.of_without_cut;
  tfae_have 1 → 4 := GentzenWithCutProvable.soundness;
  tfae_have 4 → 3 := by intro h κ _ M _ tail o; exact h M _;
  tfae_have 3 → 2 := Kripke.completeness;
  tfae_finish;

namespace ProvableGentzen

theorem of_with_cut {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[D] (Γ ⟹[2] Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) :=
  (sequent_TFAE.out 0 1).mp h

end ProvableGentzen

alias GentzenWithCutProvable.cut_elimination := ProvableGentzen.of_with_cut

end LogicD

end
