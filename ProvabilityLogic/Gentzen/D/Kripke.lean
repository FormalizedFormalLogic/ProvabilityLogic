module

public import ProvabilityLogic.Gentzen.D.WithCut
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

  Folklore; a routine bridge used for the `liftUp₁₂` case of
  `LogicD.GentzenWithCutProvable.soundness_aux`.
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
    (M.toFreeTail V).root.1 ⊩ S.toSequent := by
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
        Model.World.Forces (M := (M.toFreeTail V).toModel) (toFreeTail.chainPoint (n : ℕ∞)) C := by
      intro n C hC;
      obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC;
      exact toFreeTail.forces_box_of_root_forces_box (hΓ _ hC);
    obtain ⟨D, hD, hfreq⟩ :=
      exists_mem_forall_exists_ge (Γ' := □Δ)
        (P := fun D j => Model.World.Forces (M := (M.toFreeTail V).toModel) (toFreeTail.chainPoint (j : ℕ∞)) D)
        (i := i) (fun j hj => hi j hj (hΓ' j));
    obtain ⟨D₀, hD₀, rfl⟩ := Finset.mem_image.mp hD;
    exact ⟨□D₀, Finset.mem_image.mpr ⟨D₀, hD₀, rfl⟩,
      toFreeTail.root_forces_box_of_frequently_chainPoint_forces hfreq⟩;
  | cut h₁ h₂ ih₁ ih₂ =>
    intro hl κ _ M _ V;
    exact Model.World.forces_sequent_cut (ih₁ hl M V) (ih₂ hl M V);

/--
  Soundness of `LogicD.GentzenWithCutProof` for level-`2` sequents `Γ ⟹[2] Δ`, against the
  class of free ω-extensions of `GL`-models — condition `1 ⇒ 4` of `LogicD.semantical_TFAE`.

  - [KKIM25, Theorem 5.8]
-/
theorem soundness {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[D] (Γ ⟹[2] Δ)) :
    ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (V : ℕ∞ → α → Prop),
    (M.toFreeTail V).root.1 ⊩ (Γ ⟹ Δ) :=
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
  `□(Γ.prebox) ⟹ □(Δ.prebox)` is `LogicS.ProvableGentzen`-unprovable at level `1`. The
  contrapositive is the `(GLtoD)` step of the source's completeness argument, routed through
  `LogicS.ProofGentzen` rather than an auxiliary `GL`-sequent.

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
  `LogicD.ProvableGentzen`-unprovable. Unlike `LogicS.ExpandedLayeredSequent`, there is no
  `boxL`-closure condition, since `LogicD.ProofGentzen` has no level-`2` `boxL` rule.

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
  `impL` and `impR` while preserving level-`2` unprovability. Unlike
  `LogicS.ExpandedLayeredSequent.lindenbaum_indexed`, boxed formulas are left untouched, since
  `LogicD.ProofGentzen` has no level-`2` `boxL` rule.

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
    {S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls} : S₀ ⊆ (lindenbaum BS S₀ S₀_unprovable S₀sub).1 := by
  sorry

end ExpandedLayeredSequent


namespace ProvableGentzen.Kripke

open _root_.LogicGL.ProvableGentzen.Kripke

variable {BS : Sequent α} [Fact (⊬ᵍ[GL] BS)]

/--
  The countermodel for the level-`2` completeness argument, restricted to the limit ordinal
  ω: the cone of `t` in the finite `GL`-countermodel
  `LogicGL.ProvableGentzen.Kripke.countermodelOf BS`, extended by a constant ω-chain sharing
  the valuation of the cone's root.

  Restricting to the cone of `t` (rather than the whole countermodel) is necessary because a
  `Model.toPseudoTail` chain point sees the entire base model: without the restriction, chain
  points would see worlds outside the cone of `t`, breaking the box case of the truth lemma.

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
    Model.World.Forces (M := (bottomModel BS t o).toModel) (toPseudoTail.embed x) A ↔
    Model.World.Forces (M := countermodelOf BS) x.1 A := by
  sorry

/--
  Truth lemma for the chain part of `bottomModel`: provided the antecedent of `t` is
  `boxL`-closed, every formula in the antecedent of `t` is forced at every chain world, and
  every formula in the succedent is not forced there.

  - [KKIM25, Theorem 5.8]
-/
lemma truthlemma_chainPoint (hbox : ∀ {A : Formula α}, □A ∈ t.1.1 → A ∈ t.1.1) {n : ℕ} {A : Formula α} :
    (A ∈ t.1.1 → Model.World.Forces (M := (bottomModel BS t o).toModel) (toPseudoTail.chainPoint (n : ℕ∞)) A) ∧
    (A ∈ t.1.2 → ¬ Model.World.Forces (M := (bottomModel BS t o).toModel) (toPseudoTail.chainPoint (n : ℕ∞)) A) := by
  sorry

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
      Model.World.Forces (M := (bottomModel BS t (#· ∈ U.1.1)).toModel) (bottomModel BS t (#· ∈ U.1.1)).root.1 A) ∧
    (A ∈ U.1.2 →
      ¬ Model.World.Forces (M := (bottomModel BS t (#· ∈ U.1.1)).toModel) (bottomModel BS t (#· ∈ U.1.1)).root.1 A) := by
  sorry

end bottomModel

/--
  Cut-free completeness of `LogicD.ProofGentzen` for level-`2` sequents, restricted to
  constant ω-extensions of `GL`-models — condition `3 ⇒ 2` of `LogicD.semantical_TFAE`.

  - [KKIM25, Theorem 5.8]
-/
theorem completeness {Γ Δ : FormulaFinset α}
    (h :
      ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∀ (tail : M.World) (o : α → Prop), (M.toPseudoTail tail o).root.1 ⊩ (Γ ⟹ Δ)
    ) :
    ⊢ᵍ[D] (Γ ⟹[2] Δ) := by
  sorry

end ProvableGentzen.Kripke

/--
  The four equivalent characterizations of `Γ ⟹ Δ` being a theorem of the level-`2` sequent
  calculus for `D`, restricted to the limit ordinal ω: `LogicD.GentzenWithCutProof`- and
  cut-free `LogicD.ProofGentzen`-provability (conditions `1`-`2`), and validity at the root of
  every constant, respectively free, ω-extension of every `GL`-model (conditions `3`-`4`).

  - [KKIM25, Theorem 5.8]
-/
theorem semantical_TFAE {Γ Δ : FormulaFinset α} : [
    -- condition 1
    ⊢ᵍᶜ[D] (Γ ⟹[2] Δ),
    -- condition 2
    ⊢ᵍ[D] (Γ ⟹[2] Δ),
    -- condition 3
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∀ (tail : M.World) (o : α → Prop), (M.toPseudoTail tail o).root.1 ⊩ (Γ ⟹ Δ),
    -- condition 4
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∀ (V : ℕ∞ → α → Prop), (M.toFreeTail V).root.1 ⊩ (Γ ⟹ Δ)
  ].TFAE := by
  sorry

namespace GentzenWithCutProvable

/--
  Cut-elimination corollary of `semantical_TFAE`: condition `1` (`⊢ᵍᶜ[D]`) and condition `2`
  (`⊢ᵍ[D]`) are equivalent, so a `LogicD.GentzenWithCutProof`-proof of a level-`2` sequent
  yields a cut-free `LogicD.ProofGentzen`-proof of the same sequent.

  Original to this formalization: a direct corollary of `semantical_TFAE`, not stated
  separately in the source.
-/
theorem cutElimination {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[D] (Γ ⟹[2] Δ)) : ⊢ᵍ[D] (Γ ⟹[2] Δ) := by
  sorry

end GentzenWithCutProvable

end LogicD

end
