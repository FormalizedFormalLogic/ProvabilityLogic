module

public import SeqPL.Gentzen.S.Basic
public import SeqPL.Gentzen.Kripke
public import Mathlib.Tactic.TFAE

@[expose]
public section

universe u v

variable {α : Type u} [DecidableEq α]

namespace Model.World

variable {κ : Type v} [Nonempty κ] {M : Model κ α}

/--
  A world `x` is `X`-reflexive (KK23, "`Σ`-reflexive") if `□A → A` is forced at `x` for every
  `□A ∈ X`.
-/
def IsReflexiveOf (X : FormulaFinset α) (x : M.World) : Prop :=
  ∀ {A}, □A ∈ X → x ⊩ (□A 🡒 A)

omit [DecidableEq α] in
/-- `IsReflexiveOf` is antitone in `X`: reflexivity for a larger set implies reflexivity for
any of its subsets. -/
lemma IsReflexiveOf.anti {X X' : FormulaFinset α} {x : M.World}
  (hx : x.IsReflexiveOf X') (hXX' : X ⊆ X') : x.IsReflexiveOf X :=
  fun hA => hx (hXX' hA)

end Model.World

variable {κ : Type v} [Nonempty κ] {M : Model κ α}

/-- The `Subtype` of worlds of `M` that are `X`-reflexive. -/
abbrev Model.ReflexiveWorldOf (M : Model κ α) (X : FormulaFinset α) := {x : M.World // x.IsReflexiveOf X}

namespace Model.ReflexiveWorldOf

variable {X : FormulaFinset α}

instance : CoeOut (M.ReflexiveWorldOf X) M.World := ⟨Subtype.val⟩

end Model.ReflexiveWorldOf

variable {κ : Type v} [Nonempty κ] {M : Model κ α} [M.IsGL] {w : ℕ → M.World}

omit [DecidableEq α] in
/--
  Along a strictly descending sequence of worlds `w`, an earlier index is reachable (via `≺`)
  from any later index.
-/
lemma Model.rel_of_descending_lt (hw : ∀ n, w (n + 1) ≺ w n) {n j : ℕ} (hnj : n < j) : w j ≺ w n := by
  have hnj' : n + 1 ≤ j := Nat.succ_le_of_lt hnj;
  clear hnj;
  induction j, hnj' using Nat.le_induction with
  | base => exact hw n;
  | succ j _ ih => exact _root_.trans (hw j) ih;

omit [DecidableEq α] in
/--
  KK23 Theorem 3.1, `2 ⇒ 3` (Lemma 3.2, first half): along a strictly descending sequence of
  worlds, `□A → A` is eventually forced.
-/
lemma Model.eventually_forces_boxImp_of_descending (hw : ∀ n, w (n + 1) ≺ w n) (A : Formula α) :
  ∃ i, ∀ j ≥ i, w j ⊩ (□A 🡒 A) := by
  by_cases h : ∀ n, w n ⊩ A;
  · exact ⟨0, fun j _ => by rw [Model.World.forces_imp]; right; exact h j⟩;
  · push Not at h;
    obtain ⟨n, hn⟩ := h;
    use n + 1;
    intro j hj;
    rw [Model.World.forces_imp];
    left;
    by_contra hcon;
    have hjn : w j ≺ w n := Model.rel_of_descending_lt hw (n := n) (j := j) (by omega);
    have : w n ⊩ A := (Model.World.forces_box).mp hcon (w n) hjn;
    exact hn this;

/--
  KK23 Theorem 3.1, `2 ⇒ 3` (Lemma 3.2, second half): along a strictly descending sequence of
  worlds, every world is eventually `X`-reflexive for a fixed finite set `X`.
-/
lemma Model.eventually_isReflexive_of_descending (hw : ∀ n, w (n + 1) ≺ w n) (X : FormulaFinset α) :
  ∃ i, ∀ j ≥ i, (w j).IsReflexiveOf X := by
  induction X using Finset.induction with
  | empty => exact ⟨0, fun j _ C hC => by simp at hC⟩
  | insert B X _ ih =>
    obtain ⟨i₁, hi₁⟩ := ih;
    match B with
    | □A =>
      obtain ⟨i₂, hi₂⟩ := Model.eventually_forces_boxImp_of_descending hw A;
      refine ⟨max i₁ i₂, fun j hj C hC => ?_⟩;
      rw [Finset.mem_insert] at hC;
      rcases hC with hC | hC
      · have hCA : C = A := by injection hC;
        subst hCA;
        exact hi₂ j (le_of_max_le_right hj)
      · exact hi₁ j (le_of_max_le_left hj) hC
    | #_ | ⊥ | _ 🡒 _ =>
      refine ⟨i₁, fun j hj C hC => ?_⟩;
      rw [Finset.mem_insert] at hC;
      rcases hC with hC | hC
      · exact absurd hC (by simp)
      · exact hi₁ j hj hC

omit [Nonempty κ] [M.IsGL] in
/--
  KK23 Theorem 3.1, `2 ⇒ 3`: if there is a finite set `X` witnessing forcing at every
  `X`-reflexive world of every `GL`-model, then forcing holds eventually along every infinitely
  descending sequence.
-/
lemma eventually_forces_of_exists_isReflexive_forces {Γ Δ : FormulaFinset α}
  (h :
    ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
    ∃ X : FormulaFinset α, ∀ (x : M.ReflexiveWorldOf X), (x : M.World) ⊩ (Γ ⟹ Δ)
  ) :
  ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (w : ℕ → M.World),
  (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩ (Γ ⟹ Δ) := by
  intro κ _ M _ w hw;
  obtain ⟨X, hX⟩ := h M;
  obtain ⟨i, hi⟩ := Model.eventually_isReflexive_of_descending hw X;
  use i;
  intro j hj;
  exact hX ⟨w j, hi j hj⟩;

namespace LogicS

open ProvableGentzen

/--
  A sequent saturated for the level-`1` fragment of `LogicS.ProofGentzen` (KK23, Lemma 3.3):
  besides the implicational saturation conditions of `Sequent.Saturated`, the antecedent is
  closed under the `boxL` rule, all formulas come from the subformulas of the base sequent
  `BS`, and the associated level-`1` sequent is `LogicS.ProvableGentzen`-unprovable.
-/
structure ExpandedLayeredSequent (BS : Sequent α) extends Sequent α where
  saturated      : toSequent.Saturated
  boxL_closed    : ∀ {A : Formula α}, □A ∈ toSequent.ant → A ∈ toSequent.ant
  subset_subfmls : toSequent.ant ∪ toSequent.suc ⊆ BS.subfmls
  unprovable     : ⊬ᴳ (toSequent.ant ⟹[1] toSequent.suc)

namespace ExpandedLayeredSequent

attribute [grind .] saturated boxL_closed subset_subfmls unprovable

variable {BS : Sequent α}

open Classical in
/--
  One step of the Lindenbaum-style saturation for level-`1` sequents of `LogicS.ProofGentzen`:
  process the given list of formulas, saturating the sequent for `impL`, `impR` and `boxL`
  while preserving level-`1` unprovability.
-/
@[grind]
noncomputable def lindenbaum_indexed (S₀ : Sequent α) (S₀_unprovable : ⊬ᴳ (S₀.ant ⟹[1] S₀.suc)) :
  FormulaList α → { S : Sequent α // ⊬ᴳ (S.ant ⟹[1] S.suc) }
| [] => ⟨S₀, S₀_unprovable⟩
| (A 🡒 B) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed S₀ S₀_unprovable Γ;
  if h : (A 🡒 B) ∈ S.1 then
    if h : ⊬ᴳ ((S.1) ⟹[1] (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
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
| (□A) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed S₀ S₀_unprovable Γ;
  if h : (□A) ∈ S.1 then ⟨
    ((insert A S.1) ⟹ S.2),
    by
      contrapose! hS;
      have := ProvableGentzen.boxL hS;
      rwa [(show insert (□A) S.1 = S.1 by grind)] at this;
  ⟩
  else ⟨S, hS⟩
| _ :: Γ => lindenbaum_indexed S₀ S₀_unprovable Γ

variable {S₀ : Sequent α} {S₀_unprovable : ⊬ᴳ (S₀.ant ⟹[1] S₀.suc)} {Γ : FormulaList α}
         {A B : Formula α}

lemma subset_lindenbaum_indexed : S₀ ⊆ (lindenbaum_indexed S₀ S₀_unprovable Γ).1 := by
  induction Γ with
  | nil =>
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons A Γ ih =>
    match A with
    | #a | ⊥ => exact ih
    | A 🡒 B =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2.trans (Finset.subset_insert _ _)⟩
      · exact ⟨ih.1, ih.2⟩;
    | □A =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2⟩;

lemma subfmls_lindenbaum_indexed (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls) (hΓ : ∀ C ∈ Γ, C ∈ BS.subfmls) :
  (lindenbaum_indexed S₀ S₀_unprovable Γ).1.1 ∪ (lindenbaum_indexed S₀ S₀_unprovable Γ).1.2 ⊆ BS.subfmls := by
  induction Γ with
  | nil => exact S₀sub
  | cons A Γ ih =>
    replace ih := ih (by grind);
    match A with
    | #a | ⊥ => exact ih
    | (A 🡒 B) =>
      dsimp only [lindenbaum_indexed];
      have : (A 🡒 B) ∈ BS.subfmls := hΓ _ (by simp)
      have : A ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind;
      have : B ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind;
      split_ifs;
      all_goals
      . intro;
        grind;
    | □A =>
      dsimp only [lindenbaum_indexed];
      have : (□A) ∈ BS.subfmls := hΓ _ (by simp)
      have : A ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := □A) ‹_› $ by grind;
      split_ifs;
      all_goals
      . intro;
        grind;

/--
  `impL`-saturation part of `saturated_lindenbaum_indexed`: the antecedent of the saturated
  sequent is closed under the `impL` rule for implications from `Γ`.
-/
lemma saturated_impL_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  ∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.1 → A ∈ S.1.2 ∨ B ∈ S.1.1 := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil =>
    intro _ A;
    intros;
    simp_all;
  | cons x Γ' ih =>
    intro hΓ;
    rw [List.pairwise_cons] at hΓ;
    obtain ⟨hhead, htail⟩ := hΓ;
    replace ih : ∀ {A B : Formula α}, A 🡒 B ∈ Γ' →
      A 🡒 B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.1 →
      A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.2 ∨ B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.1 := ih htail;
    match x with
    | #a | ⊥ =>
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      refine ih ?_ hx;
      rcases List.mem_cons.mp hmem with h | h;
      · simp at h;
      · exact h;
    | C 🡒 D =>
      have hunp : ⊬ᴳ ((lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ⟹[1] (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc) :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 h2 h3 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];
    | □C =>
      have hunp : ⊬ᴳ ((lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ⟹[1] (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc) :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];

/--
  `impR`-saturation part of `saturated_lindenbaum_indexed`: the succedent of the saturated
  sequent is closed under the `impR` rule for implications from `Γ`.
-/
lemma saturated_impR_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  ∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.2 → A ∈ S.1.1 ∧ B ∈ S.1.2 := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil =>
    intro _ A;
    intros;
    simp_all;
  | cons x Γ' ih =>
    intro hΓ;
    rw [List.pairwise_cons] at hΓ;
    obtain ⟨hhead, htail⟩ := hΓ;
    replace ih : ∀ {A B : Formula α}, A 🡒 B ∈ Γ' →
      A 🡒 B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.2 →
      A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.1 ∧ B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.2 := ih htail;
    match x with
    | #a | ⊥ =>
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      refine ih ?_ hx;
      rcases List.mem_cons.mp hmem with h | h;
      · simp at h;
      · exact h;
    | C 🡒 D =>
      have hunp : ⊬ᴳ ((lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ⟹[1] (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc) :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 h2 h3 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];
    | □C =>
      have hunp : ⊬ᴳ ((lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ⟹[1] (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc) :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];

/--
  `boxL`-saturation part of `saturated_lindenbaum_indexed`: the antecedent of the saturated
  sequent is closed under the `boxL` rule for boxed formulas from `Γ`.
-/
lemma saturated_boxL_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  ∀ {A : Formula α}, □A ∈ Γ → □A ∈ S.1.1 → A ∈ S.1.1 := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil =>
    intro _ A;
    intros;
    simp_all;
  | cons x Γ' ih =>
    intro hΓ;
    rw [List.pairwise_cons] at hΓ;
    obtain ⟨hhead, htail⟩ := hΓ;
    replace ih : ∀ {A : Formula α}, □A ∈ Γ' →
      □A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.1 →
      A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.1 := ih htail;
    match x with
    | #a | ⊥ =>
      dsimp only [lindenbaum_indexed];
      intro A hmem hx;
      refine ih ?_ hx;
      rcases List.mem_cons.mp hmem with h | h;
      · simp at h;
      · exact h;
    | C 🡒 D =>
      have hunp : ⊬ᴳ ((lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ⟹[1] (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc) :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A hmem hx;
      split_ifs at hx ⊢ with h1 h2 h3 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];
    | □C =>
      have hunp : ⊬ᴳ ((lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ⟹[1] (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc) :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A hmem hx;
      split_ifs at hx ⊢ with h1 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];

/--
  Saturation of the Lindenbaum construction (KK23, Lemma 3.3): the resulting sequent is
  simultaneously `impL`-, `impR`- and `boxL`-saturated for the formulas listed in `Γ`.
-/
lemma saturated_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.1 → A ∈ S.1.2 ∨ B ∈ S.1.1) ∧
  (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.2 → A ∈ S.1.1 ∧ B ∈ S.1.2) ∧
  (∀ {A : Formula α}, □A ∈ Γ → □A ∈ S.1.1 → A ∈ S.1.1) :=
  ⟨saturated_impL_lindenbaum_indexed hΓ,
   saturated_impR_lindenbaum_indexed hΓ,
   saturated_boxL_lindenbaum_indexed hΓ⟩

/--
  Lindenbaum-style saturation for level-`1` sequents of `LogicS.ProofGentzen` (KK23, Lemma 3.3):
  every level-`1` unprovable sequent within the subformulas of `BS` extends to a saturated,
  `boxL`-closed, level-`1` unprovable sequent.
-/
noncomputable def lindenbaum (BS : Sequent α) (S₀ : Sequent α)
  (S₀_unprovable : ⊬ᴳ (S₀.ant ⟹[1] S₀.suc)) (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls) :
  ExpandedLayeredSequent BS :=
  letI Γ := BS.subfmls.toList.insertionSort (·.complexity ≤ ·.complexity);
  letI S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  haveI hΓsorted : (Γ.map (·.complexity)).SortedLE := by
    rw [List.map_insertionSort (f := Formula.complexity) (l := BS.subfmls.toList) (r := λ A B => ((A.complexity) ≤ (B.complexity))) (s := (· ≤ ·)) (by grind)];
    exact List.sortedLE_insertionSort (l := BS.subfmls.toList.map (·.complexity));
  haveI hΓmem : ∀ C ∈ Γ, C ∈ BS.subfmls := by
    intro _ hB;
    exact Finset.mem_toList.mp $ List.mem_insertionSort _ |>.mp hB;
  haveI hsub : S.1.1 ∪ S.1.2 ⊆ BS.subfmls := subfmls_lindenbaum_indexed ‹_› ‹_›;
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
        apply (saturated_lindenbaum_indexed hΓsorted).2.1 ?_ h;
        apply List.mem_insertionSort _ |>.mpr;
        exact Finset.mem_toList.mpr $ hsub $ Finset.mem_union.mpr $ Or.inr h;
    },
    boxL_closed := by
      intro A h;
      apply (saturated_lindenbaum_indexed hΓsorted).2.2 ?_ h;
      apply List.mem_insertionSort _ |>.mpr;
      exact Finset.mem_toList.mpr $ hsub $ Finset.mem_union.mpr $ Or.inl h;
  }

lemma subset_lindenbaum {S₀ : Sequent α} {S₀_unprovable : ⊬ᴳ (S₀.ant ⟹[1] S₀.suc)} {S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls} :
  S₀ ⊆ (lindenbaum BS S₀ S₀_unprovable S₀sub).1 := subset_lindenbaum_indexed

/-- Forgetting the `boxL`-closure: an `ExpandedLayeredSequent` is in particular an `ExpandedSequent`. -/
def toExpandedSequent (T : ExpandedLayeredSequent BS) : ExpandedSequent BS where
  toSequent      := T.toSequent
  saturated      := T.saturated
  subset_subfmls := T.subset_subfmls
  unprovable     := not_provableGentzen_of_not_provable_one T.unprovable

end ExpandedLayeredSequent


section

open _root_.ProvableGentzen.Kripke

variable {BS : Sequent α} [Fact (⊬ᵍ BS)]

instance : Nonempty (ExpandedSequent BS ⊕ ℕ) := ⟨.inr 0⟩

/--
  The countermodel for KK23 Theorem 3.1's cut-free completeness argument: the finite
  countermodel `ProvableGentzen.Kripke.countermodelOf BS` extended by an infinite descending
  chain of copies of the world `t` (each `Sum.inr n` sees every `Sum.inr m` with `m < n`,
  the world `t` itself, and everything `t` sees).
-/
@[grind]
def chainModel (BS : Sequent α) [Fact (⊬ᵍ BS)] (t : ExpandedSequent BS) : Model (ExpandedSequent BS ⊕ ℕ) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => Model.Rel (M := countermodelOf BS) x y
    | .inr _, .inl y => y = t ∨ Model.Rel (M := countermodelOf BS) t y
    | .inr n, .inr m => m < n
    | .inl _, .inr _ => False
  Val' x a :=
    match x with
    | .inl x => (countermodelOf BS).Val x a
    | .inr _ => (countermodelOf BS).Val t a

variable {t : ExpandedSequent BS}

instance : (chainModel BS t).IsGL where
  trans := by
    rintro (x | n) (y | m) (z | k) Rxy Ryz <;> grind;
  cwf := by
    have hInl : ∀ x : ExpandedSequent BS, Acc (flip (chainModel BS t).Rel) (.inl x) := by
      have hwf : WellFounded (flip (Model.Rel (M := countermodelOf BS))) := IsConverseWellFounded.cwf;
      intro x;
      apply hwf.induction (C := λ x => Acc (flip (chainModel BS t).Rel) (.inl x)) x;
      rintro x ih;
      constructor;
      rintro (y | m) Rxy;
      · exact ih y Rxy;
      · exact Rxy.elim;
    have hInr : ∀ n : ℕ, Acc (flip (chainModel BS t).Rel) (.inr n) := by
      intro n;
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        constructor;
        rintro (y | m) Rxy;
        · exact hInl y;
        · exact ih m Rxy;
    constructor;
    rintro (x | n);
    · exact hInl x;
    · exact hInr n;

/--
  Forcing at a world `Sum.inl x` of `chainModel BS t` coincides with forcing at `x` in
  `ProvableGentzen.Kripke.countermodelOf BS`: no world of the copied countermodel sees the chain part.
-/
lemma forces_chainModel_inl {x : ExpandedSequent BS} {A : Formula α} :
  (Model.World.Forces (M := chainModel BS t) (.inl x) A) ↔
  (Model.World.Forces (M := countermodelOf BS) x A) := by
  induction A generalizing x with
  | atom a => exact Iff.rfl;
  | bot => exact Iff.rfl;
  | imp A B ihA ihB =>
    simp only [Model.World.Forces];
    rw [ihA, ihB];
  | box A ih =>
    constructor;
    · intro h y Rxy;
      exact ih.mp (h (.inl y) Rxy);
    · rintro h (y | m) Rxy;
      · exact ih.mpr (h y Rxy);
      · exact Rxy.elim;

/--
  Truth lemma for the chain part of `chainModel BS t` (KK23 Theorem 3.1's cut-free completeness
  argument): provided the antecedent of `t` is `boxL`-closed, every formula in the antecedent of
  `t` is forced at every chain world `Sum.inr n`, and every formula in the succedent is not forced.
-/
lemma truthlemma_inr (hbox : ∀ {A : Formula α}, □A ∈ t.1.1 → A ∈ t.1.1) {n : ℕ} {A : Formula α} :
  (A ∈ t.1.1 → Model.World.Forces (M := chainModel BS t) (.inr n) A) ∧
  (A ∈ t.1.2 → ¬Model.World.Forces (M := chainModel BS t) (.inr n) A) := by
  induction A generalizing n with
  | atom a =>
    constructor;
    · intro h; exact h;
    · intro h hf; exact ExpandedSequent.not_mem_both ⟨hf, h⟩;
  | bot =>
    constructor;
    · intro h; exact absurd h ExpandedSequent.not_mem_bot_ant;
    · intro _ hf; exact hf;
  | imp A B ihA ihB =>
    constructor;
    · intro h hsA;
      rcases t.saturated.impL h with hA | hB;
      · exact absurd hsA ((ihA (n := n)).2 hA);
      · exact (ihB (n := n)).1 hB;
    · intro h hf;
      obtain ⟨hA, hB⟩ := t.saturated.impR h;
      exact ((ihB (n := n)).2 hB) (hf ((ihA (n := n)).1 hA));
  | box A ih =>
    constructor;
    · intro h;
      rintro (y | m) Rny;
      · rcases Rny with rfl | Rty;
        · exact forces_chainModel_inl.mpr (truthlemma_ant (hbox h));
        · exact forces_chainModel_inl.mpr (truthlemma_ant (Rty.2 (FormulaFinset.iff_mem_prebox_mem.mpr h)));
      · exact (ih (n := m)).1 (hbox h);
    · intro h hf;
      obtain ⟨y, Rty, hy⟩ := Model.World.not_forces_box.mp (truthlemma_suc (x := t) h);
      exact (forces_chainModel_inl.not.mpr hy) (hf (.inl y) (Or.inr Rty));

end


namespace ProvableGentzen.Kripke

/--
  Cut-free completeness of `LogicS.ProofGentzen` for level-`1` sequents (KK23 Theorem 3.1,
  condition `4 ⇒ 5`): if `Γ ⟹ Δ` is forced at some point along every infinitely descending
  sequence of every `GL`-model, then `Γ ⟹[1] Δ` is provable in `LogicS.ProofGentzen`.
-/
theorem completeness {Γ Δ : FormulaFinset α}
  (h :
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (w : ℕ → M.World),
    (∀ n, w (n + 1) ≺ w n) → ∃ i, w i ⊩ (Γ ⟹ Δ)
  )
  : ⊢ᴳ (Γ ⟹[1] Δ) := by
  by_contra hp;
  haveI : Fact (⊬ᵍ (Γ ⟹ Δ)) := ⟨not_provableGentzen_of_not_provable_one hp⟩;
  have hsub : (Γ ⟹ Δ).1 ∪ (Γ ⟹ Δ).2 ⊆ (Γ ⟹ Δ).subfmls := by grind;
  let T : ExpandedLayeredSequent (Γ ⟹ Δ) := ExpandedLayeredSequent.lindenbaum (Γ ⟹ Δ) (Γ ⟹ Δ) hp hsub;
  let t : ExpandedSequent (Γ ⟹ Δ) := T.toExpandedSequent;
  have hsubT : (Γ ⟹ Δ) ⊆ T.toSequent := ExpandedLayeredSequent.subset_lindenbaum (S₀_unprovable := hp) (S₀sub := hsub);
  obtain ⟨i, hi⟩ := h (chainModel (Γ ⟹ Δ) t) (λ n => .inr n) (λ n => Nat.lt_succ_self n);
  obtain ⟨D, hD, hfD⟩ := hi (λ C hC => (truthlemma_inr T.boxL_closed).1 (hsubT.1 hC));
  exact (truthlemma_inr T.boxL_closed).2 (hsubT.2 hD) hfD;

end ProvableGentzen.Kripke

namespace GentzenWithCutProvable

variable {Γ Δ : FormulaFinset α}

/--
  KK23 Theorem 3.1, `6 ⇒ 1` (soundness of `LogicS.GentzenWithCutProof`): every
  `LogicS.GentzenWithCutProof`-proof of `S` yields a finite set `X` such that `S` is forced at
  every world `x` of every `GL`-model, provided `x` is `X`-reflexive whenever `S` is a
  level-`1` sequent.
-/
theorem soundness_aux {S : TwoLayeredSequent α} (h : ⊢ᴳᶜ S) :
  ∃ X : FormulaFinset α, ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (x : M.World),
  (S.level = 1 → x.IsReflexiveOf X) → x ⊩ S.toSequent := by
  induction h using LogicS.GentzenWithCutProvable.rec with
  | axm l A =>
    refine ⟨∅, ?_⟩;
    intro κ _ M _ x _;
    exact Model.World.forces_sequent_axm;
  | botL l =>
    refine ⟨∅, ?_⟩;
    intro κ _ M _ x _;
    exact Model.World.forces_sequent_botL;
  | wkL h h' ih =>
    obtain ⟨X, hX⟩ := ih;
    refine ⟨X, ?_⟩;
    intro κ _ M _ x hrefl;
    exact Model.World.forces_sequent_wkL (hX M x hrefl) h';
  | wkR h h' ih =>
    obtain ⟨X, hX⟩ := ih;
    refine ⟨X, ?_⟩;
    intro κ _ M _ x hrefl;
    exact Model.World.forces_sequent_wkR (hX M x hrefl) h';
  | impL h₁ h₂ ih₁ ih₂ =>
    obtain ⟨X₁, hX₁⟩ := ih₁;
    obtain ⟨X₂, hX₂⟩ := ih₂;
    refine ⟨X₁ ∪ X₂, ?_⟩;
    intro κ _ M _ x hrefl;
    exact Model.World.forces_sequent_impL
      (hX₁ M x (fun h => Model.World.IsReflexiveOf.anti (hrefl h) Finset.subset_union_left))
      (hX₂ M x (fun h => Model.World.IsReflexiveOf.anti (hrefl h) Finset.subset_union_right));
  | impR h ih =>
    obtain ⟨X, hX⟩ := ih;
    refine ⟨X, ?_⟩;
    intro κ _ M _ x hrefl;
    exact Model.World.forces_sequent_impR (hX M x hrefl);
  | liftUp h ih =>
    obtain ⟨X, hX⟩ := ih;
    refine ⟨X, ?_⟩;
    intro κ _ M _ x _;
    exact hX M x (fun h => absurd (show (0 : Fin 2) = 1 from h) (by decide));
  | boxGL h ih =>
    rename_i Γ' A';
    obtain ⟨X, hX⟩ := ih;
    refine ⟨X, ?_⟩;
    intro κ _ M _ x _;
    have hM : M ⊧ (insert (□A') (Γ' ∪ Γ'.box) ⟹ {A'}) :=
      fun x' => hX M x' (fun h => absurd (show (0 : Fin 2) = 1 from h) (by decide));
    exact (Model.validate_gentzen_boxGL hM) x;
  | boxL h ih =>
    rename_i Γ' Δ' A';
    obtain ⟨X, hX⟩ := ih;
    refine ⟨insert (□A') X, ?_⟩;
    intro κ _ M _ x hrefl h;
    have hRefl : x.IsReflexiveOf (insert (□A') X) := hrefl rfl;
    have hBoxA : x ⊩ (□A') := h _ (Finset.mem_insert_self _ _);
    have hImp : x ⊩ (□A' 🡒 A') := hRefl (Finset.mem_insert_self _ _);
    have hA : x ⊩ A' := by
      rcases Model.World.forces_imp.mp hImp with h' | h';
      · exact absurd hBoxA h';
      · exact h';
    have hΓ : ∀ C ∈ insert A' Γ', x ⊩ C := by
      intro C hC;
      rcases Finset.mem_insert.mp hC with rfl | hC;
      · exact hA;
      · exact h C (Finset.mem_insert_of_mem hC);
    exact hX M x (fun _ => hRefl.anti (Finset.subset_insert _ _)) hΓ;
  | cut h₁ h₂ ih₁ ih₂ =>
    obtain ⟨X₁, hX₁⟩ := ih₁;
    obtain ⟨X₂, hX₂⟩ := ih₂;
    refine ⟨X₁ ∪ X₂, ?_⟩;
    intro κ _ M _ x hrefl;
    exact Model.World.forces_sequent_cut
      (hX₁ M x (fun h => Model.World.IsReflexiveOf.anti (hrefl h) Finset.subset_union_left))
      (hX₂ M x (fun h => Model.World.IsReflexiveOf.anti (hrefl h) Finset.subset_union_right));

/--
  KK23 Theorem 3.1, `6 ⇒ 1`, stated at the level of `LogicS.GentzenWithCutProvable`: provability
  of a level-`1` sequent `Γ ⟹[1] Δ` yields a finite set `X` witnessing forcing at every
  `X`-reflexive world of every `GL`-model.
-/
theorem soundness (h : ⊢ᴳᶜ (Γ ⟹[1] Δ)) :
  ∃ X : FormulaFinset α, ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
  ∀ (x : M.ReflexiveWorldOf X), (x : M.World) ⊩ (Γ ⟹ Δ) := by
  obtain ⟨X, hX⟩ := soundness_aux h;
  refine ⟨X, ?_⟩;
  intro κ _ M _ x;
  exact hX M (x : M.World) (fun _ => x.2);

end GentzenWithCutProvable

/--
  The six equivalent characterizations of `Γ ⟹ Δ` being a theorem of the sequent calculus
  `LogicS.ProofGentzen` for `S` at level `1` — uniform, model-wise and pointwise finite-set
  reflexivity witnesses on `GL`-models (conditions `1`–`4`), cut-free
  `LogicS.ProofGentzen`-provability (condition `5`), and `LogicS.GentzenWithCutProof`-provability
  (condition `6`).

  - [KK23, Theorem 3.1]
-/
theorem semantical_TFAE {Γ Δ : FormulaFinset α} : [
    -- condition 1
    ∃ X : FormulaFinset α, ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∀ (x : M.ReflexiveWorldOf X), (x : M.World) ⊩ (Γ ⟹ Δ),
    -- condition 2
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
      ∃ X : FormulaFinset α, ∀ (x : M.ReflexiveWorldOf X), (x : M.World) ⊩ (Γ ⟹ Δ),
    -- condition 3
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, ∀ j ≥ i, w j ⊩ (Γ ⟹ Δ),
    -- condition 4
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → ∀ (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ i, w i ⊩ (Γ ⟹ Δ),
    -- condition 5
    ⊢ᴳ (Γ ⟹[1] Δ),
    -- condition 6
    ⊢ᴳᶜ (Γ ⟹[1] Δ)
  ].TFAE := by
  tfae_have 1 → 2 := by
    intro h κ _ M _;
    obtain ⟨X, hX⟩ := h;
    exact ⟨X, hX M⟩;
  tfae_have 2 → 3 := eventually_forces_of_exists_isReflexive_forces;
  tfae_have 3 → 4 := by
    intro h κ _ M _ w hw;
    obtain ⟨i, hi⟩ := h M w hw;
    exact ⟨i, hi i (le_refl i)⟩;
  tfae_have 4 → 5 := ProvableGentzen.Kripke.completeness;
  tfae_have 5 → 6 := GentzenWithCutProvable.of_without_cut;
  tfae_have 6 → 1 := GentzenWithCutProvable.soundness;
  tfae_finish;

namespace GentzenWithCutProvable

/--
  Cut-elimination corollary of `semantical_TFAE`: condition `6` (`⊢ᴳᶜ`) and condition `5`
  (`⊢ᴳ`) of the TFAE are equivalent, so a `LogicS.GentzenWithCutProof`-proof of a level-`1`
  sequent yields a cut-free `LogicS.ProofGentzen`-proof of the same sequent.
-/
theorem cutElimination {Γ Δ : FormulaFinset α} (h : ⊢ᴳᶜ (Γ ⟹[1] Δ)) : ⊢ᴳ (Γ ⟹[1] Δ) :=
  (semantical_TFAE.out 5 4).mp h

end GentzenWithCutProvable

end LogicS

end
