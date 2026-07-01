module

public import SeqPL.Kripke.Gentzen
public import SeqPL.Kripke.Preservation
public import SeqPL.Kripke.RootExtension
public import Mathlib.Data.ENat.Basic

@[expose]
public section

variable [Nonempty κ] {M : Model κ α} {n : ℕ+} {A B : Formula α} {Γ Γ' Δ Δ' : FormulaFinset α}

namespace Model

abbrev toTail (M : Model κ α) (r : M.World) : RootedModel (κ ⊕ ℕ∞) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a :=
    match x with
    | .inl x => M.Val x a
    | .inr _ => M.Val r a
  root := ⟨.inr ⊤, by
    intro x hx;
    match x with
    | .inl x => simp [Model.Rel];
    | .inr i =>
      simp only [Model.Rel];
      exact lt_top_iff_ne_top.mpr (by simpa using hx);
  ⟩

namespace toTail

variable {r : M.World}

@[simp] lemma root_eq : (M.toTail r).root.1 = .inr ⊤ := rfl

@[simp]
lemma rel_inl_inl {x y : M.World} : (M.toTail r).Rel (.inl x) (.inl y) ↔ x ≺ y := by
  simp [Model.Rel];

@[simp]
lemma not_rel_inl_inr {x : M.World} {i : ℕ∞} : ¬(M.toTail r).Rel (.inl x) (.inr i) := by
  simp [Model.Rel];

@[simp]
lemma rel_inr_inl {i : ℕ∞} {x : M.World} : (M.toTail r).Rel (.inr i) (.inl x) := by
  simp [Model.Rel];

@[simp]
lemma rel_inr_inr {i j : ℕ∞} : (M.toTail r).Rel (.inr i) (.inr j) ↔ j < i := by
  simp [Model.Rel];

instance [IsTrans _ M.Rel] : IsTrans _ (M.toTail r).Rel := by
  constructor;
  intro x y z Rxy Ryz;
  match x, y, z with
  | .inl x, .inl y, .inl z =>
    simp_all only [Model.Rel];
    exact IsTrans.trans _ _ _ Rxy Ryz;
  | .inr a, .inr b, .inr c =>
    simp_all only [Model.Rel];
    exact lt_trans Ryz Rxy;
  | _, .inl _, .inr _
  | .inl _, .inr _, _
  | .inr _, _, .inl _ =>
    simp_all only [Model.Rel];

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.toTail r).Rel := by
  constructor;
  intro x;
  match x with
  | .inl x => simp_all only [Model.Rel]; apply Std.Irrefl.irrefl
  | .inr i => simp [Model.Rel];

protected abbrev tail (M : Model κ α) (r : M.World) : ℕ+ → (M.toTail r).World := λ n => .inr (n : ℕ∞)

@[simp]
lemma tail_isChain (h : i < j) : ((toTail.tail M r) j ≺ (toTail.tail M r) i) := by
  simp only [Model.Rel];
  exact_mod_cast h;

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ (M.toTail r).Rel := ⟨by
  apply ConverseWellFounded.iff_has_max.mpr;
  intro s hs;
  by_cases hs₁ : {x | Sum.inl x ∈ s}.Nonempty;
  . obtain ⟨m, hm₁, hm₂⟩ := ConverseWellFounded.has_max (IsConverseWellFounded.cwf (r := M.Rel)) _ hs₁;
    refine ⟨.inl m, hm₁, ?_⟩;
    rintro (y | j) hy;
    . exact hm₂ y hy;
    . exact not_rel_inl_inr;
  . have hs₂ : {i : ℕ∞ | Sum.inr i ∈ s}.Nonempty := by
      obtain ⟨x, hx⟩ := hs;
      match x with
      | .inl x => exact absurd ⟨x, hx⟩ hs₁;
      | .inr i => exact ⟨i, hx⟩;
    obtain ⟨m, hm₁, hm₂⟩ := (wellFounded_lt (α := ℕ∞)).has_min _ hs₂;
    refine ⟨.inr m, hm₁, ?_⟩;
    rintro (y | j) hy;
    . exact absurd ⟨y, hy⟩ hs₁;
    . exact fun h => hm₂ j hy (rel_inr_inr.mp h);
⟩

instance [M.IsGL] : (M.toTail r).IsGL where

open Model.World (Forces)

/-- 元のモデルから tail model への埋め込みは p-morphism である． -/
def pMorphismOriginal (M : Model κ α) (r : M.World) : M →ₚ (M.toTail r).toModel where
  toFun := .inl
  forth := rel_inl_inl.mpr
  back := by
    rintro w (v | i) h;
    . exact ⟨v, rfl, rel_inl_inl.mp h⟩;
    . exact absurd h not_rel_inl_inr;
  atomic := Iff.rfl

lemma modal_equivalent_original {x : M.World} :
    Model.World.ModalEquivalent (M₁ := M) (M₂ := (M.toTail r).toModel) x (.inl x) :=
  (pMorphismOriginal M r).modal_equivalence x

/-- 元のモデルの世界（`.inl x`）では tail model と元のモデルの forces が一致する． -/
lemma forces_inl {x : M.World} : Forces (M := (M.toTail r).toModel) (.inl x) A ↔ x ⊩ A :=
  modal_equivalent_original.symm

/-- 鎖上では `□A` の forcing は下方閉：`.inr n` で成立するなら，それ以下の `.inr m` でも成立する． -/
lemma forces_nat_box_antitone {m n : ℕ} (hmn : m ≤ n)
  (h : Forces (M := (M.toTail r).toModel) (.inr (n : ℕ∞)) (□A)) :
  Forces (M := (M.toTail r).toModel) (.inr (m : ℕ∞)) (□A) := by
  rintro (x | j) Rmy;
  . exact h (.inl x) rel_inr_inl;
  . apply h (.inr j);
    apply rel_inr_inr.mpr;
    exact lt_of_lt_of_le (rel_inr_inr.mp Rmy) (by exact_mod_cast hmn);

/-- 鎖上（`.inr n`）での forcing は `n` について最終的に安定する． -/
lemma forces_nat_eventually_stable (A : Formula α) :
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
    (Forces (M := (M.toTail r).toModel) (.inr (n : ℕ∞)) A ↔
     Forces (M := (M.toTail r).toModel) (.inr (k : ℕ∞)) A) := by
  induction A with
  | atom a => exact ⟨0, fun n _ => Iff.rfl⟩;
  | bot => exact ⟨0, fun n _ => Iff.rfl⟩;
  | imp A B ihA ihB =>
    obtain ⟨k₁, h₁⟩ := ihA;
    obtain ⟨k₂, h₂⟩ := ihB;
    refine ⟨max k₁ k₂, fun n hn => ?_⟩;
    have hA := (h₁ n (le_trans (le_max_left _ _) hn)).trans (h₁ (max k₁ k₂) (le_max_left _ _)).symm;
    have hB := (h₂ n (le_trans (le_max_right _ _) hn)).trans (h₂ (max k₁ k₂) (le_max_right _ _)).symm;
    constructor;
    . intro h ha; exact hB.mp (h (hA.mpr ha));
    . intro h ha; exact hB.mpr (h (hA.mp ha));
  | box A _ =>
    by_cases hf : ∀ n : ℕ, Forces (M := (M.toTail r).toModel) (.inr (n : ℕ∞)) (□A);
    . exact ⟨0, fun n _ => iff_of_true (hf n) (hf 0)⟩;
    . push Not at hf;
      obtain ⟨m, hm⟩ := hf;
      exact ⟨m, fun n hn => iff_of_false (fun h => hm (forces_nat_box_antitone hn h)) hm⟩;

/--
  部分論理式について閉じた集合 `Γ` の各 `□B ∈ Γ` に対して根で `□B 🡒 B` が成立しているならば，
  `Γ` の各論理式の forces は根と鎖上の各点（`.inr n`）で一致する．
-/
lemma root_forces_iff_forces_nat [DecidableEq α] {M : RootedModel κ α} [IsTrans _ M.Rel]
  {Γ : FormulaFinset α}
  (Γclosed : ∀ B ∈ Γ, B.subfmls ⊆ Γ)
  (hΓ : ∀ B ∈ Γ.prebox, M.root.1 ⊩ (□B 🡒 B)) :
  ∀ B ∈ Γ, ∀ n : ℕ, M.root.1 ⊩ B ↔ Forces (M := (M.toModel.toTail M.root.1).toModel) (.inr (n : ℕ∞)) B := by
  intro B;
  induction B with
  | atom a => intro _ n; exact Iff.rfl;
  | bot => intro _ n; exact Iff.rfl;
  | imp B C ihB ihC =>
    intro hBC n;
    replace ihB := ihB (Γclosed _ hBC (by grind)) n;
    replace ihC := ihC (Γclosed _ hBC (by grind)) n;
    constructor;
    . intro h hB; exact ihC.mp $ h $ ihB.mpr hB;
    . intro h hB; exact ihC.mpr $ h $ ihB.mp hB;
  | box B ihB =>
    intro hB n;
    have hBΓ : B ∈ Γ := Γclosed _ hB (by grind);
    constructor;
    . rintro h (x | j) Rny;
      . apply forces_inl.mpr;
        by_cases hx : x = M.root.1;
        . exact hx ▸ hΓ B (by grind) h;
        . exact h x (M.root.2 x hx);
      . have hj : j < (n : ℕ∞) := rel_inr_inr.mp Rny;
        obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hj);
        exact (ihB hBΓ m).mp $ hΓ B (by grind) h;
    . intro h x Rrx;
      exact forces_inl.mp $ h (.inl x) rel_inr_inl;

end toTail

end Model

end
