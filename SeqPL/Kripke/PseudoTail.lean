module

public import SeqPL.Kripke.Gentzen
public import SeqPL.Kripke.Preservation
public import SeqPL.Kripke.RootExtension
public import Mathlib.Data.ENat.Basic

@[expose]
public section

variable [Nonempty κ] {M : Model κ α} {A B : Formula α}

namespace Model

/--
  pseudo-tail model（ω 拡大モデル）：ω（`.inr ⊤`）を根とし，その下に無限降下鎖 `.inr n`（`n : ℕ`）を挟んで
  元のモデル `M` の全体を接続する．鎖上（`.inr n`）の付値は `M.Val r`，ω 上の付値は `o` で与える．
-/
abbrev toPseudoTail (M : Model κ α) (r : M.World) (o : α → Prop) : RootedModel (κ ⊕ ℕ∞) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a :=
    match x with
    | .inl x => M.Val x a
    | .inr i => if i = (⊤ : ℕ∞) then o a else M.Val r a
  root := ⟨.inr ⊤, by
    intro x hx;
    match x with
    | .inl x => simp [Model.Rel];
    | .inr i =>
      simp only [Model.Rel];
      exact lt_top_iff_ne_top.mpr (by simpa using hx);
  ⟩

namespace toPseudoTail

variable {r : M.World} {o : α → Prop}

@[simp] lemma root_eq : (M.toPseudoTail r o).root.1 = .inr ⊤ := rfl

@[simp]
lemma rel_inl_inl {x y : M.World} : (M.toPseudoTail r o).Rel (.inl x) (.inl y) ↔ x ≺ y := by
  simp [Model.Rel];

@[simp]
lemma not_rel_inl_inr {x : M.World} {i : ℕ∞} : ¬(M.toPseudoTail r o).Rel (.inl x) (.inr i) := by
  simp [Model.Rel];

@[simp]
lemma rel_inr_inl {i : ℕ∞} {x : M.World} : (M.toPseudoTail r o).Rel (.inr i) (.inl x) := by
  simp [Model.Rel];

@[simp]
lemma rel_inr_inr {i j : ℕ∞} : (M.toPseudoTail r o).Rel (.inr i) (.inr j) ↔ j < i := by
  simp [Model.Rel];

instance [IsTrans _ M.Rel] : IsTrans _ (M.toPseudoTail r o).Rel := ⟨by
  intro x y z Rxy Ryz;
  match x, y, z with
  | .inl x, .inl y, .inl z => exact rel_inl_inl.mpr $ IsTrans.trans _ _ _ (rel_inl_inl.mp Rxy) (rel_inl_inl.mp Ryz);
  | .inr i, .inr j, .inr k => exact rel_inr_inr.mpr $ lt_trans (rel_inr_inr.mp Ryz) (rel_inr_inr.mp Rxy);
  | .inr i, .inr j, .inl z | .inr i, .inl y, .inl z => exact rel_inr_inl;
  | .inl _, .inr _, _ => exact absurd Rxy not_rel_inl_inr;
  | .inl _, .inl _, .inr _ | .inr _, .inl _, .inr _ => exact absurd Ryz not_rel_inl_inr;
⟩

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.toPseudoTail r o).Rel := ⟨by
  intro x;
  match x with
  | .inl x => simp only [Model.Rel]; apply Std.Irrefl.irrefl;
  | .inr i => simp [Model.Rel];
⟩

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ (M.toPseudoTail r o).Rel := ⟨by
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

instance [M.IsGL] : (M.toPseudoTail r o).IsGL where

open Model.World (Forces)

/-- 元のモデルから pseudo-tail model への埋め込みは p-morphism である． -/
def pMorphismOriginal (M : Model κ α) (r : M.World) (o : α → Prop) : M →ₚ (M.toPseudoTail r o).toModel where
  toFun := .inl
  forth := rel_inl_inl.mpr
  back := by
    rintro w (v | i) h;
    . exact ⟨v, rfl, rel_inl_inl.mp h⟩;
    . exact absurd h not_rel_inl_inr;
  atomic := Iff.rfl

lemma modal_equivalent_original {x : M.World} :
    Model.World.ModalEquivalent (M₁ := M) (M₂ := (M.toPseudoTail r o).toModel) x (.inl x) :=
  (pMorphismOriginal M r o).modal_equivalence x

/-- 元のモデルの世界（`.inl x`）では pseudo-tail model と元のモデルの forces が一致する． -/
lemma forces_inl {x : M.World} : Forces (M := (M.toPseudoTail r o).toModel) (.inl x) A ↔ x ⊩ A :=
  modal_equivalent_original.symm

/-- pseudo-tail model の根（ω）で `□A` が成立するならば全ての点で `□A` が成立する． -/
lemma forces_box_of_root_forces_box {x : (M.toPseudoTail r o).World}
  (h : Forces (M := (M.toPseudoTail r o).toModel) (M.toPseudoTail r o).root.1 (□A)) :
  Forces (M := (M.toPseudoTail r o).toModel) x (□A) := by
  intro y Rxy;
  apply h;
  match x, y with
  | _, .inl y => exact rel_inr_inl;
  | .inl x, .inr j => exact absurd Rxy not_rel_inl_inr;
  | .inr i, .inr j => exact rel_inr_inr.mpr $ lt_of_lt_of_le (rel_inr_inr.mp Rxy) le_top;

/--
  部分論理式について閉じた集合 `S` の各 `□B ∈ S` に対して根で `□B 🡒 B` が成立しているならば，
  `S` の各論理式の forces は根と鎖上の各点（`.inr n`）で一致する．
-/
lemma root_forces_iff_forces_nat [DecidableEq α] {M : RootedModel κ α} [IsTrans _ M.Rel]
  {o : α → Prop} {S : FormulaFinset α}
  (Sclosed : ∀ B ∈ S, B.subfmls ⊆ S)
  (hS : ∀ B ∈ S.prebox, M.root.1 ⊩ (□B 🡒 B)) :
  ∀ B ∈ S, ∀ n : ℕ, M.root.1 ⊩ B ↔ Forces (M := (M.toModel.toPseudoTail M.root.1 o).toModel) (.inr (n : ℕ∞)) B := by
  intro B;
  induction B with
  | atom a =>
    intro _ n;
    show M.Val M.root.1 a ↔ if ((n : ℕ∞) = (⊤ : ℕ∞)) then o a else M.Val M.root.1 a;
    rw [if_neg (by simp)];
  | bot => intro _ n; exact Iff.rfl;
  | imp B C ihB ihC =>
    intro hBC n;
    replace ihB := ihB (Sclosed _ hBC (by grind)) n;
    replace ihC := ihC (Sclosed _ hBC (by grind)) n;
    constructor;
    . intro h hB; exact ihC.mp $ h $ ihB.mpr hB;
    . intro h hB; exact ihC.mpr $ h $ ihB.mp hB;
  | box B ihB =>
    intro hB n;
    have hBS : B ∈ S := Sclosed _ hB (by grind);
    constructor;
    . rintro h (x | j) Rny;
      . apply forces_inl.mpr;
        by_cases hx : x = M.root.1;
        . exact hx ▸ hS B (by grind) h;
        . exact h x (M.root.2 x hx);
      . have hj : j < (n : ℕ∞) := rel_inr_inr.mp Rny;
        obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hj);
        exact (ihB hBS m).mp $ hS B (by grind) h;
    . intro h x Rrx;
      exact forces_inl.mp $ h (.inl x) rel_inr_inl;

end toPseudoTail

end Model

end
