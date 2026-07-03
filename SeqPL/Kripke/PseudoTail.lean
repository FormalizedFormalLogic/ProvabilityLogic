module

public import SeqPL.Kripke.Gentzen
public import SeqPL.Kripke.Preservation
public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.RootExtension
public import Mathlib.Data.ENat.Basic

@[expose]
public section

variable [Nonempty κ] {M : Model κ α} {A B : Formula α}

namespace Model

/--
  pseudo-tail model（ω 拡大モデル）：ω（`chainPoint ⊤`）を根とし，その下に無限降下鎖 `chainPoint n`（`n : ℕ`）を
  挟んで元のモデル `M` の全体を接続する．鎖上（`chainPoint n`）の付値は `M.Val tail`，ω 上の付値は `o` で与える．
-/
abbrev toPseudoTail (M : Model κ α) (tail : M.World) (o : α → Prop) : RootedModel (κ ⊕ ℕ∞) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a :=
    match x with
    | .inl x => M.Val x a
    | .inr i => if i = (⊤ : ℕ∞) then o a else M.Val tail a
  root := ⟨.inr ⊤, by
    intro x hx;
    match x with
    | .inl x => simp [Model.Rel];
    | .inr i =>
      simp only [Model.Rel];
      exact lt_top_iff_ne_top.mpr (by simpa using hx);
  ⟩

namespace toPseudoTail

variable {tail : M.World} {o : α → Prop}

/-- The embedding of a world of the original model `M` into the pseudo-tail model
`M.toPseudoTail tail o`. -/
abbrev embed (x : M.World) : (M.toPseudoTail tail o).World := .inl x

/-- The world in the chain attached above `tail`, indexed by `i : ℕ∞` (`⊤` is the
pseudo-tail model's own root, ω). -/
abbrev chainPoint (i : ℕ∞) : (M.toPseudoTail tail o).World := .inr i

@[simp] lemma root_eq : (M.toPseudoTail tail o).root.1 = chainPoint ⊤ := rfl

@[simp]
lemma rel_embed_embed {x y : M.World} :
    (M.toPseudoTail tail o).Rel (embed x) (embed y) ↔ x ≺ y := by
  simp [Model.Rel];

@[simp]
lemma not_rel_embed_chainPoint {x : M.World} {i : ℕ∞} :
    ¬(M.toPseudoTail tail o).Rel (embed x) (chainPoint i) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_embed {i : ℕ∞} {x : M.World} :
    (M.toPseudoTail tail o).Rel (chainPoint i) (embed x) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_chainPoint {i j : ℕ∞} :
    (M.toPseudoTail tail o).Rel (chainPoint i) (chainPoint j) ↔ j < i := by
  simp [Model.Rel];

instance [IsTrans _ M.Rel] : IsTrans _ (M.toPseudoTail tail o).Rel := ⟨by
  intro x y z Rxy Ryz;
  match x, y, z with
  | .inl x, .inl y, .inl z =>
    exact rel_embed_embed.mpr $ IsTrans.trans _ _ _ (rel_embed_embed.mp Rxy) (rel_embed_embed.mp Ryz);
  | .inr i, .inr j, .inr k =>
    exact rel_chainPoint_chainPoint.mpr $ lt_trans (rel_chainPoint_chainPoint.mp Ryz) (rel_chainPoint_chainPoint.mp Rxy);
  | .inr i, .inr j, .inl z | .inr i, .inl y, .inl z => exact rel_chainPoint_embed;
  | .inl _, .inr _, _ => exact absurd Rxy not_rel_embed_chainPoint;
  | .inl _, .inl _, .inr _ | .inr _, .inl _, .inr _ => exact absurd Ryz not_rel_embed_chainPoint;
⟩

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.toPseudoTail tail o).Rel := ⟨by
  intro x;
  match x with
  | .inl x => simp only [Model.Rel]; apply Std.Irrefl.irrefl;
  | .inr i => simp [Model.Rel];
⟩

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ (M.toPseudoTail tail o).Rel := ⟨by
  apply ConverseWellFounded.iff_has_max.mpr;
  intro s hs;
  by_cases hs₁ : {x | Sum.inl x ∈ s}.Nonempty;
  . obtain ⟨m, hm₁, hm₂⟩ := ConverseWellFounded.has_max (IsConverseWellFounded.cwf (r := M.Rel)) _ hs₁;
    refine ⟨embed m, hm₁, ?_⟩;
    rintro (y | j) hy;
    . exact hm₂ y hy;
    . exact not_rel_embed_chainPoint;
  . have hs₂ : {i : ℕ∞ | Sum.inr i ∈ s}.Nonempty := by
      obtain ⟨x, hx⟩ := hs;
      match x with
      | .inl x => exact absurd ⟨x, hx⟩ hs₁;
      | .inr i => exact ⟨i, hx⟩;
    obtain ⟨m, hm₁, hm₂⟩ := (wellFounded_lt (α := ℕ∞)).has_min _ hs₂;
    refine ⟨chainPoint m, hm₁, ?_⟩;
    rintro (y | j) hy;
    . exact absurd ⟨y, hy⟩ hs₁;
    . exact fun h => hm₂ j hy (rel_chainPoint_chainPoint.mp h);
⟩

instance [M.IsGL] : (M.toPseudoTail tail o).IsGL where

open Model.World (Forces)

/-- 元のモデルから pseudo-tail model への埋め込みは p-morphism である． -/
def pMorphismOriginal (M : Model κ α) (tail : M.World) (o : α → Prop) :
    M →ₚ (M.toPseudoTail tail o).toModel where
  toFun := embed
  forth := rel_embed_embed.mpr
  back := by
    rintro w (v | i) h;
    . exact ⟨v, rfl, rel_embed_embed.mp h⟩;
    . exact absurd h not_rel_embed_chainPoint;
  atomic := Iff.rfl

lemma modal_equivalent_original {x : M.World} :
    Model.World.ModalEquivalent (M₁ := M) (M₂ := (M.toPseudoTail tail o).toModel) x (embed x) :=
  (pMorphismOriginal M tail o).modal_equivalence x

/-- 元のモデルの世界（`embed x`）では pseudo-tail model と元のモデルの forces が一致する． -/
lemma forces_inl {x : M.World} :
    Forces (M := (M.toPseudoTail tail o).toModel) (embed x) A ↔ x ⊩ A :=
  modal_equivalent_original.symm

/-- pseudo-tail model の根（ω）で `□A` が成立するならば全ての点で `□A` が成立する． -/
lemma forces_box_of_root_forces_box {x : (M.toPseudoTail tail o).World}
  (h : Forces (M := (M.toPseudoTail tail o).toModel) (M.toPseudoTail tail o).root.1 (□A)) :
  Forces (M := (M.toPseudoTail tail o).toModel) x (□A) := by
  intro y Rxy;
  apply h;
  match x, y with
  | _, .inl y => exact rel_chainPoint_embed;
  | .inl x, .inr j => exact absurd Rxy not_rel_embed_chainPoint;
  | .inr i, .inr j => exact rel_chainPoint_chainPoint.mpr $ lt_of_lt_of_le (rel_chainPoint_chainPoint.mp Rxy) le_top;

/--
  部分論理式について閉じた集合 `S` の各 `□B ∈ S` に対して根で `□B 🡒 B` が成立しているならば，
  `S` の各論理式の forces は根と鎖上の各点（`chainPoint n`）で一致する．
-/
lemma root_forces_iff_forces_nat [DecidableEq α] {M : RootedModel κ α} [IsTrans _ M.Rel]
  {o : α → Prop} {S : FormulaFinset α}
  (Sclosed : ∀ B ∈ S, B.subfmls ⊆ S)
  (hS : ∀ B ∈ S.prebox, M.root.1 ⊩ (□B 🡒 B)) :
  ∀ B ∈ S, ∀ n : ℕ, M.root.1 ⊩ B ↔
    Forces (M := (M.toModel.toPseudoTail M.root.1 o).toModel) (chainPoint (n : ℕ∞)) B := by
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
      . have hj : j < (n : ℕ∞) := rel_chainPoint_chainPoint.mp Rny;
        obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hj);
        exact (ihB hBS m).mp $ hS B (by grind) h;
    . intro h x Rrx;
      exact forces_inl.mp $ h (embed x) rel_chainPoint_embed;

end toPseudoTail

end Model

end
