module

public import ProvabilityLogic.Kripke.Preservation
public import ProvabilityLogic.Kripke.RootedModel
public import ProvabilityLogic.Kripke.RootExtension
public import Mathlib.Data.ENat.Basic

@[expose]
public section

variable [Nonempty κ] {M : Model κ α} {A B : Formula α}

namespace Model

/-- Worlds of the pseudo-tail model: the original worlds plus a chain indexed by `ℕ∞`. -/
abbrev toPseudoTail.World (M : Model κ α) : Type _ := M.World ⊕ ℕ∞

/--
  The pseudo-tail model (an ω-extension of `M`): rooted at ω (`chainPoint ⊤`), with an
  infinite descending chain `chainPoint n` (`n : ℕ`) attached below it, connecting to the
  whole of the original model `M`. Chain points (`chainPoint n`) take the valuation
  `M.Val tail`, while ω takes the valuation `o`.
-/
abbrev toPseudoTail (M : Model κ α) (tail : M.World) (o : α → Prop) :
    RootedModel (toPseudoTail.World M) α where
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
protected abbrev embed (x : M.World) : (M.toPseudoTail tail o).World := .inl x

/-- The world in the chain attached above `tail`, indexed by `i : ℕ∞` (`⊤` is the
pseudo-tail model's own root, ω). -/
protected abbrev chainPoint (i : ℕ∞) : (M.toPseudoTail tail o).World := .inr i

@[simp] lemma root_eq : (M.toPseudoTail tail o).root.1 = toPseudoTail.chainPoint ⊤ := rfl

@[simp]
lemma rel_embed_embed {x y : M.World} :
    (M.toPseudoTail tail o).Rel (toPseudoTail.embed x) (toPseudoTail.embed y) ↔ x ≺ y := by
  simp [Model.Rel];

@[simp]
lemma not_rel_embed_chainPoint {x : M.World} {i : ℕ∞} :
    ¬(M.toPseudoTail tail o).Rel (toPseudoTail.embed x) (toPseudoTail.chainPoint i) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_embed {i : ℕ∞} {x : M.World} :
    (M.toPseudoTail tail o).Rel (toPseudoTail.chainPoint i) (toPseudoTail.embed x) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_chainPoint {i j : ℕ∞} :
    (M.toPseudoTail tail o).Rel (toPseudoTail.chainPoint i) (toPseudoTail.chainPoint j) ↔ j < i := by
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
  . obtain ⟨m, hm₁, hm₂⟩ := ConverseWellFounded.has_max (IsConverseWellFounded.cwf (rel := M.Rel)) _ hs₁;
    use toPseudoTail.embed m, hm₁;
    rintro (y | j) hy;
    . exact hm₂ y hy;
    . exact not_rel_embed_chainPoint;
  . have hs₂ : {i : ℕ∞ | Sum.inr i ∈ s}.Nonempty := by
      obtain ⟨x, hx⟩ := hs;
      match x with
      | .inl x => exact absurd ⟨x, hx⟩ hs₁;
      | .inr i => exact ⟨i, hx⟩;
    obtain ⟨m, hm₁, hm₂⟩ := (wellFounded_lt (α := ℕ∞)).has_min _ hs₂;
    use toPseudoTail.chainPoint m, hm₁;
    rintro (y | j) hy;
    . exact absurd ⟨y, hy⟩ hs₁;
    . exact fun h => hm₂ j hy (rel_chainPoint_chainPoint.mp h);
⟩

instance [M.IsGL] : (M.toPseudoTail tail o).IsGL where

open Model.World (Forces)

/-- The embedding of the original model into the pseudo-tail model is a p-morphism. -/
def pMorphismOriginal (M : Model κ α) (tail : M.World) (o : α → Prop) :
    M →ₚ (M.toPseudoTail tail o).toModel where
  toFun := toPseudoTail.embed
  forth := rel_embed_embed.mpr
  back := by
    rintro w (v | i) h;
    . exact ⟨v, rfl, rel_embed_embed.mp h⟩;
    . exact absurd h not_rel_embed_chainPoint;
  atomic := Iff.rfl

lemma modal_equivalent_original {x : M.World} :
    Model.World.ModalEquivalent (M₁ := M) (M₂ := (M.toPseudoTail tail o).toModel) x (toPseudoTail.embed x) :=
  (pMorphismOriginal M tail o).modal_equivalence x

/-- At an original-model world (`embed x`), forcing in the pseudo-tail model agrees
with forcing in the original model. -/
lemma forces_inl {x : M.World} :
    Forces (M := (M.toPseudoTail tail o).toModel) (toPseudoTail.embed x) A ↔ x ⊩ A :=
  modal_equivalent_original.symm

/-- If `□A` holds at the pseudo-tail model's root (ω), it holds at every point. -/
lemma forces_box_of_root_forces_box {x : (M.toPseudoTail tail o).World}
  (h : (M.toPseudoTail tail o).root.1 ⊩ (□A)) :
  x ⊩ (□A) := by
  intro y Rxy;
  apply h;
  match x, y with
  | _, .inl y => exact rel_chainPoint_embed;
  | .inl x, .inr j => exact absurd Rxy not_rel_embed_chainPoint;
  | .inr i, .inr j => exact rel_chainPoint_chainPoint.mpr $ lt_of_lt_of_le (rel_chainPoint_chainPoint.mp Rxy) le_top;

/--
  If `S` is closed under subformulas and the root forces `□B 🡒 B` for every `□B ∈ S`,
  then forcing of every formula in `S` at the root agrees with forcing at every chain
  point (`chainPoint n`).
-/
lemma root_forces_iff_forces_nat [DecidableEq α] {M : RootedModel κ α} [IsTrans _ M.Rel]
  {o : α → Prop} {S : FormulaFinset α}
  (Sclosed : ∀ B ∈ S, B.subfmls ⊆ S)
  (hS : ∀ B ∈ S.prebox, M.root.1 ⊩ (□B 🡒 B)) :
  ∀ B ∈ S, ∀ n : ℕ, M.root.1 ⊩ B ↔
    Forces (M := (M.toModel.toPseudoTail M.root.1 o).toModel) (toPseudoTail.chainPoint (n : ℕ∞)) B := by
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
      exact forces_inl.mp $ h (toPseudoTail.embed x) rel_chainPoint_embed;

end toPseudoTail

end Model

end
