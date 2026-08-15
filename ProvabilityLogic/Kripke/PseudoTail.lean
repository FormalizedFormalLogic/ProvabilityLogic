module

public import ProvabilityLogic.Kripke.Preservation
public import ProvabilityLogic.Kripke.RootExtension
public import Mathlib.Data.ENat.Basic

@[expose]
public section

variable [Nonempty κ] {M : Model κ α} {A B : Formula α}

namespace Model

/-- Worlds of the free-tail model: the original worlds plus a chain indexed by `ℕ∞`. -/
abbrev toFreeTail.World (M : Model κ α) : Type _ := M.World ⊕ ℕ∞

/--
  The free-tail model (an ω-extension of `M`): rooted at ω (`chainPoint ⊤`), with an
  infinite descending chain `chainPoint n` (`n : ℕ`) attached below it, connecting to
  the whole of the original model `M`. Chain point `chainPoint i` takes the valuation
  `V i`.

  Unlike a tail point of [KKIM25, Definition 2.2], which sees only the cone of a
  designated world together with the tail points below it, here every chain point sees
  the whole of `M`.
-/
abbrev toFreeTail (M : Model κ α) (V : ℕ∞ → α → Prop) :
    RootedModel (toFreeTail.World M) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a :=
    match x with
    | .inl x => M x a
    | .inr i => V i a
  root := ⟨.inr ⊤, by
    intro x hx;
    match x with
    | .inl x => simp [Model.Rel];
    | .inr i =>
      simp only [Model.Rel];
      exact lt_top_iff_ne_top.mpr (by simpa using hx);
  ⟩

/--
  The pseudo-tail model (a constant ω-extension of `M`): the free-tail model whose
  chain points below ω all share the valuation `M tail`, while ω itself takes the
  valuation `o`.
-/
abbrev toPseudoTail (M : Model κ α) (tail : M.World) (o : α → Prop) :=
  M.toFreeTail (fun i a => if i = (⊤ : ℕ∞) then o a else M tail a)

namespace toFreeTail

variable {V : ℕ∞ → α → Prop}

/-- The embedding of a world of the original model `M` into the free-tail model
`M.toFreeTail V`. -/
protected abbrev embed (x : M.World) : (M.toFreeTail V).World := .inl x

/-- The world in the chain, indexed by `i : ℕ∞` (`⊤` is the free-tail model's own
root, ω). -/
protected abbrev chainPoint (i : ℕ∞) : (M.toFreeTail V).World := .inr i

@[simp] lemma root_eq : (M.toFreeTail V).root.1 = toFreeTail.chainPoint ⊤ := rfl

@[simp]
lemma rel_embed_embed {x y : M.World} :
    (M.toFreeTail V).Rel (toFreeTail.embed x) (toFreeTail.embed y) ↔ x ≺ y := by
  simp [Model.Rel];

@[simp]
lemma not_rel_embed_chainPoint {x : M.World} {i : ℕ∞} :
    ¬(M.toFreeTail V).Rel (toFreeTail.embed x) (toFreeTail.chainPoint i) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_embed {i : ℕ∞} {x : M.World} :
    (M.toFreeTail V).Rel (toFreeTail.chainPoint i) (toFreeTail.embed x) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_chainPoint {i j : ℕ∞} :
    (M.toFreeTail V).Rel (toFreeTail.chainPoint i) (toFreeTail.chainPoint j) ↔ j < i := by
  simp [Model.Rel];

instance [IsTrans _ M.Rel] : IsTrans _ (M.toFreeTail V).Rel := ⟨by
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

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.toFreeTail V).Rel := ⟨by
  intro x;
  match x with
  | .inl x => simp only [Model.Rel]; apply Std.Irrefl.irrefl;
  | .inr i => simp [Model.Rel];
⟩

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ (M.toFreeTail V).Rel := ⟨by
  apply ConverseWellFounded.iff_has_max.mpr;
  intro s hs;
  by_cases hs₁ : {x | Sum.inl x ∈ s}.Nonempty;
  . obtain ⟨m, hm₁, hm₂⟩ := ConverseWellFounded.has_max (IsConverseWellFounded.cwf (rel := M.Rel)) _ hs₁;
    use toFreeTail.embed m, hm₁;
    rintro (y | j) hy;
    . exact hm₂ y hy;
    . exact not_rel_embed_chainPoint;
  . have hs₂ : {i : ℕ∞ | Sum.inr i ∈ s}.Nonempty := by
      obtain ⟨x, hx⟩ := hs;
      match x with
      | .inl x => exact absurd ⟨x, hx⟩ hs₁;
      | .inr i => exact ⟨i, hx⟩;
    obtain ⟨m, hm₁, hm₂⟩ := (wellFounded_lt (α := ℕ∞)).has_min _ hs₂;
    use toFreeTail.chainPoint m, hm₁;
    rintro (y | j) hy;
    . exact absurd ⟨y, hy⟩ hs₁;
    . exact fun h => hm₂ j hy (rel_chainPoint_chainPoint.mp h);
⟩

instance [M.IsGL] : (M.toFreeTail V).IsGL where

open Model.World (Forces)

/-- The embedding of the original model into the free-tail model is a p-morphism. -/
def pMorphismOriginal (M : Model κ α) (V : ℕ∞ → α → Prop) :
    M →ₚ (M.toFreeTail V).toModel where
  toFun := toFreeTail.embed
  forth := rel_embed_embed.mpr
  back := by
    rintro w (v | i) h;
    . exact ⟨v, rfl, rel_embed_embed.mp h⟩;
    . exact absurd h not_rel_embed_chainPoint;
  atomic := Iff.rfl

lemma modal_equivalent_original {x : M.World} :
    Model.World.ModalEquivalent (M₁ := M) (M₂ := (M.toFreeTail V).toModel) x (toFreeTail.embed x) :=
  (pMorphismOriginal M V).modal_equivalence x

/-- At an original-model world (`embed x`), forcing in the free-tail model agrees
with forcing in the original model. -/
lemma forces_inl {x : M.World} :
    Forces (M := (M.toFreeTail V).toModel) (toFreeTail.embed x) A ↔ x ⊩ A :=
  modal_equivalent_original.symm

/-- If `□A` holds at the free-tail model's root (ω), it holds at every point. -/
lemma forces_box_of_root_forces_box {x : (M.toFreeTail V).World}
  (h : (M.toFreeTail V).root.1 ⊩ (□A)) :
  x ⊩ (□A) := by
  intro y Rxy;
  apply h;
  match x, y with
  | _, .inl y => exact rel_chainPoint_embed;
  | .inl x, .inr j => exact absurd Rxy not_rel_embed_chainPoint;
  | .inr i, .inr j => exact rel_chainPoint_chainPoint.mpr $ lt_of_lt_of_le (rel_chainPoint_chainPoint.mp Rxy) le_top;

/--
  If `□A` holds at cofinally many chain points, it holds at the free-tail model's root
  (ω): the core of condition (‡) in the proof of [KKIM25, Theorem 5.7].
-/
lemma root_forces_box_of_frequently_chainPoint_forces
  (h : ∀ n : ℕ, ∃ j ≥ n, Forces (M := (M.toFreeTail V).toModel) (toFreeTail.chainPoint (j : ℕ∞)) (□A)) :
  (M.toFreeTail V).root.1 ⊩ (□A) := by
  rintro (y | m) Rry;
  . obtain ⟨j, -, hj⟩ := h 0;
    exact hj _ (rel_chainPoint_embed (i := (j : ℕ∞)));
  . have hm : m < (⊤ : ℕ∞) := rel_chainPoint_chainPoint.mp Rry;
    obtain ⟨m₀, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hm);
    obtain ⟨j, hj₁, hj₂⟩ := h (m₀ + 1);
    exact hj₂ _ (rel_chainPoint_chainPoint.mpr (WithTop.coe_lt_coe.mpr (by omega)));

end toFreeTail

namespace toPseudoTail

variable {tail : M.World} {o : α → Prop}

open Model.World (Forces)

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
    Forces (M := (M.toModel.toPseudoTail M.root.1 o).toModel) (toFreeTail.chainPoint (n : ℕ∞)) B := by
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
      . apply toFreeTail.forces_inl.mpr;
        by_cases hx : x = M.root.1;
        . exact hx ▸ hS B (by grind) h;
        . exact h x (M.root.2 x hx);
      . have hj : j < (n : ℕ∞) := toFreeTail.rel_chainPoint_chainPoint.mp Rny;
        obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hj);
        exact (ihB hBS m).mp $ hS B (by grind) h;
    . intro h x Rrx;
      exact toFreeTail.forces_inl.mp $ h (toFreeTail.embed x) toFreeTail.rel_chainPoint_embed;

-- Re-expose the `toFreeTail` API under the old names, for callers built against
-- `toPseudoTail` before it became a specialization of `toFreeTail`.
export toFreeTail (embed chainPoint root_eq rel_embed_embed not_rel_embed_chainPoint
  rel_chainPoint_embed rel_chainPoint_chainPoint pMorphismOriginal modal_equivalent_original
  forces_inl forces_box_of_root_forces_box)

end toPseudoTail

end Model

end
