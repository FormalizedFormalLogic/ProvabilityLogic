module

public import SeqPL.Kripke.Preservation
public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.RootExtension
public import Mathlib.Data.ENat.Basic

@[expose]
public section

variable [Nonempty κ] {M : Model κ α} {n : ℕ+} {A B : Formula α} {Γ Γ' Δ Δ' : FormulaFinset α}

namespace Model

/-- Worlds of the tail model: the original worlds plus a chain indexed by `ℕ∞`. -/
abbrev toTail.World (M : Model κ α) : Type _ := M.World ⊕ ℕ∞

abbrev toTail (M : Model κ α) (tail : M.World) : RootedModel (toTail.World M) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a :=
    match x with
    | .inl x => M.Val x a
    | .inr _ => M.Val tail a
  root := ⟨.inr ⊤, by
    intro x hx;
    match x with
    | .inl x => simp [Model.Rel];
    | .inr i =>
      simp only [Model.Rel];
      exact lt_top_iff_ne_top.mpr (by simpa using hx);
  ⟩

namespace toTail

variable {tail : M.World}

/-- The embedding of a world of the original model `M` into the tail model `M.toTail tail`. -/
protected abbrev embed (x : M.World) : (M.toTail tail).World := .inl x

/-- The world in the chain attached above `tail`, indexed by `i : ℕ∞` (`⊤` is the tail model's own root). -/
protected abbrev chainPoint (i : ℕ∞) : (M.toTail tail).World := .inr i

@[simp] lemma root_eq : (M.toTail tail).root.1 = toTail.chainPoint ⊤ := rfl

@[simp]
lemma rel_embed_embed {x y : M.World} : (M.toTail tail).Rel (toTail.embed x) (toTail.embed y) ↔ x ≺ y := by
  simp [Model.Rel];

@[simp]
lemma not_rel_embed_chainPoint {x : M.World} {i : ℕ∞} : ¬(M.toTail tail).Rel (toTail.embed x) (toTail.chainPoint i) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_embed {i : ℕ∞} {x : M.World} : (M.toTail tail).Rel (toTail.chainPoint i) (toTail.embed x) := by
  simp [Model.Rel];

@[simp]
lemma rel_chainPoint_chainPoint {i j : ℕ∞} : (M.toTail tail).Rel (toTail.chainPoint i) (toTail.chainPoint j) ↔ j < i := by
  simp [Model.Rel];

instance [IsTrans _ M.Rel] : IsTrans _ (M.toTail tail).Rel := by
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

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.toTail tail).Rel := by
  constructor;
  intro x;
  match x with
  | .inl x => simp_all only [Model.Rel]; apply Std.Irrefl.irrefl
  | .inr i => simp [Model.Rel];

/-- The chain of `ℕ∞`-worlds attached above `tail`. -/
protected abbrev chain (M : Model κ α) (tail : M.World) : ℕ+ → (M.toTail tail).World := λ n => toTail.chainPoint n

@[simp]
lemma chain_isChain (h : i < j) : ((toTail.chain M tail) j ≺ (toTail.chain M tail) i) := by
  simp only [Model.Rel];
  exact_mod_cast h;

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ (M.toTail tail).Rel := ⟨by
  apply ConverseWellFounded.iff_has_max.mpr;
  intro s hs;
  by_cases hs₁ : {x | Sum.inl x ∈ s}.Nonempty;
  . obtain ⟨m, hm₁, hm₂⟩ := ConverseWellFounded.has_max (IsConverseWellFounded.cwf (rel := M.Rel)) _ hs₁;
    use toTail.embed m, hm₁;
    rintro (y | j) hy;
    . exact hm₂ y hy;
    . exact not_rel_embed_chainPoint;
  . have hs₂ : {i : ℕ∞ | Sum.inr i ∈ s}.Nonempty := by
      obtain ⟨x, hx⟩ := hs;
      match x with
      | .inl x => exact absurd ⟨x, hx⟩ hs₁;
      | .inr i => exact ⟨i, hx⟩;
    obtain ⟨m, hm₁, hm₂⟩ := (wellFounded_lt (α := ℕ∞)).has_min _ hs₂;
    use toTail.chainPoint m, hm₁;
    rintro (y | j) hy;
    . exact absurd ⟨y, hy⟩ hs₁;
    . exact fun h => hm₂ j hy (rel_chainPoint_chainPoint.mp h);
⟩

instance [M.IsGL] : (M.toTail tail).IsGL where

open Model.World (Forces)

/-- The embedding of the original model into the tail model is a p-morphism. -/
def pMorphismOriginal (M : Model κ α) (tail : M.World) : M →ₚ (M.toTail tail).toModel where
  toFun := toTail.embed
  forth := rel_embed_embed.mpr
  back := by
    rintro w (v | i) h;
    . exact ⟨v, rfl, rel_embed_embed.mp h⟩;
    . exact absurd h not_rel_embed_chainPoint;
  atomic := Iff.rfl

lemma modal_equivalent_original {x : M.World} :
    Model.World.ModalEquivalent (M₁ := M) (M₂ := (M.toTail tail).toModel) x (toTail.embed x) :=
  (pMorphismOriginal M tail).modal_equivalence x

/-- At an original-model world (`embed x`), forcing in the tail model agrees with
forcing in the original model. -/
lemma forces_inl {x : M.World} : Forces (M := (M.toTail tail).toModel) (toTail.embed x) A ↔ x ⊩ A :=
  modal_equivalent_original.symm

/-- Forcing of `□A` is downward closed on the chain: if it holds at `chainPoint n`,
it also holds at any `chainPoint m` below it. -/
lemma forces_nat_box_antitone {m n : ℕ} (hmn : m ≤ n)
  (h : Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) (□A)) :
  Forces (M := (M.toTail tail).toModel) (toTail.chainPoint m) (□A) := by
  rintro (x | j) Rmy;
  . exact h (toTail.embed x) rel_chainPoint_embed;
  . apply h (toTail.chainPoint j);
    apply rel_chainPoint_chainPoint.mpr;
    exact lt_of_lt_of_le (rel_chainPoint_chainPoint.mp Rmy) (by exact_mod_cast hmn);

/-- Forcing at chain points (`chainPoint n`) eventually stabilizes as `n` grows. -/
lemma forces_nat_eventually_stable (A : Formula α) :
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
    (Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) A ↔
     Forces (M := (M.toTail tail).toModel) (toTail.chainPoint k) A) := by
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
    by_cases hf : ∀ n : ℕ, Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) (□A);
    . exact ⟨0, fun n _ => iff_of_true (hf n) (hf 0)⟩;
    . push Not at hf;
      obtain ⟨m, hm⟩ := hf;
      exact ⟨m, fun n hn => iff_of_false (fun h => hm (forces_nat_box_antitone hn h)) hm⟩;

/-- Forcing at chain points (`chainPoint n`) eventually stabilizes, as `n` grows, to the
forcing value at the tail model's own root (`chainPoint ⊤`). -/
lemma forces_nat_eventually_root (A : Formula α) :
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
    (Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) A ↔
     Forces (M := (M.toTail tail).toModel) (toTail.chainPoint ⊤) A) := by
  induction A with
  | atom a => exact ⟨0, fun n _ => Iff.rfl⟩;
  | bot => exact ⟨0, fun n _ => Iff.rfl⟩;
  | imp A B ihA ihB =>
    obtain ⟨k₁, h₁⟩ := ihA;
    obtain ⟨k₂, h₂⟩ := ihB;
    refine ⟨max k₁ k₂, fun n hn => ?_⟩;
    have hA := h₁ n (le_trans (le_max_left _ _) hn);
    have hB := h₂ n (le_trans (le_max_right _ _) hn);
    constructor;
    . intro h ha; exact hB.mp (h (hA.mpr ha));
    . intro h ha; exact hB.mpr (h (hA.mp ha));
  | box A _ =>
    by_cases hf : ∀ n : ℕ, Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) (□A);
    . refine ⟨0, fun n _ => iff_of_true (hf n) ?_⟩;
      rintro (x | j) hxy;
      . exact hf 0 (toTail.embed x) rel_chainPoint_embed;
      . obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt (rel_chainPoint_chainPoint.mp hxy));
        exact hf (m + 1) (toTail.chainPoint m) (rel_chainPoint_chainPoint.mpr (by exact_mod_cast Nat.lt_succ_self m));
    . push Not at hf;
      obtain ⟨m, hm⟩ := hf;
      have hm' : ¬ Forces (M := (M.toTail tail).toModel) (toTail.chainPoint ⊤) (□A) := fun h => hm (by
        rintro (x | j) hxy;
        . exact h (toTail.embed x) rel_chainPoint_embed;
        . exact h (toTail.chainPoint j) (rel_chainPoint_chainPoint.mpr (lt_of_lt_of_le (rel_chainPoint_chainPoint.mp hxy) le_top)));
      exact ⟨m, fun n hn => iff_of_false (fun h => hm (forces_nat_box_antitone hn h)) hm'⟩;

/--
  **Tail Lemma** (`Visser1984` Lemma 2.2): `A` is forced at the tail model's own root
  (`chainPoint ⊤`) iff `A` is eventually forced along the chain (`chainPoint n` for all
  sufficiently large `n`).
-/
lemma tailLemma (A : Formula α) :
  Forces (M := (M.toTail tail).toModel) (toTail.chainPoint ⊤) A ↔
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) A := by
  obtain ⟨k, hk⟩ := forces_nat_eventually_root (tail := tail) A;
  constructor;
  . intro h; exact ⟨k, fun n hn => (hk n hn).mpr h⟩;
  . rintro ⟨k', hk'⟩;
    exact (hk (max k k') (le_max_left _ _)).mp (hk' (max k k') (le_max_right _ _));

/--
  If `Γ` is closed under subformulas and the root forces `□B 🡒 B` for every `□B ∈ Γ`,
  then forcing of every formula in `Γ` at the root agrees with forcing at every chain
  point (`chainPoint n`).
-/
lemma root_forces_iff_forces_nat [DecidableEq α] {M : RootedModel κ α} [IsTrans _ M.Rel]
  {Γ : FormulaFinset α}
  (Γclosed : ∀ B ∈ Γ, B.subfmls ⊆ Γ)
  (hΓ : ∀ B ∈ Γ.prebox, M.root.1 ⊩ (□B 🡒 B)) :
  ∀ B ∈ Γ, ∀ n : ℕ, M.root.1 ⊩ B ↔ Forces (M := (M.toModel.toTail M.root.1).toModel) (toTail.chainPoint n) B := by
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
      . have hj : j < (n : ℕ∞) := rel_chainPoint_chainPoint.mp Rny;
        obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hj);
        exact (ihB hBΓ m).mp $ hΓ B (by grind) h;
    . intro h x Rrx;
      exact forces_inl.mp $ h (toTail.embed x) rel_chainPoint_embed;

end toTail

end Model

end
