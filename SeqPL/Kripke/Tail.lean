module

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

end toTail

end Model

end
