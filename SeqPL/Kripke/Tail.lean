module

public import SeqPL.Kripke.RootExtension

@[expose]
public section

variable [Nonempty κ] {M : Model κ} {n : ℕ+} {A B : Formula} {Γ Γ' Δ Δ' : FormulaFinset}

namespace Model

abbrev toTail (M : Model κ) (r : M.root) : Model (κ ⊕ ℕ∞) where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val x a :=
    match x with
    | .inl x => M.Val x a
    | .inr _ => M.Val r a

namespace toTail

variable {r : M.root}

protected abbrev root (M : Model κ) (r : M.root) : (M.toTail r).root := ⟨.inr ⊤, by
  intro x hx;
  match x with
  | .inl x => simp_all [toTail, Model.Rel]
  | .inr i => simp_all [Model.Rel]; grind;
⟩

instance : Nonempty (M.toTail r).root := ⟨toTail.root M r⟩

instance [IsTrans _ M.Rel] : IsTrans _ (M.toTail r).Rel := by
  constructor;
  intro x y z Rxy Ryz;
  match x, y, z with
  | .inl x, .inl y, .inl z =>
    simp_all only [Model.Rel];
    exact IsTrans.trans _ _ _ Rxy Ryz;
  | .inr _, .inr _, .inr _ =>
    grind;
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

protected abbrev tail (M : Model κ) (r : M.root) : ℕ+ → (M.toTail r).World := λ n => .inr n

@[simp]
lemma tail_isChain (h : i < j) : ((toTail.tail M r) j ≺ (toTail.tail M r) i) := by
  simp [Model.Rel]; grind;

end toTail

end Model

end
