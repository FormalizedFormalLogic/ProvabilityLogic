module

public import SeqPL.Kripke.Basic


@[expose]
public section


namespace Fin

def posLast (n : ℕ+) : Fin n := ⟨n.natPred, by simp [PNat.natPred]⟩

end Fin


variable [Nonempty κ] {M : Model κ} {n : ℕ+} {A B : Formula} {Γ Γ' Δ Δ' : FormulaFinset}

namespace Model

abbrev root (M : Model κ) := { r : M.World // ∀ x, x ≠ r → r ≺ x }

abbrev extendRoot (M : Model κ) (n : ℕ+) (r : M.root) : Model (κ ⊕ Fin n) where
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

namespace extendRoot

variable {r : M.root}

protected abbrev root (M : Model κ) (n : ℕ+) (r : M.root) : (M.extendRoot n r).root := ⟨.inr (Fin.posLast n), by
  intro x hx;
  match x with
  | .inl x => simp_all [extendRoot, Model.Rel]
  | .inr i => simp_all [Model.Rel, Fin.posLast]; sorry;
⟩
instance : Nonempty (M.extendRoot n r).root := ⟨extendRoot.root M n r⟩

instance [IsTrans _ M.Rel] : IsTrans _ (M.extendRoot n r).Rel := by
  constructor;
  intro x y z Rxy Ryz;
  match x, y, z with
  | .inl x, .inl y, .inl z =>
    simp_all only [Model.Rel];
    exact IsTrans.trans _ _ _ Rxy Ryz;
  | .inr _, .inr _, .inr _ => omega;
  | _, .inl _, .inr _
  | .inl _, .inr _, _
  | .inr _, _, .inl _ =>
    simp_all only [Model.Rel];

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.extendRoot n r).Rel := by
  constructor;
  intro x;
  match x with
  | .inl x => simp_all only [Model.Rel]; apply Std.Irrefl.irrefl
  | .inr i => simp [Model.Rel];

protected abbrev chain (M : Model κ) (n : ℕ+) (r : M.root) : List (M.extendRoot n r).World := List.finRange n |>.reverse.map (.inr ·)

@[simp]
lemma chain_length : (extendRoot.chain M n r).length = n := by simp

@[simp]
lemma chain_isChain : List.IsChain (· ≺ ·) (extendRoot.chain M n r) := by
  apply List.isChain_map_of_isChain (R := λ a b => b < a);
  . simp [Model.Rel]
  . simp [List.isChain_reverse]
    sorry;

end extendRoot

end Model

end
