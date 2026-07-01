module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Pairwise

@[expose]
public section

namespace List.IsChain

variable {α : Type*} {R : α → α → Prop} {l : List α} {x y : α}

/-- 推移的関係の chain 上の相異なる 2 元はいずれかの向きに関係する． -/
lemma connected_of_trans [IsTrans α R] (h : List.IsChain R l)
    (hx : x ∈ l) (hy : y ∈ l) (nexy : x ≠ y) : R x y ∨ R y x := by
  have hp : l.Pairwise (fun a b => R a b ∨ R b a) :=
    (List.isChain_iff_pairwise.mp h).imp (fun h => Or.inl h);
  haveI : Std.Symm (fun a b => R a b ∨ R b a) := ⟨fun _ _ h => h.symm⟩;
  exact hp.forall hx hy nexy;

/-- 非反射的・推移的関係の chain は重複を持たない． -/
lemma nodup_of_irrefl_trans [IsTrans α R] [Std.Irrefl R] (h : List.IsChain R l) : l.Nodup := by
  apply (List.isChain_iff_pairwise.mp h).imp;
  intro a b hab e;
  subst e;
  exact Std.Irrefl.irrefl a hab;

end List.IsChain

end
