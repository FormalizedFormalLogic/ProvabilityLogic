module

public import SeqPL.Kripke.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.Chain
public import Mathlib.Data.PNat.Basic

@[expose]
public section


namespace Fin

def posLast (n : ℕ+) : Fin n := ⟨n.natPred, by simp [PNat.natPred]⟩

end Fin


variable [Nonempty κ]


abbrev Model.Root (M : Model κ α) := { r : M.World // ∀ x, x ≠ r → r ≺ x }

structure RootedModel (κ) [Nonempty κ] (α) extends Model κ α where
  root : toModel.Root


abbrev RootedModel.extendRoot (M : RootedModel κ α) (n : ℕ+) : RootedModel (M.World ⊕ Fin n) α where
  Rel' x y :=
    match x, y with
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl _ => True
    | .inr i, .inr j => j < i
  Val' x a :=
    match x with
    | .inl x => M.Val x a
    | .inr _ => M.Val M.root a
  root := ⟨.inr (Fin.posLast n), by
    intro x hx;
    match x with
    | .inl x => simp [Model.Rel];
    | .inr i =>
      replace hx : i ≠ Fin.posLast n := by simpa using hx;
      have h1 := i.2;
      have h2 : i.val ≠ n.natPred := by simpa [Fin.ext_iff, Fin.posLast] using hx;
      simp only [Model.Rel, Fin.lt_def, Fin.posLast, PNat.natPred] at *;
      omega;
  ⟩

namespace RootedModel.extendRoot

variable {M : RootedModel κ α} {n : ℕ+} {x y : M.World}

def embed (x : M.World) : (M.extendRoot n).World := .inl x
instance : Coe M.World (M.extendRoot n).World := ⟨embed⟩

@[grind =]
lemma rel_embed_embed_iff_rel : (M.extendRoot n).Rel x y ↔ x ≺ y := by
  simp [embed, Model.Rel];

@[grind =]
lemma relItr_embed_embed_iff_relItr : (M.extendRoot n).RelItr k x y ↔ x ≺^[k] y := by
  induction k generalizing x y <;> simp_all [embed, Model.RelItr]

instance [Fintype M.World] : Fintype (M.extendRoot n).World := instFintypeSum M.World (Fin n)

instance [IsTrans _ M.Rel] : IsTrans _ (M.extendRoot n).Rel := by
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

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.extendRoot n).Rel := by
  constructor;
  intro x;
  match x with
  | .inl x => simp_all only [Model.Rel]; apply Std.Irrefl.irrefl
  | .inr i => simp [Model.Rel];

instance [IsConverseWellFounded _ M.Rel] : IsConverseWellFounded _ (M.extendRoot n).Rel where
  cwf := by
    have accInl : ∀ x : M.World, Acc (flip (M.extendRoot n).Rel) (Sum.inl x) := by
      intro x;
      apply WellFounded.induction (IsConverseWellFounded.cwf (r := M.Rel)) x;
      intro x ih;
      constructor;
      intro y hy;
      match y with
      | .inl y => exact ih y hy;
      | .inr j => simp [flip, Model.Rel] at hy;
    have accInr : ∀ i : Fin n, Acc (flip (M.extendRoot n).Rel) (Sum.inr i) := by
      suffices ∀ k, ∀ i : Fin n, i.val = k → Acc (flip (M.extendRoot n).Rel) (Sum.inr i) by
        intro i; exact this i.val i rfl;
      intro k;
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro i rfl;
        constructor;
        intro y hy;
        match y with
        | .inl x => exact accInl x;
        | .inr j => exact ih j.val (by simpa [flip, Model.Rel] using hy) j rfl;
    apply WellFounded.intro;
    intro x;
    match x with
    | .inl x => exact accInl x;
    | .inr i => exact accInr i;

instance [M.IsGL] : (M.extendRoot n).IsGL where

@[simp, grind .]
lemma not_rel_original_tail : ¬(M.extendRoot n |>.Rel (embed x) (Sum.inr i)) := by
  by_contra this;
  grind [embed];

@[simp, grind .]
lemma not_relItr_original_tail  [IsTrans _ M.Rel] : ¬(M.extendRoot n |>.RelItr k (embed x) (Sum.inr i)) := by
  by_contra this;
  match k with
  | 0 =>
    grind [embed];
  | k + 1 =>
    replace : embed (n := n) x ≺ Sum.inr i := Model.relItr_unwrap_trans_pos (by omega) this;
    grind [embed];

lemma exists_tail_of_not_original_world {x : (M.extendRoot n).World} (h : ∀ (x₀ : M.World), x ≠ embed x₀) : ∃ i, x = Sum.inr i := by
  match x with
  | .inl x₀ => exfalso; apply h x₀; rfl;
  | .inr i => use i;

lemma exists_original_of_embed_rel {x : M.World} {y : (M.extendRoot n).World}
  : embed (n := n) x ≺ y → ∃ y₀ : M.World, y = embed y₀ := by
  contrapose!;
  intro h;
  obtain ⟨i, rfl⟩ := exists_tail_of_not_original_world h;
  exact not_rel_original_tail (x := x) (n := n);

lemma same_forces_embed {x : M.World} : Model.World.Forces (M := M.extendRoot n |>.toModel) (embed x) A ↔ x ⊩ A := by
  induction A generalizing x with
  | box A ihA =>
    constructor;
    . grind;
    . intro h y Rxy;
      obtain ⟨y, rfl⟩ := exists_original_of_embed_rel Rxy;
      exact ihA |>.mpr $ h y (rel_embed_embed_iff_rel.mp Rxy);
  | _ => grind [embed]

/-- Chain of `n`-root extension of `M` -/
protected def tail (M : RootedModel κ α) (n : ℕ+) : List (M.extendRoot n).World := List.finRange n |>.reverse.map (.inr ·)

@[simp, grind .]
lemma tail_length : (extendRoot.tail M n).length = n := by simp [extendRoot.tail]

@[simp, grind .]
lemma tail_isChain : List.IsChain (· ≺ ·) (extendRoot.tail M n) := by
  apply List.isChain_map_of_isChain (R := λ a b => b < a);
  . simp [Model.Rel]
  . simp only [List.isChain_reverse];
    simp [List.isChain_iff_pairwise, List.pairwise_lt_finRange];


namespace Ext1

lemma eq_original_or_eq_root (x : (M.extendRoot 1).World) : (∃ x₀ : M.World, x = x₀) ∨ x = (M.extendRoot 1).root := by
  match x with
  | .inl x => simp [embed];
  | .inr i => simp [Fin.posLast]; omega;

lemma eq_original_of_rel_extendRoot_root [Std.Irrefl M.Rel] {x : (M.extendRoot 1).World} (h : (M.extendRoot 1).root.1 ≺ x)
  : ∃ x₀ : M.World, x = x₀ := by
  rcases eq_original_or_eq_root x with (⟨x₀, rfl⟩ | rfl);
  . use x₀;
  . grind;

lemma eq_original_of_neq_extendRoot_root [Std.Irrefl M.Rel] {x : (M.extendRoot 1).World} (h : x ≠ (M.extendRoot 1).root)
  : ∃ x₀ : M.World, x = x₀ := by
  apply eq_original_of_rel_extendRoot_root;
  apply M.extendRoot 1 |>.root.2;
  assumption;

end Ext1

end RootedModel.extendRoot

/-
namespace Model

variable {κ₁ κ₂} [Nonempty κ₁] [Nonempty κ₂] {M₁ : Model κ₁ α} {M₂ : Model κ₂ α}

structure Isomorphism (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) : Type* where
  f : M₁.World → M₂.World
  preserve_rel : ∀ {x y}, x ≺ y ↔ (f x) ≺ (f y)
infixl:60 " ≃ " => Isomorphism

noncomputable def Isomorphism.symm (ι : M₁ ≃ M₂) : Isomorphism M₂ M₁ where
  f := Function.invFun ι.f
  preserve_rel {x y} := by
    sorry;

end Model


namespace RootedModel.extendRoot

section

def compositionIsomprphism {M : RootedModel κ α} {n m : ℕ+} : ((M.extendRoot n).extendRoot m).toModel ≃ (M.extendRoot (n + m)).toModel where
  f x :=
    match x with
    | .inl $ .inl x => .inl x
    | .inl $ .inr ⟨i, hi⟩ => .inr ⟨i, by simp_all; omega⟩
    | .inr ⟨i, hi⟩ => .inr ⟨n + i, by simp_all⟩
  preserve_rel {x y} := by grind;

end

end RootedModel.extendRoot
-/


end
