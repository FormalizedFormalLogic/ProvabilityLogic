module

public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.RootExtension

@[expose]
public section

variable [Nonempty κ] {α}

namespace Model

namespace World

variable {M : Model κ α} {r x y : M.World}

@[grind]
def IsSuccessorOf (x r : M.World) : Prop := x = r ∨ r ≺ x

@[simp, grind .]
lemma isSuccessorOf_self {r : M.World} : r.IsSuccessorOf r := by grind;

lemma isSuccessorOf_of_isSuccessorOf [IsTrans _ M.Rel] (h : x.IsSuccessorOf r) (Rxy : x ≺ y) : y.IsSuccessorOf r := by
  rcases h with (rfl | h);
  . right; assumption;
  . right; trans x <;> assumption;

@[grind]
def IsProperPredecessorOf (x r : M.World) : Prop := x ≠ r ∧ x ≺ r

end World


abbrev Successors (M : Model κ α) (r : M.World) := { x : M.World // x.IsSuccessorOf r }
infixl:60 "↾" => Successors

instance {M : Model κ α} : Nonempty (M↾r) := ⟨⟨r, by grind⟩⟩

instance {M : Model κ α} {r : M.World} [Finite M.World] : Finite (Successors M r) := Subtype.finite

@[grind]
def toRootedModel (M : Model κ α) (r : M.World) : RootedModel (M↾r) α where
  Rel' x y := M.Rel x y
  Val' x a := M.Val x a
  root := ⟨⟨r, by grind⟩, by grind⟩

namespace toRootedModel

variable {M : Model κ α} {r x : M.World} {A : Formula α}

instance [IsTrans _ M.Rel] : IsTrans _ (toRootedModel M r).Rel := by
  constructor;
  rintro ⟨x, rfl | Rrx⟩ ⟨y, rfl | Rry⟩ ⟨z, rfl | Rrz⟩ Rxy Ryz;
  case inl.inr.inl | inr.inl.inr | inr.inr.inl | inr.inr.inr =>
    simp_all only [Model.Rel, toRootedModel];
    trans y <;> assumption;
  all_goals
    simp_all only [Model.Rel, toRootedModel];

instance [Std.Irrefl M.Rel] : Std.Irrefl (toRootedModel M r).Rel := by
  constructor;
  rintro ⟨x, rfl | Rrx⟩ <;>
  . simp_all only [Model.Rel, toRootedModel];
    apply Std.Irrefl.irrefl;

instance [Finite M.World] : Finite (toRootedModel M r).World := inferInstance

instance [M.IsFiniteGL] : (toRootedModel M r).IsFiniteGL where


variable [IsTrans _ M.Rel]

open Model.World (Forces)

lemma forces_same_of_isSuccessorOf (hx : x.IsSuccessorOf r) : Forces (M := toRootedModel M r |>.toModel) ⟨x, hx⟩ A ↔ x ⊩ A := by
  induction A generalizing x with
  | atom a => simp [Forces, toRootedModel];
  | bot => simp [Forces];
  | imp A B ihA ihB => grind;
  | box A ihA =>
    constructor;
    . intro h y Rxy;
      apply ihA (Model.World.isSuccessorOf_of_isSuccessorOf hx Rxy) |>.mp;
      apply h;
      grind;
    . intro h y Rxy;
      apply ihA (Model.World.isSuccessorOf_of_isSuccessorOf hx Rxy) |>.mpr;
      apply h;
      grind;

lemma forces_same_at_successor {x : (toRootedModel M r).World} : Forces x A ↔ Forces (M := M) x A :=
  forces_same_of_isSuccessorOf x.property

lemma forces_same_at_root : Forces (M := toRootedModel M r |>.toModel) ⟨r, by grind⟩ A ↔ Forces (M := M) r A :=
  forces_same_of_isSuccessorOf (by grind)

end toRootedModel


end Model

end
