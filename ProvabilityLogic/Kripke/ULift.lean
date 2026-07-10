module

public import ProvabilityLogic.Kripke.Linearity
public import ProvabilityLogic.Kripke.Preservation

@[expose]
public section

/-!
`ULift`-lifting of a model along its world type. Used to turn a `Fin (n + 1)`-indexed
countermodel (living in `Type 0`) into a countermodel in an arbitrary universe `Type v`, so
that Gentzen completeness theorems stated for a fixed universe of worlds can be generalized
to quantify over all universes.
-/

universe v

variable {κ : Type u} [Nonempty κ] {α : Type w} {M : Model κ α}

namespace Model

/-- The model obtained from `M` by replacing its world type `κ` with `ULift.{v} κ`, keeping
the same relation and valuation up to `ULift.down`. -/
def uLift (M : Model κ α) : Model (ULift.{v} κ) α where
  Rel' x y := M.Rel' x.down y.down
  Val' x a := M.Val' x.down a

/-- `M` and `M.uLift` are bisimilar via `x ↦ ULift.up x`, since the frame and valuation of
`M.uLift` are literally those of `M` transported through the bijection `ULift.up`/`.down`. -/
def uLiftBisimulation (M : Model κ α) : M ⇄ M.uLift.{v} where
  toRel x y := y = ULift.up x
  atomic := by
    intro x y a h; subst h; rfl
  forth := by
    intro x y y' h hR; subst h;
    exact ⟨.up y, rfl, hR⟩
  back := by
    intro x y y' h hR; subst h;
    exact ⟨y'.down, rfl, hR⟩

/-- Forcing is preserved by `ULift`-lifting a model: a formula is forced at `ULift.up x` in
`M.uLift` iff it is forced at `x` in `M`. -/
lemma forces_uLift_iff {x : M.World} {A : Formula α} :
    Model.World.Forces (M := M.uLift.{v}) (ULift.up x) A ↔ Model.World.Forces (M := M) x A :=
  (World.modal_equivalent_of_bisimilar M.uLiftBisimulation.{v} rfl).symm

instance [IsTrans _ M.Rel] : IsTrans _ (M.uLift.{v}).Rel where
  trans := fun x y z hxy hyz => IsTrans.trans (r := M.Rel) x.down y.down z.down hxy hyz

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.uLift.{v}).Rel where
  irrefl := fun x => Std.Irrefl.irrefl (r := M.Rel) x.down

instance [Finite M.World] : Finite (M.uLift.{v}).World := inferInstanceAs (Finite (ULift.{v} κ))

instance [M.IsFiniteGL] : (M.uLift.{v}).IsFiniteGL where
  finite := inferInstance

instance [M.IsFiniteGLPoint3] : (M.uLift.{v}).IsFiniteGLPoint3 where
  finite := inferInstance
  linear := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ hxy hxz;
    rcases Model.linear (M := M) hxy hxz with h | h | h;
    · exact Or.inl h;
    · exact Or.inr <| Or.inl <| congrArg ULift.up h;
    · exact Or.inr <| Or.inr h;

end Model

end
