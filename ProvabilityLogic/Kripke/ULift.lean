module

public import ProvabilityLogic.Kripke.Linearity
public import ProvabilityLogic.Kripke.Preservation

/-!
`ULift`-lifting of a model, and of a rooted model, along its world type. Forcing (at every
world, resp. at the root) is preserved, and the `GL`/`GLPoint3` finite model classes are
inherited, so a countermodel may freely be moved between universes.

This turns a concretely indexed countermodel such as a `Fin (n + 1)`-indexed chain (living in
`Type 0`) into a countermodel in an arbitrary universe `Type v`. Both directions are used:
completeness theorems stated for a fixed universe of worlds are generalized to quantify over
all universes, and conversely a small rooted countermodel is transported into the universe of
the atom type `α`, which is the universe over which `LogicGL.iff_forces_root` quantifies.
-/

@[expose]
public section

universe v

variable {κ : Type u} [Nonempty κ] {α : Type w}

namespace Model

variable {M : Model κ α}

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
    (ULift.up x) ⊩[M.uLift.{v}] A ↔ x ⊩[M] A :=
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

namespace RootedModel

variable {M : RootedModel κ α}

/-- The rooted model obtained from `M` by `ULift`-lifting its world type: the frame and the
valuation are those of `M.toModel.uLift`, and `ULift.up M.root` is again a root. -/
def uLift (M : RootedModel κ α) : RootedModel (ULift.{v} κ) α where
  toModel := M.toModel.uLift
  root := ⟨.up M.root.1, fun x hx => M.root.2 x.down (fun h => hx (congrArg ULift.up h))⟩

instance [M.IsFiniteGL] : (M.uLift.{v}).IsFiniteGL :=
  inferInstanceAs (M.toModel.uLift.{v}).IsFiniteGL

instance [M.IsFiniteGLPoint3] : (M.uLift.{v}).IsFiniteGLPoint3 :=
  inferInstanceAs (M.toModel.uLift.{v}).IsFiniteGLPoint3

/-- Forcing at the root is preserved by `ULift`-lifting a rooted model. -/
lemma forces_uLift_root_iff {A : Formula α} :
  (M.uLift.{v}).root.1 ⊩[(M.uLift.{v}).toModel] A ↔ M.root.1 ⊩[M.toModel] A :=
  Model.forces_uLift_iff

end RootedModel

end
