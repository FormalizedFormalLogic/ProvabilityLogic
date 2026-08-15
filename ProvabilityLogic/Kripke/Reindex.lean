module

public import ProvabilityLogic.Kripke.Linearity
public import ProvabilityLogic.Kripke.Preservation
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
Transport of a model, and of a rooted model, along an equivalence of its world type. Forcing
(at every world, resp. at the root), validity and the `GL`/`GLPoint3` finite model classes are
all preserved, so a countermodel may freely be re-indexed by any type in bijection with its
worlds — in particular by a type in another universe.

Specializing the equivalence to `Finite.equivFin` presents every finite model as a *concrete*
model, one whose worlds are literally `Fin n`. Since a concrete model lives in `Type 0`, it can
in turn be re-indexed into an arbitrary universe, which is what makes it a usable normal form:
`Model.uLift` handles only the special case `Equiv.ulift`, whereas re-indexing composes the two
directions in one step.

This is routine infrastructure with no counterpart in the literature.
-/

@[expose]
public section

universe u v w

section

variable {κ : Type u} [Nonempty κ] {κ' : Type v} [Nonempty κ'] {α : Type w}

namespace Model

variable {M : Model κ α} {e : κ ≃ κ'} {A : Formula α}

/-- The model obtained from `M` by transporting its world type along `e`. -/
def reindex (M : Model κ α) (e : κ ≃ κ') : Model κ' α where
  Rel' x y := M.Rel' (e.symm x) (e.symm y)
  Val' x a := M.Val' (e.symm x) a

/-- `M` and `M.reindex e` are bisimilar via `x ↦ e x`, since the frame and the valuation of
`M.reindex e` are literally those of `M` transported through the bijection `e`. -/
def reindexBisimulation (M : Model κ α) (e : κ ≃ κ') : M ⇄ M.reindex e where
  toRel x y := y = e x
  atomic := by
    rintro x y a rfl;
    simp [reindex, Model.Val];
  forth := by
    rintro x y y' rfl hR;
    exact ⟨e y, rfl, by simpa [reindex, Model.Rel] using hR⟩;
  back := by
    rintro x y y' rfl hR;
    exact ⟨e.symm y', by simp, by simpa [reindex, Model.Rel] using hR⟩;

/-- Forcing is preserved by re-indexing a model: a formula is forced at `e x` in `M.reindex e`
iff it is forced at `x` in `M`. -/
lemma forces_reindex_iff {x : M.World} :
  Model.World.Forces (M := M.reindex e) (e x) A ↔ Model.World.Forces (M := M) x A :=
  (World.modal_equivalent_of_bisimilar (M.reindexBisimulation e) rfl).symm

/-- Forcing is preserved by re-indexing a model, stated at an arbitrary world `y` of
`M.reindex e` rather than at one of the form `e x`. -/
lemma forces_reindex_iff' {y : (M.reindex e).World} :
  Model.World.Forces (M := M.reindex e) y A ↔ Model.World.Forces (M := M) (e.symm y) A := by
  simpa using forces_reindex_iff (M := M) (e := e) (x := e.symm y);

instance [IsTrans _ M.Rel] : IsTrans _ (M.reindex e).Rel where
  trans := fun x y z hxy hyz => IsTrans.trans (r := M.Rel) (e.symm x) (e.symm y) (e.symm z) hxy hyz

instance [Std.Irrefl M.Rel] : Std.Irrefl (M.reindex e).Rel where
  irrefl := fun x => Std.Irrefl.irrefl (r := M.Rel) (e.symm x)

/-- Finiteness of the worlds transfers along `e`. This is deliberately not an `instance`: its
head would be the bare `Finite κ'`, which turns every `Equiv` in context into a source of
`Finite` instances and makes typeclass search loop. -/
lemma finite_reindex [Finite M.World] : Finite (M.reindex e).World := Finite.of_equiv _ e

instance [M.IsFiniteGL] : (M.reindex e).IsFiniteGL where
  finite := finite_reindex

instance [M.IsFiniteGLPoint3] : (M.reindex e).IsFiniteGLPoint3 where
  finite := finite_reindex
  linear := by
    intro x y z hxy hxz;
    rcases Model.linear (M := M) hxy hxz with h | h | h;
    · exact Or.inl h;
    · exact Or.inr <| Or.inl <| e.symm.injective h;
    · exact Or.inr <| Or.inr h;

/-- Validity is preserved by re-indexing a model. -/
lemma validate_reindex_iff : M.reindex e ⊧ A ↔ M ⊧ A :=
  ⟨fun h x => forces_reindex_iff.mp <| h (e x), fun h _ => forces_reindex_iff'.mpr <| h _⟩

end Model


namespace RootedModel

variable {M : RootedModel κ α} {e : κ ≃ κ'} {A : Formula α}

/-- The rooted model obtained from `M` by re-indexing its world type: the frame and the
valuation are those of `M.toModel.reindex e`, and `e M.root.1` is again a root. -/
def reindex (M : RootedModel κ α) (e : κ ≃ κ') : RootedModel κ' α where
  toModel := M.toModel.reindex e
  root := ⟨e M.root.1, by
    intro x hx;
    have h : e.symm x ≠ M.root.1 := fun h => hx <| by rw [← h, Equiv.apply_symm_apply];
    show M.Rel' (e.symm (e M.root.1)) (e.symm x);
    rw [Equiv.symm_apply_apply];
    exact M.root.2 _ h⟩

instance [M.IsFiniteGL] : (M.reindex e).IsFiniteGL :=
  inferInstanceAs (M.toModel.reindex e).IsFiniteGL

instance [M.IsFiniteGLPoint3] : (M.reindex e).IsFiniteGLPoint3 :=
  inferInstanceAs (M.toModel.reindex e).IsFiniteGLPoint3

/-- Forcing at the root is preserved by re-indexing a rooted model. -/
lemma forces_reindex_root_iff : (M.reindex e).root.1 ⊩ A ↔ M.root.1 ⊩ A :=
  Model.forces_reindex_iff

end RootedModel

end


section Concrete

/-- A *concrete* model is one whose worlds are literally `Fin n`. Every finite model is a
concrete model up to re-indexing (`Model.toConcrete`), and a concrete model lives in `Type 0`,
hence can be re-indexed into any universe.

The size is a plain `n : ℕ` with `[NeZero n]`, as in Mathlib's own `Fin` API, rather than an
`ℕ+`: `PNat.val` is not reducible, so instance search cannot see through `Fin ↑n` to instances
registered for a literal `Fin n`. -/
abbrev ConcreteModel (n : ℕ) [NeZero n] (α : Type w) := Model (Fin n) α

/-- A rooted `ConcreteModel`. -/
abbrev ConcreteRootedModel (n : ℕ) [NeZero n] (α : Type w) := RootedModel (Fin n) α

variable {κ : Type u} [Nonempty κ] [Finite κ] {α : Type w}

namespace Model

variable {M : Model κ α} {A : Formula α}

/-- The number of worlds of a model. Being `Nat.card`, it takes the junk value `0` on an
infinite model; only the finite case carries the `NeZero` instance below, and hence only
finite models can be presented concretely. -/
noncomputable def card (M : Model κ α) : ℕ := Nat.card M.World

instance (M : Model κ α) : NeZero M.card := ⟨Nat.card_pos.ne'⟩

/-- Any finite model is a concrete model up to re-indexing. -/
noncomputable def toConcrete (M : Model κ α) : ConcreteModel M.card α :=
  M.reindex (Finite.equivFin κ)

/-- Forcing is preserved by presenting a finite model as a concrete one. -/
lemma forces_toConcrete_iff {x : M.World} :
  Model.World.Forces (M := M.toConcrete) (Finite.equivFin κ x) A ↔
  Model.World.Forces (M := M) x A :=
  forces_reindex_iff

/-- Forcing is preserved by presenting a finite model as a concrete one, stated at an arbitrary
world of the concrete model. -/
lemma forces_toConcrete_iff' {x : M.toConcrete.World} :
  Model.World.Forces (M := M.toConcrete) x A ↔
  Model.World.Forces (M := M) ((Finite.equivFin κ).symm x) A :=
  forces_reindex_iff'

/-- Validity is preserved by presenting a finite model as a concrete one. -/
lemma validate_toConcrete_iff : M.toConcrete ⊧ A ↔ M ⊧ A := validate_reindex_iff

instance [M.IsFiniteGL] : M.toConcrete.IsFiniteGL :=
  inferInstanceAs (M.reindex (Finite.equivFin κ)).IsFiniteGL

instance [M.IsFiniteGLPoint3] : M.toConcrete.IsFiniteGLPoint3 :=
  inferInstanceAs (M.reindex (Finite.equivFin κ)).IsFiniteGLPoint3

end Model

namespace RootedModel

variable {M : RootedModel κ α} {A : Formula α}

/-- Any finite rooted model is a concrete rooted model up to re-indexing. -/
noncomputable def toConcrete (M : RootedModel κ α) : ConcreteRootedModel M.card α :=
  M.reindex (Finite.equivFin κ)

instance [M.IsFiniteGL] : M.toConcrete.IsFiniteGL :=
  inferInstanceAs (M.reindex (Finite.equivFin κ)).IsFiniteGL

instance [M.IsFiniteGLPoint3] : M.toConcrete.IsFiniteGLPoint3 :=
  inferInstanceAs (M.reindex (Finite.equivFin κ)).IsFiniteGLPoint3

/-- Forcing at the root is preserved by presenting a finite rooted model as a concrete one. -/
lemma forces_toConcrete_root_iff : M.toConcrete.root.1 ⊩ A ↔ M.root.1 ⊩ A :=
  forces_reindex_root_iff

end RootedModel

end Concrete

end
