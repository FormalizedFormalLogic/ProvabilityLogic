module

public import ProvabilityLogic.ToFoundation.Vorspiel.Rel.CWF

/-!
This file ports `Rel.IrreflGen`, `WeaklyConverseWellFounded` and
`IsWeaklyConverseWellFounded` from the sibling repository
`FormalizedFormalLogic/ModalLogic` (`ModalLogicArchive/Vorspiel/Rel/Basic.lean` and
`ModalLogicArchive/Vorspiel/Rel/WCWF.lean`), which are not available from Foundation
but are needed for the Kripke semantics of Grz.
-/

@[expose]
public section

/-- The irreflexive part of a relation. -/
def Rel.IrreflGen (r : Rel α α) : Rel α α := fun x y => r x y ∧ x ≠ y

/-- Unfolding lemma for `Rel.IrreflGen`. -/
@[simp, grind =]
lemma Rel.irreflGen_iff {r : Rel α α} {x y : α} : r.IrreflGen x y ↔ r x y ∧ x ≠ y := Iff.rfl

/-- A relation is weakly converse well-founded if the converse of its irreflexive part is
well-founded, i.e. every nonempty set has a maximal element with respect to `r.IrreflGen`.
This is the semantic frame condition of the modal logic `Grz`. -/
abbrev WeaklyConverseWellFounded {α} (rel : Rel α α) := ConverseWellFounded rel.IrreflGen

/-- Typeclass wrapper around `WeaklyConverseWellFounded`, for use as a `Model` frame
condition. -/
class IsWeaklyConverseWellFounded (α) (rel : Rel α α) : Prop where wcwf : WeaklyConverseWellFounded rel

section

variable {α} {r : Rel α α}

/-- Every nonempty subset of a weakly converse well-founded relation has an element that is
maximal with respect to the irreflexive part of the relation. -/
lemma WeaklyConverseWellFounded.has_max [IsWeaklyConverseWellFounded α r] (s : Set α) (hs : s.Nonempty) :
    ∃ m ∈ s, ∀ x ∈ s, ¬(r m x ∧ m ≠ x) :=
  ConverseWellFounded.iff_has_max.mp IsWeaklyConverseWellFounded.wcwf s hs

instance : Std.Irrefl r.IrreflGen := ⟨fun _ h => h.2 rfl⟩

-- `IsTrans r` alone does not suffice: `x ≠ y`, `y ≠ z` and `r x z` do not rule out `x = z`;
-- antisymmetry is what rules that out.
/-- The irreflexive part of a transitive antisymmetric relation is transitive. -/
instance [IsTrans α r] [Std.Antisymm r] : IsTrans α r.IrreflGen where
  trans a b c hab hbc := by
    obtain ⟨rab, hab'⟩ := hab;
    obtain ⟨rbc, hbc'⟩ := hbc;
    refine ⟨IsTrans.trans a b c rab rbc, ?_⟩;
    rintro rfl;
    exact hab' (Std.Antisymm.antisymm a b rab rbc);

/-- On a finite type, a transitive antisymmetric relation is weakly converse well-founded:
its irreflexive part is transitive and irreflexive, hence converse well-founded by
`Finite.converseWellFounded_of_trans_of_irrefl`. -/
instance [Finite α] [IsTrans α r] [Std.Antisymm r] : IsWeaklyConverseWellFounded α r :=
  ⟨Finite.converseWellFounded_of_trans_of_irrefl (R := r.IrreflGen)⟩

/-- A weakly converse well-founded relation is antisymmetric: if `r a b` and `r b a` with
`a ≠ b`, then `{a, b}` has no maximal element with respect to `r.IrreflGen`, contradicting
weak converse well-foundedness.

This direction is not consumed elsewhere in the repository; kept for parity with the
sibling repository. -/
lemma WeaklyConverseWellFounded.antisymm (h : WeaklyConverseWellFounded r) :
    ∀ a b, r a b → r b a → a = b := by
  intro a b rab rba;
  by_contra hne;
  obtain ⟨m, hm, hmax⟩ := ConverseWellFounded.iff_has_max.mp h {a, b} ⟨a, by simp⟩;
  rcases hm with (rfl | rfl);
  · exact hmax b (by simp) ⟨rab, hne⟩;
  · exact hmax a (by simp) ⟨rba, Ne.symm hne⟩;

end
