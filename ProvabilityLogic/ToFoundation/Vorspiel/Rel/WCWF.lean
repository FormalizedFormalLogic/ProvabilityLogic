module

public import ProvabilityLogic.ToFoundation.Vorspiel.Rel.CWF

/-!
# Weakly converse well-founded relations

`Rel.IrreflGen` and `WeaklyConverseWellFounded`, the frame condition of the Kripke
semantics of `Grz`, together with the instances relating them to transitivity and
antisymmetry. Ported from the sibling repository `FormalizedFormalLogic/ModalLogic`,
since Foundation does not provide them.
-/

@[expose]
public section

/-- The irreflexive part of a relation. -/
def Rel.IrreflGen (r : Rel α α) : Rel α α := fun x y => r x y ∧ x ≠ y

@[simp, grind =]
lemma Rel.irreflGen_iff {r : Rel α α} {x y : α} : r.IrreflGen x y ↔ r x y ∧ x ≠ y := Iff.rfl

/-- Every nonempty set has a maximal element with respect to `r.IrreflGen`. This is the
frame condition of the modal logic `Grz`. -/
abbrev WeaklyConverseWellFounded {α} (rel : Rel α α) := ConverseWellFounded rel.IrreflGen

class IsWeaklyConverseWellFounded (α) (rel : Rel α α) : Prop where wcwf : WeaklyConverseWellFounded rel

section

variable {α} {r : Rel α α}

lemma WeaklyConverseWellFounded.has_max [IsWeaklyConverseWellFounded α r] (s : Set α) (hs : s.Nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, ¬(r m x ∧ m ≠ x) :=
  ConverseWellFounded.iff_has_max.mp IsWeaklyConverseWellFounded.wcwf s hs

instance : Std.Irrefl r.IrreflGen := ⟨fun _ h => h.2 rfl⟩

-- `IsTrans r` alone does not suffice: `x ≠ y`, `y ≠ z` and `r x z` do not rule out `x = z`;
-- antisymmetry is what rules that out.
instance [IsTrans α r] [Std.Antisymm r] : IsTrans α r.IrreflGen where
  trans a b c hab hbc := by
    obtain ⟨rab, hab'⟩ := hab;
    obtain ⟨rbc, hbc'⟩ := hbc;
    exact ⟨IsTrans.trans a b c rab rbc,
      by rintro rfl; exact hab' (Std.Antisymm.antisymm a b rab rbc)⟩;

instance [Finite α] [IsTrans α r] [Std.Antisymm r] : IsWeaklyConverseWellFounded α r :=
  ⟨Finite.converseWellFounded_of_trans_of_irrefl (R := r.IrreflGen)⟩

lemma WeaklyConverseWellFounded.antisymm (h : WeaklyConverseWellFounded r) :
  ∀ a b, r a b → r b a → a = b := by
  intro a b rab rba;
  by_contra hne;
  obtain ⟨m, hm, hmax⟩ := ConverseWellFounded.iff_has_max.mp h {a, b} ⟨a, by simp⟩;
  rcases hm with (rfl | rfl);
  . exact hmax b (by simp) ⟨rab, hne⟩;
  . exact hmax a (by simp) ⟨rba, Ne.symm hne⟩;

end
