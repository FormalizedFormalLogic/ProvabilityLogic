module

public import SeqPL.Formula.Substitution

@[expose]
public section

variable {α β γ : Type*}

namespace Formula

/-- Renaming of propositional atoms along a function. -/
@[grind]
def map (f : α → β) : Formula α → Formula β
  | #a => #(f a)
  | ⊥ => ⊥
  | A 🡒 B => A.map f 🡒 B.map f
  | □A => □(A.map f)

variable {f : α → β} {A B : Formula α}

@[simp, grind =] lemma map_atom {a : α} : (#a : Formula α).map f = #(f a) := rfl
@[simp, grind =] lemma map_bot : (⊥ : Formula α).map f = ⊥ := rfl
@[simp, grind =] lemma map_imp : (A 🡒 B).map f = A.map f 🡒 B.map f := rfl
@[simp, grind =] lemma map_box : (□A).map f = □(A.map f) := rfl
@[simp, grind =] lemma map_neg : (∼A).map f = ∼(A.map f) := rfl
@[simp, grind =] lemma map_and : (A ⋏ B).map f = A.map f ⋏ B.map f := rfl
@[simp, grind =] lemma map_or : (A ⋎ B).map f = A.map f ⋎ B.map f := rfl

@[simp, grind =]
lemma map_boxItr {n : ℕ} : (□^[n]A).map f = □^[n](A.map f) := by
  induction n generalizing A <;> grind

lemma map_map {g : β → γ} : (A.map f).map g = A.map (g ∘ f) := by
  induction A <;> grind

@[simp, grind =]
lemma map_id : A.map id = A := by
  induction A <;> grind

@[simp, grind =]
lemma atoms_map [DecidableEq α] [DecidableEq β] : (A.map f).atoms = A.atoms.image f := by
  induction A with
  | atom a => simp [Formula.atoms, map];
  | bot => simp [Formula.atoms, map];
  | imp A B ihA ihB => simp [Formula.atoms, map, ihA, ihB, Finset.image_union];
  | box A ih => simpa [Formula.atoms, map] using ih;

/-- A substitution acting as the identity on the atoms of `A` leaves `A` unchanged. -/
lemma subst_eq_self_of_forall_atoms [DecidableEq α] {s : Substitution α}
    (h : ∀ a ∈ A.atoms, s a = #a) : A⟦s⟧ = A := by
  induction A with
  | atom a => exact h a (by simp [Formula.atoms]);
  | bot => rfl;
  | imp A B ihA ihB =>
    rw [Formula.subst_imp, ihA (fun a ha => h a (by simp [Formula.atoms, ha])),
      ihB (fun a ha => h a (by simp [Formula.atoms, ha]))];
  | box A ih =>
    rw [Formula.subst_box, ih (fun a ha => h a (by simpa [Formula.atoms] using ha))];

end Formula


namespace Formula

/-- Substitution across atom types: each atom of `A` is replaced by a formula over `β`,
following `g`. Unlike `subst`, which stays within a single type `α`, `bind` allows the
target type `β` to differ, so that `A` (over an arbitrary alphabet `α`, e.g. `ℕ`) can be
turned into a formula over any `β` without needing `β` itself to carry designated atoms. -/
@[grind]
def bind (g : α → Formula β) : Formula α → Formula β
  | #a => g a
  | ⊥ => ⊥
  | A 🡒 B => A.bind g 🡒 B.bind g
  | □A => □(A.bind g)

variable {g : α → Formula β} {A B : Formula α}

@[simp, grind =] lemma bind_atom {a : α} : (#a : Formula α).bind g = g a := rfl
@[simp, grind =] lemma bind_bot : (⊥ : Formula α).bind g = ⊥ := rfl
@[simp, grind =] lemma bind_imp : (A 🡒 B).bind g = A.bind g 🡒 B.bind g := rfl
@[simp, grind =] lemma bind_box : (□A).bind g = □(A.bind g) := rfl
@[simp, grind =] lemma bind_neg : (∼A).bind g = ∼(A.bind g) := by grind;
@[simp, grind =] lemma bind_and : (A ⋏ B).bind g = A.bind g ⋏ B.bind g := by grind;
@[simp, grind =] lemma bind_or  : (A ⋎ B).bind g = A.bind g ⋎ B.bind g := by grind;

end Formula
