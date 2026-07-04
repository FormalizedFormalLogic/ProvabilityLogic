module

public import SeqPL.Formula.Letterless
public import SeqPL.Formula.Substitution
public import SeqPL.Hilbert.Basic

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

/-- Hilbert provability is preserved under renaming of atoms. -/
lemma ProvableHilbert.map (f : α → β) {A : Formula α} (h : ⊢ʰ A) : ⊢ʰ (A.map f) := by
  induction h using ProvableHilbert.rec with
  | implyK => exact ProvableHilbert.implyK
  | implyS => exact ProvableHilbert.implyS
  | dne => exact ProvableHilbert.dne
  | andElimL => exact ProvableHilbert.andElimL
  | andElimR => exact ProvableHilbert.andElimR
  | andIntro => exact ProvableHilbert.andIntro
  | orIntroL => exact ProvableHilbert.orIntroL
  | orIntroR => exact ProvableHilbert.orIntroR
  | orElim => exact ProvableHilbert.orElim
  | modalK => exact ProvableHilbert.modalK
  | modal4 => exact ProvableHilbert.modal4
  | modalL => exact ProvableHilbert.modalL
  | mdp h₁ h₂ ih₁ ih₂ => exact ProvableHilbert.mdp ih₁ ih₂
  | nec h ih => exact ProvableHilbert.nec ih
