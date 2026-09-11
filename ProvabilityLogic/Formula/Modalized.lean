module

public import ProvabilityLogic.Formula.Substitution

/-!
# Modalized formulas

Syntactic notions around *modalization* of a `Formula`: an atom being modalized in a
formula, a formula all of whose atoms are modalized, and the operation replacing every
non-modalized atom by `⊥`.

## References

- [SV82]
- [Bek89, Lemma 11]
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace Formula

variable {p q : α} {A B C : Formula α}

/-- `p` occurs only in the scope of `□` in `A` (termed "`p` is modalized in `A`" in the
source). -/
@[grind]
def ModalizedIn (p : α) : Formula α → Prop
  | #a    => a ≠ p
  | ⊥     => True
  | A 🡒 B => A.ModalizedIn p ∧ B.ModalizedIn p
  | □_    => True

lemma ModalizedIn.of_not_mem_atoms (h : p ∉ A.atoms) : A.ModalizedIn p := by
  induction A <;> grind [atoms];

omit [DecidableEq α] in
@[simp] lemma ModalizedIn.box : (□A).ModalizedIn p := by simp [ModalizedIn];

lemma ModalizedIn.subst_single (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
  (A⟦p ↦ #q⟧).ModalizedIn q := by
  induction A <;> grind [atoms, ModalizedIn];

abbrev Modalized (A : Formula α) : Prop := ∀ a, A.ModalizedIn a

/-- Replace every unboxed atom of `A` by `⊥`, keeping the maximal boxed subformulas: turns
`f(□C₁, …, □Cₙ, p₁, …, pₘ)` into `f(□C₁, …, □Cₙ, ⊥, …, ⊥)`.

- [Bek89, Lemma 11]
-/
@[grind]
def modalize : Formula α → Formula α
  | #_    => ⊥
  | ⊥     => ⊥
  | A 🡒 B => A.modalize 🡒 B.modalize
  | □A    => □A

omit [DecidableEq α] in
@[simp, grind .]
lemma modalized_modalize : A.modalize.Modalized := by
  intro a; induction A <;> grind;

@[simp, grind .]
lemma atoms_modalize_subset : A.modalize.atoms ⊆ A.atoms := by
  induction A <;> grind;

end Formula
