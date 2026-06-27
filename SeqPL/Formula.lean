module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Basic

@[expose]
public section

variable {α : Type*}

inductive Formula (α : Type*)
| atom : α → Formula α
| bot  : Formula α
| imp  : Formula α → Formula α → Formula α
| box  : Formula α → Formula α
deriving Repr, DecidableEq

namespace Formula

variable {A B : Formula α}

prefix:100 "#" => atom
notation:max "⊥" => bot
infixr:85 " 🡒 " => imp
prefix:95 "□" => box

abbrev neg (A : Formula α) : Formula α := A 🡒 ⊥
prefix:90 "∼" => neg

abbrev or (A B : Formula α) : Formula α := ∼A 🡒 B
infixl:83 " ⋎ " => or

abbrev and (A B : Formula α) : Formula α := ∼(A 🡒 ∼B)
infixl:84 " ⋏ " => and

abbrev iff (A B : Formula α) : Formula α := (A 🡒 B) ⋏ (B 🡒 A)
infix:85 " 🡘 " => iff

abbrev top : Formula α := ∼⊥
notation:max "⊤" => top

abbrev dia (A : Formula α) : Formula α := ∼□(∼A)
prefix:95 "◇" => dia

@[grind]
def boxItr (A : Formula α) (n : ℕ) : Formula α := match n with
  | 0 => A
  | n + 1 => □(boxItr A n)
notation:95 "□^[" n "]" A:max => boxItr A n

@[grind =_]
lemma boxItr_one : (□^[1]A) = □A := by grind;

lemma boxItr_comp {n m : ℕ} : (□^[n + m]A) = □^[n](□^[m]A) := by
  induction n generalizing A <;> grind;

@[grind]
def diaItr (A : Formula α) (n : ℕ) : Formula α := match n with
  | 0 => A
  | n + 1 => ◇(diaItr A n)
notation:95 "◇^[" n "]" A:max => diaItr A n

@[grind =_]
lemma diaItr_one : (◇^[1]A) = ◇A := by grind;

lemma diaItr_comp {n m : ℕ} : (◇^[n + m]A) = ◇^[n](◇^[m]A) := by
  induction n generalizing A <;> grind;

abbrev boxdot (A : Formula α) : Formula α := A ⋏ □A
prefix:95 "⊡" => boxdot

@[grind]
def IsBox : Formula α → Prop
| □_ => True
| _ => False

instance : DecidablePred (Formula.IsBox (α := α)) := λ A => by
  cases A;
  case box => exact isTrue $ by grind;
  case atom | bot | imp => exact isFalse $ by grind;

end Formula


abbrev FormulaList (α) := List $ Formula α

namespace FormulaList

protected def conj : FormulaList α → Formula α
| [] => ⊤
| [A] => A
| A :: B :: Γ  => A ⋏ FormulaList.conj (B :: Γ)
prefix:100 "⋀" => FormulaList.conj

@[simp, grind .] lemma conj_nil : FormulaList.conj (α := α) [] = ⊤ := rfl
@[simp, grind .] lemma conj_singleton : FormulaList.conj [A] = A := rfl

protected def disj : FormulaList α → Formula α
| [] => ⊥
| [A] => A
| A :: B :: Γ  => A ⋎ FormulaList.disj (B :: Γ)
prefix:100 "⋁" => FormulaList.disj

@[simp, grind .] lemma disj_nil : FormulaList.disj (α := α) [] = ⊥ := rfl
@[simp, grind .] lemma disj_singleton : FormulaList.disj [A] = A := rfl

end FormulaList


abbrev FormulaFinset (α) := Finset (Formula α)

namespace FormulaFinset

protected noncomputable def conj : FormulaFinset α → Formula α := FormulaList.conj ∘ Finset.toList
prefix:100 "⋀" => FormulaFinset.conj

@[simp, grind .] lemma conj_empty : FormulaFinset.conj (α := α) ∅ = ⊤ := by simp [FormulaFinset.conj]
@[simp, grind .] lemma conj_singleton : FormulaFinset.conj ({A} : FormulaFinset α) = A := by simp [FormulaFinset.conj]


protected noncomputable def disj : FormulaFinset α → Formula α := FormulaList.disj ∘ Finset.toList
prefix:100 "⋁" => FormulaFinset.disj

@[simp, grind .] lemma disj_empty : FormulaFinset.disj (α := α) ∅ = ⊥ := by simp [FormulaFinset.disj]
@[simp, grind .] lemma disj_singleton : FormulaFinset.disj ({A} : FormulaFinset α) = A := by simp [FormulaFinset.disj]


abbrev box [DecidableEq α] (Γ : FormulaFinset α) : FormulaFinset α := Γ.image (□·)

end FormulaFinset


abbrev FormulaSet (α) := Set (Formula α)


end
