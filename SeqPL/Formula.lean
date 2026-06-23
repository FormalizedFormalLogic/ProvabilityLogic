module

public import Mathlib

@[expose]
public section

inductive Formula
| atom : ℕ → Formula
| bot  : Formula
| imp  : Formula → Formula → Formula
| box  : Formula → Formula
deriving Repr, DecidableEq

namespace Formula

prefix:100 "#" => atom
notation:90 "⊥" => bot
infixr:85 " 🡒 " => imp
prefix:95 "□" => box

abbrev neg (A : Formula) : Formula := A 🡒 ⊥
prefix:90 "∼" => neg

abbrev or (A B : Formula) : Formula := ∼A 🡒 B
infixl:83 " ⋎ " => or

abbrev and (A B : Formula) : Formula := ∼(A 🡒 ∼B)
infixl:84 " ⋏ " => and

def top : Formula := ∼⊥
notation "⊤" => top


@[grind]
def IsBox : Formula → Prop
| □_ => True
| _ => False

instance : DecidablePred Formula.IsBox := λ A => by
  cases A;
  case box => exact isTrue $ by grind;
  case atom | bot | imp => exact isFalse $ by grind;

end Formula


abbrev FormulaList := List Formula

namespace FormulaList

protected def conj : FormulaList → Formula
| [] => ⊤
| [A] => A
| A :: B :: Γ  => A ⋏ FormulaList.conj (B :: Γ)
prefix:100 "⋀" => FormulaList.conj

@[simp, grind .] lemma conj_nil : FormulaList.conj [] = ⊤ := rfl
@[simp, grind .] lemma conj_singleton : FormulaList.conj [A] = A := rfl

protected def disj : FormulaList → Formula
| [] => ⊥
| [A] => A
| A :: B :: Γ  => A ⋎ FormulaList.disj (B :: Γ)
prefix:100 "⋁" => FormulaList.disj

@[simp, grind .] lemma disj_nil : FormulaList.disj [] = ⊥ := rfl
@[simp, grind .] lemma disj_singleton : FormulaList.disj [A] = A := rfl

end FormulaList


abbrev FormulaFinset := Finset Formula

namespace FormulaFinset

protected noncomputable def conj : FormulaFinset → Formula := FormulaList.conj ∘ Finset.toList
prefix:100 "⋀" => FormulaFinset.conj

@[simp, grind .] lemma conj_empty : FormulaFinset.conj ∅ = ⊤ := by simp [FormulaFinset.conj]
@[simp, grind .] lemma conj_singleton : FormulaFinset.conj {A} = A := by simp [FormulaFinset.conj]


protected noncomputable def disj : FormulaFinset → Formula := FormulaList.disj ∘ Finset.toList
prefix:100 "⋁" => FormulaFinset.disj

@[simp, grind .] lemma disj_empty : FormulaFinset.disj ∅ = ⊥ := by simp [FormulaFinset.disj]
@[simp, grind .] lemma disj_singleton : FormulaFinset.disj {A} = A := by simp [FormulaFinset.disj]


abbrev box (Γ : FormulaFinset) : FormulaFinset := Γ.image (□·)

end FormulaFinset

end
