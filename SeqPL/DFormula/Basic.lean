module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Basic

@[expose]
public section

variable {α : Type*}

@[grind]
inductive DFormula (α : Type*)
| patom : α → DFormula α
| natom : α → DFormula α
| top   : DFormula α
| bot   : DFormula α
| and   : DFormula α → DFormula α → DFormula α
| or    : DFormula α → DFormula α → DFormula α
| box   : DFormula α → DFormula α
| dia   : DFormula α → DFormula α
deriving Repr, DecidableEq

namespace DFormula

prefix:100 "♯" => patom
prefix:100 "♭" => natom

notation:max "⊤" => top
notation:max "⊥" => bot
infixl:84 " ⋏ " => and
infixl:83 " ⋎ " => or
prefix:95 "□" => box
prefix:95 "◇" => dia

variable {A B : DFormula α}

@[grind]
def neg : DFormula α → DFormula α
| ♯a => ♭a
| ♭a => ♯a
| ⊤ => ⊥
| ⊥ => ⊤
| A ⋏ B => A.neg ⋎ B.neg
| A ⋎ B => A.neg ⋏ B.neg
| □A => ◇(A.neg)
| ◇A => □(A.neg)
prefix:90 "∼" => neg

@[simp, grind =]
lemma eq_negneg : ∼∼A = A := by induction A <;> grind;

abbrev imp (A B : DFormula α) : DFormula α := ∼A ⋎ B
infixr:85 " 🡒 " => imp

abbrev iff (A B : DFormula α) : DFormula α := (A 🡒 B) ⋏ (B 🡒 A)

end DFormula

abbrev DFormulaList (α : Type*) := List (DFormula α)

abbrev DFormulaFinset (α : Type*) := Finset (DFormula α)


end
