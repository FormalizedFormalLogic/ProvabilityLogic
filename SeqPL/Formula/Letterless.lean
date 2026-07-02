module

public import SeqPL.Formula.Basic

@[expose]
public section

namespace Formula

abbrev Substitution (α) := α → Formula α

@[grind]
def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | □φ      => □(φ.subst s)
  | φ 🡒 ψ   => φ.subst s 🡒 ψ.subst s
notation:95 φ "⟦" s "⟧" => Formula.subst s φ

variable {s : Substitution α} {A B : Formula α}

lemma subst_atom : (#a)⟦s⟧ = s a := by grind;
lemma subst_bot : (⊥)⟦s⟧ = ⊥ := by grind;
lemma subst_top : (⊤)⟦s⟧ = ⊤ := by grind;
lemma subst_imp : (A 🡒 B)⟦s⟧ = A⟦s⟧ 🡒 B⟦s⟧ := by rfl
lemma subst_and : (A ⋏ B)⟦s⟧ = A⟦s⟧ ⋏ B⟦s⟧ := by grind;
lemma subst_or  : (A ⋎ B)⟦s⟧ = A⟦s⟧ ⋎ B⟦s⟧ := by grind;
lemma subst_neg : (∼A)⟦s⟧ = ∼(A⟦s⟧) := by grind;
lemma subst_iff : (A 🡘 B)⟦s⟧ = A⟦s⟧ 🡘 B⟦s⟧ := by grind;
attribute [simp, grind =]
  subst_atom
  subst_bot
  subst_top
  subst_neg
  subst_and
  subst_or
  subst_imp
  subst_iff
@[simp, grind =] lemma subst_box : (□A)⟦s⟧ = □(A⟦s⟧) := by grind;
@[simp, grind =] lemma subst_boxItr {n : ℕ} : (□^[n]A)⟦s⟧ = □^[n](A⟦s⟧) := by induction n generalizing A <;> grind;
@[simp, grind =] lemma subst_dia : (◇A)⟦s⟧ = ◇(A⟦s⟧) := by grind;
@[simp, grind =] lemma subst_diaItr {n : ℕ} : (◇^[n]A)⟦s⟧ = ◇^[n](A⟦s⟧) := by induction n generalizing A <;> grind;

@[simp, grind =]
lemma subst_lconj {Γ : FormulaList α} : (⋀Γ)⟦s⟧ = ⋀(Γ.map (·⟦s⟧)) := by
  match Γ with
  | [] => simp;
  | [A] => simp;
  | A :: B :: Γ => simp [FormulaList.conj, subst_lconj (Γ := B :: Γ)];

end Formula


variable {α : Type*}

abbrev LetterlessFormula := Formula Empty

namespace LetterlessFormula

variable {A : LetterlessFormula}

@[grind]
def lift : LetterlessFormula → Formula α
  | ⊥ => ⊥
  | A 🡒 B => lift A 🡒 lift B
  | □A => □(lift A)
instance : Coe LetterlessFormula (Formula α) := ⟨lift⟩

@[simp, grind =] lemma eq_subst_self : A⟦s⟧ = A := by induction A <;> grind;

/-- Substitution acts trivially on lifted letterless formulas. -/
@[simp, grind =]
lemma subst_lift {s : Formula.Substitution α} : (lift A : Formula α)⟦s⟧ = lift A := by
  induction A <;> grind;

end LetterlessFormula


abbrev LetterlessFormulaList := FormulaList Empty

abbrev LetterlessFormulaFinset := FormulaFinset Empty

namespace LetterlessFormulaFinset

def lift [DecidableEq α] : LetterlessFormulaFinset → FormulaFinset α := λ Γ => Γ.image (LetterlessFormula.lift)
instance [DecidableEq α] : Coe LetterlessFormulaFinset (FormulaFinset α) := ⟨lift⟩

end LetterlessFormulaFinset


abbrev LetterlessFormulaSet := FormulaSet Empty

namespace LetterlessFormulaSet

def lift : LetterlessFormulaSet → FormulaSet α := λ Γ => Γ.image (LetterlessFormula.lift)
instance : Coe LetterlessFormulaSet (FormulaSet α) := ⟨lift⟩

end LetterlessFormulaSet


namespace Formula

def Letterless : Formula α → Prop
  | #_ => False
  | ⊥ => True
  | A 🡒 B => A.Letterless ∧ B.Letterless
  | □A => A.Letterless

def toLetterless : (A : Formula α) → (_ : Letterless A) → LetterlessFormula
  | ⊥, _ => ⊥
  | A 🡒 B, ⟨hA, hB⟩ => toLetterless A hA 🡒 toLetterless B hB
  | □A, hA => □(toLetterless A hA)

end Formula



end
