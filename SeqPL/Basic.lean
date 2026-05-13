module

public import Mathlib

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

end Formula

abbrev FormulaFinset := Finset Formula

abbrev FormulaFinset.box (Γ : FormulaFinset) : FormulaFinset := Γ.image (□·)

structure Sequent where
  ant : FormulaFinset
  suc : FormulaFinset

infix:50 " ⟹ " => Sequent.mk

inductive Proof : Sequent → Type
| axm (A) : Proof ({A} ⟹ {A})
| botL : Proof ({⊥} ⟹ ∅)
| wkL  {Γ Γ' Δ}  : Proof (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → Proof (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : Proof (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → Proof (Γ ⟹ Δ')
| impL {Γ Δ A B} : Proof (Γ ⟹ (insert A Δ)) → Proof (insert B Γ ⟹ Δ) → Proof ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : Proof ((insert A Γ) ⟹ (insert B Δ)) → Proof (Γ ⟹ (insert (A 🡒 B) Δ))
| boxGL {Γ A} : Proof ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) → Proof (Γ.box ⟹ {□A})

prefix:120 "⊢! " => Proof

namespace Proof

variable {Γ Δ : FormulaFinset} {A B C : Formula}

def union (A) {Γ Δ : Finset _} (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢! (Γ ⟹ Δ) := wkR $ wkL $ axm A

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢! (Γ ⟹ Δ) := wkR (Δ := ∅) $ wkL botL

def mdpL_mem (A B) (h₁ : A 🡒 B ∈ Γ := by grind) (h₂ : A ∈ Γ := by grind) (h₃ : B ∈ Δ := by grind) : ⊢! (Γ ⟹ Δ) := by
  rw [(show Γ = insert (A 🡒 B) (insert A (Γ \ {A, A 🡒 B})) by grind)];
  apply impL;
  . apply union A;
  . apply union B;


def negL : ⊢! (Γ ⟹ (insert A Δ)) → ⊢! ((insert (∼A) Γ) ⟹ Δ) := λ p => impL p (wkR $ wkL botL)

def negR : ⊢! ((insert A Γ) ⟹ Δ) → ⊢! (Γ ⟹ (insert (∼A) Δ)) := λ p => impR $ wkR $ wkL p

def andL : ⊢! ((insert A $ insert B $ Γ) ⟹ Δ) → ⊢! (insert (A ⋏ B) Γ ⟹ Δ) := λ p => by
  apply impL;
  . apply impR;
    apply negR;
    simpa [(show (insert A $ insert B Γ) = (insert B $ insert A Γ) by grind)] using p;
  . exact botL_mem;

def andR : ⊢! (Γ ⟹ insert A Δ) → ⊢! (Γ ⟹ insert B Δ) → ⊢! (Γ ⟹ insert (A ⋏ B) Δ) := λ p q => by
  apply impR;
  apply impL;
  . exact wkR p;
  . exact negL $ wkR q;

def orL : ⊢! (insert A Γ ⟹ Δ) → ⊢! (insert B Γ ⟹ Δ) → ⊢! (insert (A ⋎ B) Γ ⟹ Δ) := λ p q => by
  apply impL;
  . exact negR p;
  . exact q;

def orR : ⊢! (Γ ⟹ (insert A $ insert B Δ)) → ⊢! (Γ ⟹ insert (A ⋎ B) Δ) := λ p => by
  apply impR;
  apply negL;
  simpa;


def axiomŁ1 : ⊢! (∅ ⟹ {A 🡒 B 🡒 A}) := impR (Δ := ∅) $ impR $ union A

def axiomŁ2 : ⊢! (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := by
  apply impR (Δ := ∅);
  apply impR;
  apply impR;
  simp only [insert_empty_eq];
  rw [(show {A, A 🡒 B, A 🡒 B 🡒 C} = ({A 🡒 B 🡒 C, A 🡒 B, A}) by grind)];
  apply impL;
  . exact impL (union A) (union A);
  . exact impL (impL (union A) (union B)) (union C);

def axiomŁ3 : ⊢! (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := by
  apply impR (Δ := ∅);
  apply impR;
  simp;
  rw [(show {B, ∼A 🡒 ∼B} = ({∼A 🡒 ∼B, B}) by grind)];
  exact impL (negR $ union A) (negL $ union B);

def axiomK : ⊢! (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := by
  apply impR (Δ := ∅);
  apply impR;
  simp only [insert_empty_eq];
  rw [(show ({□A, □(A 🡒 B)}) = (FormulaFinset.box {A, (A 🡒 B)}) by grind)];
  apply boxGL;
  apply mdpL_mem A B;

def axiom4 : ⊢! (∅ ⟹ {(□A 🡒 □□A)}) := by
  apply impR (Δ := ∅);
  simp only [insert_empty_eq];
  rw [(show ({□A}) = FormulaFinset.box {A} by grind)];
  apply boxGL;
  apply union (□A);

def axiomL : ⊢! (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := by
  apply impR (Δ := ∅);
  simp only [insert_empty_eq];
  rw [(show ({□(□A 🡒 A)}) = FormulaFinset.box {□A 🡒 A} by grind)];
  apply boxGL;
  apply mdpL_mem (□A) A;

def ruleNec : ⊢! (∅ ⟹ {A}) → ⊢! (∅ ⟹ {□A}) := λ p => boxGL (Γ := ∅) $ wkL p

#eval axiomŁ1 (A := #0) (B := #1)
#eval axiomŁ2 (A := #0) (B := #1) (C := #2)
#eval axiomŁ3 (A := #0) (B := #1)
#eval axiom4 (A := #0)
#eval axiomL (A := #0)

end Proof



abbrev Provable (S : Sequent) : Prop := Nonempty (⊢! S)
prefix:120 "⊢ " => Provable

namespace Provable

variable {Γ Δ : FormulaFinset} {A B C : Formula}

lemma axiomŁ1 : ⊢ (∅ ⟹ {A 🡒 B 🡒 A}) := ⟨Proof.axiomŁ1⟩
lemma axiomŁ2 : ⊢ (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := ⟨Proof.axiomŁ2⟩
lemma axiomŁ3 : ⊢ (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := ⟨Proof.axiomŁ3⟩
lemma axiomK  : ⊢ (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := ⟨Proof.axiomK⟩
lemma axiom4  : ⊢ (∅ ⟹ {(□A 🡒 □□A)}) := ⟨Proof.axiom4⟩
lemma axiomL  : ⊢ (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := ⟨Proof.axiomL⟩
lemma ruleNec : ⊢ (∅ ⟹ {A}) → ⊢ (∅ ⟹ {□A}) := λ ⟨p⟩ => ⟨Proof.ruleNec p⟩

end Provable
