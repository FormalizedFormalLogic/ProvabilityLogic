module

public import SeqPL.Formula.Basic

@[expose]
public section

universe u
variable {α : Type u} [DecidableEq α]

structure Sequent (α : Type u) where
  ant : FormulaFinset α
  suc : FormulaFinset α

infix:50 " ⟹ " => Sequent.mk

inductive ProofGentzen : Sequent α → Type u
| axm (A) : ProofGentzen ({A} ⟹ {A})
| botL : ProofGentzen ({⊥} ⟹ (∅ : FormulaFinset α))
| wkL  {Γ Γ' Δ}  : ProofGentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : ProofGentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen (Γ ⟹ Δ')
| impL {Γ Δ A B} : ProofGentzen (Γ ⟹ (insert A Δ)) → ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹ (insert B Δ)) → ProofGentzen (Γ ⟹ (insert (A 🡒 B) Δ))
| boxGL {Γ A} : ProofGentzen ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) → ProofGentzen (Γ.box ⟹ {□A})
prefix:120 "⊢ᵍ! " => ProofGentzen


namespace ProofGentzen

variable {Γ Δ : FormulaFinset α} {A B C : Formula α}

def union (A) {Γ Δ : FormulaFinset α} (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ! (Γ ⟹ Δ) := wkR $ wkL $ axm A

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ! (Γ ⟹ Δ) := wkR (Δ := ∅) $ wkL botL

def mdpL_mem (A B) (h₁ : A 🡒 B ∈ Γ := by grind) (h₂ : A ∈ Γ := by grind) (h₃ : B ∈ Δ := by grind) : ⊢ᵍ! (Γ ⟹ Δ) := by
  rw [(show Γ = insert (A 🡒 B) (insert A (Γ \ {A, A 🡒 B})) by grind)];
  apply impL;
  . apply union A;
  . apply union B;


def negL : ⊢ᵍ! (Γ ⟹ (insert A Δ)) → ⊢ᵍ! ((insert (∼A) Γ) ⟹ Δ) := λ p => impL p (wkR $ wkL botL)

def negR : ⊢ᵍ! ((insert A Γ) ⟹ Δ) → ⊢ᵍ! (Γ ⟹ (insert (∼A) Δ)) := λ p => impR $ wkR $ wkL p

def andL : ⊢ᵍ! ((insert A $ insert B $ Γ) ⟹ Δ) → ⊢ᵍ! (insert (A ⋏ B) Γ ⟹ Δ) := λ p => by
  apply impL;
  . apply impR;
    apply negR;
    simpa [(show (insert A $ insert B Γ) = (insert B $ insert A Γ) by grind)] using p;
  . exact botL_mem;

def andR : ⊢ᵍ! (Γ ⟹ insert A Δ) → ⊢ᵍ! (Γ ⟹ insert B Δ) → ⊢ᵍ! (Γ ⟹ insert (A ⋏ B) Δ) := λ p q => by
  apply impR;
  apply impL;
  . exact wkR p;
  . exact negL $ wkR q;

def orL : ⊢ᵍ! (insert A Γ ⟹ Δ) → ⊢ᵍ! (insert B Γ ⟹ Δ) → ⊢ᵍ! (insert (A ⋎ B) Γ ⟹ Δ) := λ p q => by
  apply impL;
  . exact negR p;
  . exact q;

def orR : ⊢ᵍ! (Γ ⟹ (insert A $ insert B Δ)) → ⊢ᵍ! (Γ ⟹ insert (A ⋎ B) Δ) := λ p => by
  apply impR;
  apply negL;
  simpa;

def axiomŁ1 : ⊢ᵍ! (∅ ⟹ {A 🡒 B 🡒 A}) := impR (Δ := ∅) $ impR $ union A

def axiomŁ2 : ⊢ᵍ! (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := by
  apply impR (Δ := ∅);
  apply impR;
  apply impR;
  simp only [insert_empty_eq];
  rw [(show {A, A 🡒 B, A 🡒 B 🡒 C} = ({A 🡒 B 🡒 C, A 🡒 B, A}) by grind)];
  apply impL;
  . exact impL (union A) (union A);
  . exact impL (impL (union A) (union B)) (union C);

def axiomŁ3 : ⊢ᵍ! (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := by
  apply impR (Δ := ∅);
  apply impR;
  simp;
  rw [(show {B, ∼A 🡒 ∼B} = ({∼A 🡒 ∼B, B}) by grind)];
  exact impL (negR $ union A) (negL $ union B);

def axiomK : ⊢ᵍ! (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := by
  apply impR (Δ := ∅);
  apply impR;
  simp only [insert_empty_eq];
  rw [(show ({□A, □(A 🡒 B)}) = (FormulaFinset.box {A, (A 🡒 B)}) by grind)];
  apply boxGL;
  apply mdpL_mem A B;

def axiom4 : ⊢ᵍ! (∅ ⟹ {(□A 🡒 □□A)}) := by
  apply impR (Δ := ∅);
  simp only [insert_empty_eq];
  rw [(show ({□A}) = FormulaFinset.box {A} by grind)];
  apply boxGL;
  apply union (□A);

def axiomL : ⊢ᵍ! (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := by
  apply impR (Δ := ∅);
  simp only [insert_empty_eq];
  rw [(show ({□(□A 🡒 A)}) = FormulaFinset.box {□A 🡒 A} by grind)];
  apply boxGL;
  apply mdpL_mem (□A) A;

def ruleNec : ⊢ᵍ! (∅ ⟹ {A}) → ⊢ᵍ! (∅ ⟹ {□A}) := λ p => boxGL (Γ := ∅) $ wkL p

/-
#eval axiomŁ1 (A := #0) (B := #1)
#eval axiomŁ2 (A := #0) (B := #1) (C := #2)
#eval axiomŁ3 (A := #0) (B := #1)
#eval axiom4 (A := #0)
#eval axiomL (A := #0)
-/

end ProofGentzen



abbrev ProvableGentzen (S : Sequent α) : Prop := Nonempty (⊢ᵍ! S)
prefix:120 "⊢ᵍ " => ProvableGentzen

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B C : Formula α}

lemma axm (A : Formula α) : ⊢ᵍ ({A} ⟹ {A}) := ⟨ProofGentzen.axm A⟩
lemma union (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ (Γ ⟹ Δ) := ⟨ProofGentzen.union A hΓ hΔ⟩
lemma union' (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ S := union A hΓ hΔ
lemma botL : ⊢ᵍ ({⊥} ⟹ (∅ : FormulaFinset α)) := ⟨ProofGentzen.botL⟩
@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ (Γ ⟹ Δ) := ⟨ProofGentzen.botL_mem h⟩
@[grind =>] lemma botL_mem' (S : Sequent α) (h : ⊥ ∈ S.ant := by grind) : ⊢ᵍ S := botL_mem h
lemma wkL (π : ⊢ᵍ (Γ ⟹ Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ (Γ' ⟹ Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᵍ (Γ ⟹ Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ (Γ ⟹ Δ') := ⟨ProofGentzen.wkR π.some h⟩
lemma wk (π : ⊢ᵍ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᵍ (Γ' ⟹ Δ') := wkR (wkL π hΓ) hΔ
lemma impL (π₁ : ⊢ᵍ (Γ ⟹ insert A Δ)) (π₂ : ⊢ᵍ (insert B Γ ⟹ Δ)) : ⊢ᵍ ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᵍ ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍ (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩
lemma boxGL (π : ⊢ᵍ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : ⊢ᵍ (Γ.box ⟹ {□A}) := ⟨ProofGentzen.boxGL π.some⟩

lemma axiomŁ1 : ⊢ᵍ (∅ ⟹ {A 🡒 B 🡒 A}) := ⟨ProofGentzen.axiomŁ1⟩
lemma axiomŁ2 : ⊢ᵍ (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := ⟨ProofGentzen.axiomŁ2⟩
lemma axiomŁ3 : ⊢ᵍ (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := ⟨ProofGentzen.axiomŁ3⟩
lemma axiomK  : ⊢ᵍ (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := ⟨ProofGentzen.axiomK⟩
lemma axiom4  : ⊢ᵍ (∅ ⟹ {(□A 🡒 □□A)}) := ⟨ProofGentzen.axiom4⟩
lemma axiomL  : ⊢ᵍ (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := ⟨ProofGentzen.axiomL⟩
lemma ruleNec : ⊢ᵍ (∅ ⟹ {A}) → ⊢ᵍ (∅ ⟹ {□A}) := λ ⟨p⟩ => ⟨ProofGentzen.ruleNec p⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent α) → ⊢ᵍ S → Prop}
  (axm : ∀ A, motive ({A} ⟹ {A}) (ProvableGentzen.axm A))
  (botL : motive ({⊥} ⟹ (∅ : FormulaFinset α)) ProvableGentzen.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍ (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᵍ (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍ (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍ (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᵍ ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxGL : ∀ {Γ A} (h : ⊢ᵍ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) h → motive (Γ.box ⟹ {□A}) (boxGL h)
  )
  : ∀ {S : Sequent α} (h : ⊢ᵍ S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

prefix:120 "⊬ᵍ " => λ S => ¬⊢ᵍ S

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : Sequent α} : (⊬ᵍ S) ↔ (IsEmpty (⊢ᵍ! S)) := by simp [ProvableGentzen];

end ProvableGentzen

end
