module

public import ProvabilityLogic.Gentzen.GL.Basic

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace LogicGrz

open LogicGL
open scoped FormulaFinset

/--
Cut-free Gentzen sequent calculus `GrzSeq` for the Grzegorczyk logic `Grz`.

Besides the propositional rules shared with `LogicGL.ProofGentzen`, two modal rules are added:
- `boxT`: the reflexivity (`T`) rule, allowing `B` to be assumed once `□B` sits in the
  antecedent.
- `boxGrz`: the Grz box-right rule. Its conclusion's antecedent must be exactly a boxed
  finset `□Γ` and its succedent must be exactly the singleton `{□A}`; side formulas are
  recovered afterwards via `wkL`/`wkR`. The source rule bakes side formulas into the rule
  itself, but we follow the more economical presentation already used for
  `LogicGL.ProofGentzen.boxGL`, adding weakening explicitly instead.
- [SS21, Figure 1]
- [Avr84, §I]
-/
inductive ProofGentzen : Sequent α → Type u
| axm (A) : ProofGentzen ({A} ⟹ {A})
| botL : ProofGentzen ({⊥} ⟹ (∅ : FormulaFinset α))
| wkL  {Γ Γ' Δ}  : ProofGentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : ProofGentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen (Γ ⟹ Δ')
| impL {Γ Δ A B} : ProofGentzen (Γ ⟹ (insert A Δ)) → ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹ (insert B Δ)) → ProofGentzen (Γ ⟹ (insert (A 🡒 B) Δ))
| boxT   {Γ Δ : FormulaFinset α} {B} : ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen (insert (□B) Γ ⟹ Δ)
| boxGrz {Γ : FormulaFinset α} {A}   : ProofGentzen (insert (□(A 🡒 □A)) (□Γ) ⟹ {A}) → ProofGentzen (□Γ ⟹ {□A})
notation:120 "⊢ᵍ[Grz]! " S:121 => ProofGentzen S


namespace ProofGentzen

variable {Γ Δ : FormulaFinset α} {A B C : Formula α}

def union (A) {Γ Δ : FormulaFinset α} (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[Grz]! (Γ ⟹ Δ) := wkR $ wkL $ axm A

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[Grz]! (Γ ⟹ Δ) := wkR (Δ := ∅) $ wkL botL

def mdpL_mem (A B) (h₁ : A 🡒 B ∈ Γ := by grind) (h₂ : A ∈ Γ := by grind) (h₃ : B ∈ Δ := by grind) : ⊢ᵍ[Grz]! (Γ ⟹ Δ) := by
  rw [(show Γ = insert (A 🡒 B) (insert A (Γ \ {A, A 🡒 B})) by grind)];
  apply impL;
  . apply union A;
  . apply union B;

def deductionTheorem (π : ⊢ᵍ[Grz]! (insert A Γ ⟹ {B})) : ⊢ᵍ[Grz]! (Γ ⟹ {A 🡒 B}) := by
  rw [← insert_empty_eq];
  apply impR;
  rwa [insert_empty_eq];

def negL : ⊢ᵍ[Grz]! (Γ ⟹ (insert A Δ)) → ⊢ᵍ[Grz]! ((insert (∼A) Γ) ⟹ Δ) := λ p => impL p (wkR $ wkL botL)

def negR : ⊢ᵍ[Grz]! ((insert A Γ) ⟹ Δ) → ⊢ᵍ[Grz]! (Γ ⟹ (insert (∼A) Δ)) := λ p => impR $ wkR $ wkL p

def andL : ⊢ᵍ[Grz]! ((insert A $ insert B $ Γ) ⟹ Δ) → ⊢ᵍ[Grz]! (insert (A ⋏ B) Γ ⟹ Δ) := λ p => by
  apply impL;
  . apply impR;
    apply negR;
    simpa [(show (insert A $ insert B Γ) = (insert B $ insert A Γ) by grind)] using p;
  . exact botL_mem;

def andR : ⊢ᵍ[Grz]! (Γ ⟹ insert A Δ) → ⊢ᵍ[Grz]! (Γ ⟹ insert B Δ) → ⊢ᵍ[Grz]! (Γ ⟹ insert (A ⋏ B) Δ) := λ p q => by
  apply impR;
  apply impL;
  . exact wkR p;
  . exact negL $ wkR q;

def orL : ⊢ᵍ[Grz]! (insert A Γ ⟹ Δ) → ⊢ᵍ[Grz]! (insert B Γ ⟹ Δ) → ⊢ᵍ[Grz]! (insert (A ⋎ B) Γ ⟹ Δ) := λ p q => by
  apply impL;
  . exact negR p;
  . exact q;

def orR : ⊢ᵍ[Grz]! (Γ ⟹ (insert A $ insert B Δ)) → ⊢ᵍ[Grz]! (Γ ⟹ insert (A ⋎ B) Δ) := λ p => by
  apply impR;
  apply negL;
  simpa;

def implyK : ⊢ᵍ[Grz]! (∅ ⟹ {A 🡒 B 🡒 A}) := deductionTheorem $ deductionTheorem $ union A

def implyS : ⊢ᵍ[Grz]! (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert A (insert (A 🡒 B) (insert (A 🡒 B 🡒 C) ∅)) = ({A 🡒 B 🡒 C, A 🡒 B, A}) by grind)];
  apply impL;
  . exact impL (union A) (union A);
  . exact impL (impL (union A) (union B)) (union C);

def elimContra : ⊢ᵍ[Grz]! (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [(show insert B (insert (∼A 🡒 ∼B) ∅) = ({∼A 🡒 ∼B, B}) by grind)];
  exact impL (negR $ union A) (negL $ union B);

def dne : ⊢ᵍ[Grz]! (∅ ⟹ {∼∼A 🡒 A}) := by
  apply deductionTheorem;
  exact negL (negR (axm A));

def andElimL : ⊢ᵍ[Grz]! (∅ ⟹ {(A ⋏ B) 🡒 A}) := by
  apply deductionTheorem;
  apply andL;
  apply union A;

def andElimR : ⊢ᵍ[Grz]! (∅ ⟹ {(A ⋏ B) 🡒 B}) := by
  apply deductionTheorem;
  apply andL;
  apply union B;

def andIntro : ⊢ᵍ[Grz]! (∅ ⟹ {A 🡒 B 🡒 (A ⋏ B)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply andR;
  . apply union A;
  . apply union B;

def orIntroL : ⊢ᵍ[Grz]! (∅ ⟹ {A 🡒 (A ⋎ B)}) := by
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply orR;
  apply union A;

def orIntroR : ⊢ᵍ[Grz]! (∅ ⟹ {B 🡒 (A ⋎ B)}) := by
  apply deductionTheorem;
  rw [← insert_empty_eq];
  apply orR;
  apply union B;

def orElim : ⊢ᵍ[Grz]! (∅ ⟹ {(A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)}) := by
  apply deductionTheorem;
  apply deductionTheorem;
  apply deductionTheorem;
  apply orL;
  . apply mdpL_mem A C;
  . apply mdpL_mem B C;


def seq_T : ⊢ᵍ[Grz]! ({□A} ⟹ {A}) := by
  rw [← insert_empty_eq];
  apply boxT;
  rw [insert_empty_eq];
  exact axm A;

def modalT : ⊢ᵍ[Grz]! (∅ ⟹ {□A 🡒 A}) := deductionTheorem $ wkL seq_T (by grind)

def seq_four : ⊢ᵍ[Grz]! ({□A} ⟹ {□□A}) := by
  rw [(show ({□A} : FormulaFinset α) = □({A} : FormulaFinset α) by grind)];
  apply boxGrz;
  rw [(show □({A} : FormulaFinset α) = {□A} by grind)];
  exact union (□A);

def modal4 : ⊢ᵍ[Grz]! (∅ ⟹ {□A 🡒 □□A}) := deductionTheorem $ wkL seq_four (by grind)

def seq_grz_core : ⊢ᵍ[Grz]! ({□(A 🡒 □A), □(□(A 🡒 □A) 🡒 A)} ⟹ {A}) := by
  rw [(show ({□(A 🡒 □A), □(□(A 🡒 □A) 🡒 A)} : FormulaFinset α)
    = insert (□(□(A 🡒 □A) 🡒 A)) {□(A 🡒 □A)} by grind)];
  apply boxT;
  apply mdpL_mem (□(A 🡒 □A)) A;

def seq_grz_box : ⊢ᵍ[Grz]! ({□(□(A 🡒 □A) 🡒 A)} ⟹ {□A}) := by
  rw [(show ({□(□(A 🡒 □A) 🡒 A)} : FormulaFinset α) = □({□(A 🡒 □A) 🡒 A} : FormulaFinset α) by grind)];
  apply boxGrz;
  rw [(show □({□(A 🡒 □A) 🡒 A} : FormulaFinset α) = {□(□(A 🡒 □A) 🡒 A)} by grind)];
  exact seq_grz_core;

def modalGrzAux : ⊢ᵍ[Grz]! (∅ ⟹ {□(□(A 🡒 □A) 🡒 A) 🡒 □A}) := deductionTheorem $ wkL seq_grz_box (by grind)


def seq_K_core : ⊢ᵍ[Grz]! ({□A, □(A 🡒 B)} ⟹ {□B}) := by
  rw [(show ({□A, □(A 🡒 B)} : FormulaFinset α) = □({A, A 🡒 B} : FormulaFinset α) by grind)];
  apply boxGrz;
  rw [(show □({A, A 🡒 B} : FormulaFinset α) = {□A, □(A 🡒 B)} by grind)];
  rw [(show insert (□(B 🡒 □B)) ({□A, □(A 🡒 B)} : FormulaFinset α)
    = insert (□A) (insert (□(A 🡒 B)) {□(B 🡒 □B)}) by grind)];
  apply boxT;
  rw [(show insert A (insert (□(A 🡒 B)) ({□(B 🡒 □B)} : FormulaFinset α))
    = insert (□(A 🡒 B)) (insert A {□(B 🡒 □B)}) by grind)];
  apply boxT;
  apply mdpL_mem A B;

def modalK : ⊢ᵍ[Grz]! (∅ ⟹ {□(A 🡒 B) 🡒 (□A 🡒 □B)}) := deductionTheorem $ deductionTheorem seq_K_core


def nec (p : ⊢ᵍ[Grz]! (∅ ⟹ {A})) : ⊢ᵍ[Grz]! (∅ ⟹ {□A}) := by
  rw [(show (∅ : FormulaFinset α) = □(∅ : FormulaFinset α) by grind)];
  apply boxGrz;
  rw [(show □(∅ : FormulaFinset α) = ∅ by grind)];
  exact wkL p (by grind);

end ProofGentzen


abbrev ProvableGentzen (S : Sequent α) : Prop := Nonempty (ProofGentzen S)
notation:120 "⊢ᵍ[Grz] " S:121 => ProvableGentzen S

notation:120 "⊬ᵍ[Grz] " S:121 => ¬ ProvableGentzen S

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B C : Formula α}

lemma axm (A : Formula α) : ⊢ᵍ[Grz] ({A} ⟹ {A}) := ⟨ProofGentzen.axm A⟩
lemma union (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ[Grz] (Γ ⟹ Δ) := ⟨ProofGentzen.union A hΓ hΔ⟩
lemma union' (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ[Grz] S := union A hΓ hΔ
lemma botL : ⊢ᵍ[Grz] ({⊥} ⟹ (∅ : FormulaFinset α)) := ⟨ProofGentzen.botL⟩
@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[Grz] (Γ ⟹ Δ) := ⟨ProofGentzen.botL_mem h⟩
@[grind =>] lemma botL_mem' (S : Sequent α) (h : ⊥ ∈ S.ant := by grind) : ⊢ᵍ[Grz] S := botL_mem h
lemma wkL (π : ⊢ᵍ[Grz] (Γ ⟹ Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ[Grz] (Γ' ⟹ Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᵍ[Grz] (Γ ⟹ Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ[Grz] (Γ ⟹ Δ') := ⟨ProofGentzen.wkR π.some h⟩
lemma wk (π : ⊢ᵍ[Grz] (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᵍ[Grz] (Γ' ⟹ Δ') := wkR (wkL π hΓ) hΔ
lemma impL (π₁ : ⊢ᵍ[Grz] (Γ ⟹ insert A Δ)) (π₂ : ⊢ᵍ[Grz] (insert B Γ ⟹ Δ)) : ⊢ᵍ[Grz] ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᵍ[Grz] ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍ[Grz] (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩
lemma boxT (π : ⊢ᵍ[Grz] (insert B Γ ⟹ Δ)) : ⊢ᵍ[Grz] (insert (□B) Γ ⟹ Δ) := ⟨ProofGentzen.boxT π.some⟩
lemma boxGrz (π : ⊢ᵍ[Grz] (insert (□(A 🡒 □A)) (□Γ) ⟹ {A})) : ⊢ᵍ[Grz] (□Γ ⟹ {□A}) := ⟨ProofGentzen.boxGrz π.some⟩

lemma orR (h : ⊢ᵍ[Grz] (Γ ⟹ insert A (insert B Δ))) : ⊢ᵍ[Grz] (Γ ⟹ insert (A ⋎ B) Δ) :=
  ⟨ProofGentzen.orR h.some⟩
lemma orL (h₁ : ⊢ᵍ[Grz] (insert A Γ ⟹ Δ)) (h₂ : ⊢ᵍ[Grz] (insert B Γ ⟹ Δ)) : ⊢ᵍ[Grz] (insert (A ⋎ B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.orL h₁.some h₂.some⟩
lemma andR (h₁ : ⊢ᵍ[Grz] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍ[Grz] (Γ ⟹ insert B Δ)) : ⊢ᵍ[Grz] (Γ ⟹ insert (A ⋏ B) Δ) :=
  ⟨ProofGentzen.andR h₁.some h₂.some⟩
lemma andL (h : ⊢ᵍ[Grz] (insert A (insert B Γ) ⟹ Δ)) : ⊢ᵍ[Grz] (insert (A ⋏ B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.andL h.some⟩
lemma negL (h : ⊢ᵍ[Grz] (Γ ⟹ insert A Δ)) : ⊢ᵍ[Grz] (insert (∼A) Γ ⟹ Δ) :=
  ⟨ProofGentzen.negL h.some⟩
lemma negR (h : ⊢ᵍ[Grz] (insert A Γ ⟹ Δ)) : ⊢ᵍ[Grz] (Γ ⟹ insert (∼A) Δ) :=
  ⟨ProofGentzen.negR h.some⟩

lemma implyK : ⊢ᵍ[Grz] (∅ ⟹ {A 🡒 B 🡒 A}) := ⟨ProofGentzen.implyK⟩
lemma implyS : ⊢ᵍ[Grz] (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := ⟨ProofGentzen.implyS⟩
lemma elimContra : ⊢ᵍ[Grz] (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := ⟨ProofGentzen.elimContra⟩
lemma dne : ⊢ᵍ[Grz] (∅ ⟹ {∼∼A 🡒 A}) := ⟨ProofGentzen.dne⟩
lemma andElimL : ⊢ᵍ[Grz] (∅ ⟹ {(A ⋏ B) 🡒 A}) := ⟨ProofGentzen.andElimL⟩
lemma andElimR : ⊢ᵍ[Grz] (∅ ⟹ {(A ⋏ B) 🡒 B}) := ⟨ProofGentzen.andElimR⟩
lemma andIntro : ⊢ᵍ[Grz] (∅ ⟹ {A 🡒 B 🡒 (A ⋏ B)}) := ⟨ProofGentzen.andIntro⟩
lemma orIntroL : ⊢ᵍ[Grz] (∅ ⟹ {A 🡒 (A ⋎ B)}) := ⟨ProofGentzen.orIntroL⟩
lemma orIntroR : ⊢ᵍ[Grz] (∅ ⟹ {B 🡒 (A ⋎ B)}) := ⟨ProofGentzen.orIntroR⟩
lemma orElim : ⊢ᵍ[Grz] (∅ ⟹ {(A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)}) := ⟨ProofGentzen.orElim⟩

theorem deductionTheorem (π : ⊢ᵍ[Grz] (insert A Γ ⟹ {B})) : ⊢ᵍ[Grz] (Γ ⟹ {A 🡒 B}) := ⟨π.some.deductionTheorem⟩

lemma seq_T : ⊢ᵍ[Grz] ({□A} ⟹ {A}) := ⟨ProofGentzen.seq_T⟩
lemma modalT : ⊢ᵍ[Grz] (∅ ⟹ {□A 🡒 A}) := ⟨ProofGentzen.modalT⟩
lemma seq_four : ⊢ᵍ[Grz] ({□A} ⟹ {□□A}) := ⟨ProofGentzen.seq_four⟩
lemma modal4 : ⊢ᵍ[Grz] (∅ ⟹ {□A 🡒 □□A}) := ⟨ProofGentzen.modal4⟩
lemma seq_grz_core : ⊢ᵍ[Grz] ({□(A 🡒 □A), □(□(A 🡒 □A) 🡒 A)} ⟹ {A}) := ⟨ProofGentzen.seq_grz_core⟩
lemma seq_grz_box : ⊢ᵍ[Grz] ({□(□(A 🡒 □A) 🡒 A)} ⟹ {□A}) := ⟨ProofGentzen.seq_grz_box⟩
lemma modalGrzAux : ⊢ᵍ[Grz] (∅ ⟹ {□(□(A 🡒 □A) 🡒 A) 🡒 □A}) := ⟨ProofGentzen.modalGrzAux⟩
lemma seq_K_core : ⊢ᵍ[Grz] ({□A, □(A 🡒 B)} ⟹ {□B}) := ⟨ProofGentzen.seq_K_core⟩
lemma modalK : ⊢ᵍ[Grz] (∅ ⟹ {□(A 🡒 B) 🡒 (□A 🡒 □B)}) := ⟨ProofGentzen.modalK⟩
lemma nec : ⊢ᵍ[Grz] (∅ ⟹ {A}) → ⊢ᵍ[Grz] (∅ ⟹ {□A}) := λ ⟨p⟩ => ⟨ProofGentzen.nec p⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent α) → ⊢ᵍ[Grz] S → Prop}
  (axm : ∀ A, motive ({A} ⟹ {A}) (ProvableGentzen.axm A))
  (botL : motive ({⊥} ⟹ (∅ : FormulaFinset α)) ProvableGentzen.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍ[Grz] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᵍ[Grz] (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍ[Grz] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍ[Grz] (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᵍ[Grz] ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxT : ∀ {Γ Δ B} (h : ⊢ᵍ[Grz] (insert B Γ ⟹ Δ)),
    motive (insert B Γ ⟹ Δ) h → motive (insert (□B) Γ ⟹ Δ) (boxT h)
  )
  (boxGrz : ∀ {Γ : FormulaFinset α} {A} (h : ⊢ᵍ[Grz] (insert (□(A 🡒 □A)) (□Γ) ⟹ {A})),
    motive (insert (□(A 🡒 □A)) (□Γ) ⟹ {A}) h → motive (□Γ ⟹ {□A}) (boxGrz h)
  )
  : ∀ {S : Sequent α} (h : ⊢ᵍ[Grz] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : Sequent α} : (⊬ᵍ[Grz] S) ↔ (IsEmpty (⊢ᵍ[Grz]! S)) := by simp [ProvableGentzen];

end ProvableGentzen


inductive GentzenWithCutProof : Sequent α → Type u
| axm (A) : GentzenWithCutProof ({A} ⟹ {A})
| botL : GentzenWithCutProof ({⊥} ⟹ ∅)
| wkL  {Γ Γ' Δ}  : GentzenWithCutProof (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → GentzenWithCutProof (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : GentzenWithCutProof (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → GentzenWithCutProof (Γ ⟹ Δ')
| impL {Γ Δ A B} : GentzenWithCutProof (Γ ⟹ (insert A Δ)) → GentzenWithCutProof (insert B Γ ⟹ Δ) → GentzenWithCutProof ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : GentzenWithCutProof ((insert A Γ) ⟹ (insert B Δ)) → GentzenWithCutProof (Γ ⟹ (insert (A 🡒 B) Δ))
| boxT   {Γ Δ : FormulaFinset α} {B} : GentzenWithCutProof (insert B Γ ⟹ Δ) → GentzenWithCutProof (insert (□B) Γ ⟹ Δ)
| boxGrz {Γ : FormulaFinset α} {A}   : GentzenWithCutProof (insert (□(A 🡒 □A)) (□Γ) ⟹ {A}) → GentzenWithCutProof (□Γ ⟹ {□A})
| cut {Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹ insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹ Δ₂) → GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂)
notation:120 "⊢ᵍᶜ[Grz]! " S:121 => GentzenWithCutProof S

abbrev GentzenWithCutProvable (S : Sequent α) : Prop := Nonempty (⊢ᵍᶜ[Grz]! S)
notation:120 "⊢ᵍᶜ[Grz] " S:121 => GentzenWithCutProvable S


def GentzenWithCutProof.ofGentzenProof {S : Sequent α} : ⊢ᵍ[Grz]! S → ⊢ᵍᶜ[Grz]! S
| .axm A => .axm A
| .botL => .botL
| .wkL h h' => .wkL (ofGentzenProof h) h'
| .wkR h h' => .wkR (ofGentzenProof h) h'
| .impL h₁ h₂ => .impL (ofGentzenProof h₁) (ofGentzenProof h₂)
| .impR h => .impR (ofGentzenProof h)
| .boxT h => .boxT (ofGentzenProof h)
| .boxGrz h => .boxGrz (ofGentzenProof h)

namespace GentzenWithCutProvable

variable {S : Sequent α} {A B : Formula α} {Γ Γ' Γ₁ Γ₂ Δ Δ' Δ₁ Δ₂ : FormulaFinset α}

theorem of_without_cut : ⊢ᵍ[Grz] S → ⊢ᵍᶜ[Grz] S := λ ⟨p⟩ => ⟨GentzenWithCutProof.ofGentzenProof p⟩

lemma axm (A : Formula α) : ⊢ᵍᶜ[Grz] ({A} ⟹ {A}) := ⟨GentzenWithCutProof.axm A⟩
lemma botL : ⊢ᵍᶜ[Grz] ({⊥} ⟹ ∅ : Sequent α) := ⟨GentzenWithCutProof.botL⟩
lemma wkL (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ') : ⊢ᵍᶜ[Grz] (Γ' ⟹ Δ) := ⟨GentzenWithCutProof.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Δ ⊆ Δ') : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ') := ⟨GentzenWithCutProof.wkR h.some h'⟩
lemma impL (h₁ : ⊢ᵍᶜ[Grz] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ[Grz] ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨GentzenWithCutProof.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ[Grz] ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍᶜ[Grz] (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨GentzenWithCutProof.impR h.some⟩
lemma boxT (h : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ[Grz] (insert (□B) Γ ⟹ Δ) := ⟨GentzenWithCutProof.boxT h.some⟩
lemma boxGrz (h : ⊢ᵍᶜ[Grz] (insert (□(A 🡒 □A)) (□Γ) ⟹ {A})) : ⊢ᵍᶜ[Grz] (□Γ ⟹ {□A}) := ⟨GentzenWithCutProof.boxGrz h.some⟩
lemma cut (h₁ : ⊢ᵍᶜ[Grz] (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᵍᶜ[Grz] (insert A Γ₂ ⟹ Δ₂)) : ⊢ᵍᶜ[Grz] (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := ⟨GentzenWithCutProof.cut h₁.some h₂.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent α) → ⊢ᵍᶜ[Grz] S → Prop}
  (axm : ∀ A : Formula α, motive ({A} ⟹ {A}) (GentzenWithCutProvable.axm A))
  (botL : motive ({⊥} ⟹ ∅ : Sequent α) GentzenWithCutProvable.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍᶜ[Grz] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᵍᶜ[Grz] ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxT : ∀ {Γ : FormulaFinset α} {Δ B} (h : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)),
    motive (insert B Γ ⟹ Δ) h → motive (insert (□B) Γ ⟹ Δ) (boxT h)
  )
  (boxGrz : ∀ {Γ : FormulaFinset α} {A} (h : ⊢ᵍᶜ[Grz] (insert (□(A 🡒 □A)) (□Γ) ⟹ {A})),
    motive (insert (□(A 🡒 □A)) (□Γ) ⟹ {A}) h → motive (□Γ ⟹ {□A}) (boxGrz h)
  )
  (cut : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A}
    (h₁ : ⊢ᵍᶜ[Grz] (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᵍᶜ[Grz] (insert A Γ₂ ⟹ Δ₂)),
    (motive (Γ₁ ⟹ insert A Δ₁) h₁) → (motive (insert A Γ₂ ⟹ Δ₂) h₂) →
    motive (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) (GentzenWithCutProvable.cut h₁ h₂)
  )
  : ∀ {S : Sequent α} (h : ⊢ᵍᶜ[Grz] S), motive S h := by
    rintro S ⟨h⟩;
    induction h with
    | axm A => apply axm;
    | botL => apply botL;
    | wkL h h' ih => apply wkL ⟨h⟩ h' ih;
    | wkR h h' ih => apply wkR ⟨h⟩ h' ih;
    | cut h₁ h₂ ih₁ ih₂ => apply cut ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impL h₁ h₂ ih₁ ih₂ => apply impL ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impR h ih => apply impR ⟨h⟩ ih;
    | boxT h ih => apply boxT ⟨h⟩ ih;
    | boxGrz h ih => apply boxGrz ⟨h⟩ ih;

/-- One direction of the deduction theorem for the cut-full calculus. -/
theorem deductionTheorem (π : ⊢ᵍᶜ[Grz] (insert A Γ ⟹ {B})) : ⊢ᵍᶜ[Grz] (Γ ⟹ {A 🡒 B}) := by
  rw [(show ({A 🡒 B} : FormulaFinset α) = insert (A 🡒 B) ∅ by grind)];
  apply impR;
  rwa [(show insert B (∅ : FormulaFinset α) = {B} by grind)];

/-- The standard form of the Grz axiom, derived from the boxed `ProofGentzen.modalGrzAux` by a
cut against the reflexivity axiom. -/
theorem modalGrz {A : Formula α} : ⊢ᵍᶜ[Grz] (∅ ⟹ {□(□(A 🡒 □A) 🡒 A) 🡒 A}) := by
  have h₁ : ⊢ᵍᶜ[Grz] ({□(□(A 🡒 □A) 🡒 A)} ⟹ insert (□A) ∅) := by
    rw [(show insert (□A) (∅ : FormulaFinset α) = {□A} by grind)];
    exact of_without_cut ProvableGentzen.seq_grz_box;
  have h₂ : ⊢ᵍᶜ[Grz] (insert (□A) (∅ : FormulaFinset α) ⟹ {A}) := by
    rw [(show insert (□A) (∅ : FormulaFinset α) = {□A} by grind)];
    exact of_without_cut ProvableGentzen.seq_T;
  have h₃ := cut h₁ h₂;
  rw [(show ({□(□(A 🡒 □A) 🡒 A)} ∪ (∅ : FormulaFinset α)) = {□(□(A 🡒 □A) 🡒 A)} by grind),
      (show ((∅ : FormulaFinset α) ∪ {A}) = {A} by grind)] at h₃;
  exact deductionTheorem h₃;

end GentzenWithCutProvable

end LogicGrz

end
