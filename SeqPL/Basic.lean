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

lemma axm (A) : ⊢ ({A} ⟹ {A}) := ⟨Proof.axm A⟩
@[grind =>] lemma union (A) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ (Γ ⟹ Δ) := ⟨Proof.union A hΓ hΔ⟩
@[grind =>] lemma union' (A) {S : Sequent} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ S := union A hΓ hΔ
lemma botL : ⊢ ({⊥} ⟹ ∅) := ⟨Proof.botL⟩
@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ (Γ ⟹ Δ) := ⟨Proof.botL_mem h⟩
@[grind =>] lemma botL_mem' (S : Sequent) (h : ⊥ ∈ S.ant := by grind) : ⊢ S := botL_mem h
lemma wkL {Γ Γ' Δ} (π : ⊢ (Γ ⟹ Δ)) (h : Γ ⊆ Γ') : ⊢ (Γ' ⟹ Δ) := ⟨Proof.wkL π.some h⟩
lemma wkR {Γ Δ Δ'} (π : ⊢ (Γ ⟹ Δ)) (h : Δ ⊆ Δ') : ⊢ (Γ ⟹ Δ') := ⟨Proof.wkR π.some h⟩
lemma wk {Γ Γ' Δ Δ'} (π : ⊢ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ (Γ' ⟹ Δ') := wkR (wkL π hΓ) hΔ
lemma impL {Γ Δ A B} (π₁ : ⊢ (Γ ⟹ insert A Δ)) (π₂ : ⊢ (insert B Γ ⟹ Δ)) : ⊢ ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨Proof.impL π₁.some π₂.some⟩
lemma impR {Γ Δ A B} (π : ⊢ ((insert A Γ) ⟹ (insert B Δ))) : ⊢ (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨Proof.impR π.some⟩
lemma boxGL {Γ A} (π : ⊢ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : ⊢ (Γ.box ⟹ {□A}) := ⟨Proof.boxGL π.some⟩

lemma axiomŁ1 : ⊢ (∅ ⟹ {A 🡒 B 🡒 A}) := ⟨Proof.axiomŁ1⟩
lemma axiomŁ2 : ⊢ (∅ ⟹ {(A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)}) := ⟨Proof.axiomŁ2⟩
lemma axiomŁ3 : ⊢ (∅ ⟹ {(∼A 🡒 ∼B) 🡒 (B 🡒 A)}) := ⟨Proof.axiomŁ3⟩
lemma axiomK  : ⊢ (∅ ⟹ {(□(A 🡒 B) 🡒 (□A 🡒 □B))}) := ⟨Proof.axiomK⟩
lemma axiom4  : ⊢ (∅ ⟹ {(□A 🡒 □□A)}) := ⟨Proof.axiom4⟩
lemma axiomL  : ⊢ (∅ ⟹ {□(□A 🡒 A) 🡒 □A}) := ⟨Proof.axiomL⟩
lemma ruleNec : ⊢ (∅ ⟹ {A}) → ⊢ (∅ ⟹ {□A}) := λ ⟨p⟩ => ⟨Proof.ruleNec p⟩

end Provable

abbrev Unprovable (S : Sequent) : Prop := ¬⊢ S
prefix:120 "⊬ " => Unprovable

@[grind =]
lemma iff_unprovable_isEmpty_proof {S : Sequent} : (⊬ S) ↔ (IsEmpty (⊢! S)) := by simp [Unprovable, Provable];

section Semantics

structure Model (κ : Type*) [Nonempty κ] where
  Rel' : κ → κ → Prop
  Val : κ → ℕ → Prop

namespace Model

variable [Nonempty κ]

abbrev World (_ : Model κ) := κ
abbrev Rel {M : Model κ} : M.World → M.World → Prop := M.Rel'
infixl:60 " ≺ " => Rel

end Model

variable [Nonempty κ] {M : Model κ} {A B : Formula} {Γ Γ' Δ Δ' : FormulaFinset}

@[grind]
def Formula.Forced {M : Model κ} (x : M.World) : Formula → Prop
| #a    => M.Val x a
| ⊥     => False
| A 🡒 B => Forced x A → Forced x B
| □A    => ∀ y, x ≺ y → Forced y A
infix:55 " ⊩ " => Formula.Forced

lemma Formula.iff_not_forced_box {M : Model κ} {x : M.World} {A : Formula} : ¬x ⊩ □A ↔ ∃ y, x ≺ y ∧ ¬y ⊩ A := by grind;

@[grind]
def Formula.Valid (M : Model κ) (A : Formula) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Formula.Valid


def FormulaFinset.Forced {M : Model κ} (x : M.World) (Γ : FormulaFinset) : Prop := ∀ A ∈ Γ, x ⊩ A
infix:55 " ⊩ " => FormulaFinset.Forced


@[grind]
def Sequent.Forced {M : Model κ} (x : M.World) (S : Sequent) : Prop := (∀ C ∈ S.ant, x ⊩ C) → (∃ D ∈ S.suc, x ⊩ D)
infix:55 " ⊩ " => Sequent.Forced

lemma Sequent.forced_succ_singleton {M : Model κ} {x : M.World} : x ⊩ (Γ ⟹ {A}) ↔ (∀ C ∈ Γ, x ⊩ C) → x ⊩ A := by grind;

@[grind]
def Sequent.Valid (M : Model κ) (S : Sequent) : Prop := ∀ x : M.World, x ⊩ S
infix:50 " ⊧ " => Sequent.Valid


section soundness

variable {M : Model κ} {Γ Γ' Δ Δ' : FormulaFinset} {A B : Formula}

lemma valid_axm : M ⊧ ({A} ⟹ {A}) := by
  intro x h;
  use A;
  constructor;
  . grind;
  . exact h _ (by grind);

lemma valid_botL : M ⊧ ({⊥} ⟹ ∅) := by
  intro x;
  simp [Sequent.Forced, Formula.Forced];

lemma valid_wkL (h : M ⊧ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ' := by grind) : M ⊧ (Γ' ⟹ Δ) := by
  intro x h';
  apply h;
  grind;

lemma valid_wkR (h : M ⊧ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ' := by grind) : M ⊧ (Γ ⟹ Δ') := by
  intro x hΓ;
  obtain ⟨D, hD₁, hD₂⟩ := h x hΓ;
  grind;

lemma valid_impL (hA : M ⊧ (Γ ⟹ insert A Δ)) (hB : M ⊧ (insert B Γ ⟹ Δ)) : M ⊧ ((insert (A 🡒 B) Γ) ⟹ Δ) := by
  intro x h;
  replace hA := hA x
  replace hB := hB x;
  simp only [Finset.mem_insert, forall_eq_or_imp] at h;
  grind;

lemma valid_impR (h : M ⊧ ((insert A Γ) ⟹ (insert B Δ))) : M ⊧ (Γ ⟹ (insert (A 🡒 B) Δ)) := by
  intro x hΓ;
  by_cases x ⊩ A;
  . obtain ⟨D, hD₁, hD₂⟩ := h x $ by grind;
    simp at hD₁;
    rcases hD₁ with (rfl | hD₁);
    . use A 🡒 D; grind;
    . use D; grind;
  . use A 🡒 B;
    grind;


namespace Model

abbrev _root_.IsConverseWellFounded (α) (R : α → α → Prop) := IsWellFounded α (λ x y => R y x)

lemma has_terminal [IsConverseWellFounded _ M.Rel'] : ∀ (W : Set M.World), Set.Nonempty W → ∃ t ∈ W, ∀ x ∈ W, ¬(t ≺ x) :=
  WellFounded.wellFounded_iff_has_min.mp (by apply IsWellFounded.wf)

class IsGL (M : Model κ) extends IsTrans _ M.Rel', IsConverseWellFounded _ M.Rel'

class IsFiniteGL (M : Model κ) extends IsTrans _ M.Rel', Std.Irrefl M.Rel' where
  finite : Finite M.World

instance [M.IsFiniteGL] : M.IsGL where
  wf := by apply @Finite.wellFounded_of_trans_of_irrefl M.World (IsFiniteGL.finite);

end Model



lemma valid_boxGL [M.IsGL] (h : M ⊧ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : M ⊧ (Γ.box ⟹ {□A}) := by
  intro x;
  apply Sequent.forced_succ_singleton.mpr;
  intro hΓ y Rxy;
  apply Sequent.forced_succ_singleton.mp $ h y;
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, forall_eq_or_imp];
  refine ⟨?_, ?_⟩;
  . by_contra hC;
    obtain ⟨z, Ryz, hz⟩ := Formula.iff_not_forced_box.mp hC;
    obtain ⟨t, ⟨Ryt, hntA⟩, ht₂⟩ := M.has_terminal ({z | y ≺ z ∧ ¬z ⊩ A}) ⟨z, ⟨Ryz, hz⟩⟩;
    apply hntA;
    apply Sequent.forced_succ_singleton.mp $ h t;
    simp;
    constructor;
    . rintro t' Rtt';
      by_contra;
      exact ht₂ t' ⟨_root_.trans Ryt Rtt', by assumption⟩ Rtt';
    . rintro C (hC | ⟨C, hC, rfl⟩);
      . apply hΓ (□C) (by simpa) t;
        apply _root_.trans Rxy Ryt;
      . intro t' Rtt';
        apply hΓ (□C) (by simpa) t';
        apply _root_.trans (_root_.trans Rxy Ryt) Rtt';
  . rintro C (hC | ⟨C, hC, rfl⟩);
    . exact hΓ (□C) (by simpa) y Rxy;
    . intro z Ryz;
      exact hΓ (□C) (by simpa) z (_root_.trans Rxy Ryz);

theorem soundness (h : ⊢ S) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ, [M.IsGL] → M ⊧ S := by
  obtain ⟨p⟩ := h;
  intro _ M M_finiteGL;
  induction p with
  | axm A => exact valid_axm
  | botL => exact valid_botL
  | wkL h _ ih => exact valid_wkL ih;
  | wkR h _ ih => exact valid_wkR ih;
  | impL _ _ ih₁ ih₂ => exact valid_impL ih₁ ih₂
  | impR _ ih => exact valid_impR ih
  | boxGL _ ih => exact valid_boxGL ih

theorem finite_soundness (h : ⊢ S) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ, [M.IsFiniteGL] → M ⊧ S := λ _ _ M [M.IsFiniteGL] => soundness h M

def trivial_GL_model : Model (Fin 1) where
  Rel' := λ _ _ => False
  Val := λ _ _ => False

instance : trivial_GL_model.IsFiniteGL where
  finite := inferInstance;
  trans  := by tauto;
  irrefl := by tauto;

lemma not_provable_empty : ⊬ (∅ ⟹ ∅) := by
  by_contra h;
  simpa [Sequent.Forced] using (soundness h trivial_GL_model) 0;

end soundness


section completeness

namespace Formula

def subfmls : Formula → Finset Formula
| #a    => {#a}
| ⊥     => {⊥}
| A 🡒 B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)
| □A    => insert (□A) A.subfmls

@[grind .]
lemma mem_subfmls_self : A ∈ A.subfmls := by cases A <;> simp [Formula.subfmls];

@[grind]
def IsBox : Formula → Prop
| □_ => True
| _ => False

instance : DecidablePred Formula.IsBox := λ A => by
  cases A;
  case box => exact isTrue $ by grind;
  case atom | bot | imp => exact isFalse $ by grind;

end Formula


namespace FormulaFinset

@[grind]
def subfmls (Γ : FormulaFinset) : Finset Formula := Finset.biUnion Γ Formula.subfmls

@[grind .] lemma subset_self_subfmls : Γ ⊆ Γ.subfmls := by grind;

@[grind]
noncomputable def prebox (Γ : FormulaFinset) : FormulaFinset := Γ.preimage (□·) $ by grind [Set.InjOn];

@[grind =]
lemma iff_mem_prebox_mem : A ∈ Γ.prebox ↔ □A ∈ Γ := by simp [FormulaFinset.prebox];

end FormulaFinset

namespace Sequent

@[grind]
def subfmls (S : Sequent) : Finset Formula := S.ant.subfmls ∪ S.suc.subfmls

structure subset (S T : Sequent) : Prop where
  ant_subset : S.ant ⊆ T.ant
  suc_subset : S.suc ⊆ T.suc

instance : HasSubset (Sequent) := ⟨subset⟩

variable {S : Sequent}

@[grind .] lemma subset_self_subfmls : S.ant ∪ S.suc ⊆ S.subfmls := by grind;

structure Saturated (S : Sequent) where
  impL : ∀ {A B}, A 🡒 B ∈ S.1 → A ∈ S.2 ∨ B ∈ S.1
  impR : ∀ {A B}, A 🡒 B ∈ S.2 → A ∈ S.1 ∧ B ∈ S.2

structure Expanded (BS : Sequent) (S : Sequent) extends S.Saturated where
  subset_subfmls : S.1 ∪ S.2 ⊆ BS.subfmls
  unprovable     : ⊬ S

section Expanded



end Expanded

-- lemma lindenbaum

end Sequent

structure ExpandedSequent (BS : Sequent) extends Sequent where
  saturated : toSequent.Saturated
  subset_subfmls : toSequent.1 ∪ toSequent.2 ⊆ BS.subfmls
  unprovable     : ⊬ toSequent

attribute [grind .] ExpandedSequent.saturated ExpandedSequent.subset_subfmls ExpandedSequent.unprovable

namespace ExpandedSequent

variable {S : ExpandedSequent BS}

@[grind .] lemma not_mem_both {A : Formula} : ¬(A ∈ S.1.1 ∧ A ∈ S.1.2) := by grind;

@[grind .] lemma not_mem_bot_ant : ⊥ ∉ S.1.1 := by grind;

@[grind =>] lemma of_mem_imp_ant (h : A 🡒 B ∈ S.1.1 := by grind) : A ∈ S.1.2 ∨ B ∈ S.1.1 := S.saturated.impL h
@[grind =>] lemma of_mem_imp_suc (h : A 🡒 B ∈ S.1.2 := by grind) : A ∈ S.1.1 ∧ B ∈ S.1.2 := S.saturated.impR h

section

variable {BS : Sequent} [Fact (⊬ BS)]

open Classical in
noncomputable def lindenbaum_indexed (BS : Sequent) [Fact (⊬ BS)] {S₀} (hS₀ : ⊬ S₀) : List Formula → { S : Sequent // ⊬ S }
| [] => ⟨S₀, hS₀⟩
| ((A 🡒 B) :: l) =>
  let ⟨S, hS⟩ := lindenbaum_indexed BS hS₀ l;
  if h : (A 🡒 B) ∈ S.1 then
    if h : ⊬ ((S.1) ⟹ (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
    else ⟨((insert B S.1) ⟹ S.2), by
      push Not at h;
      contrapose! hS;
      have := Provable.impL h hS;
      rwa [(show insert (A 🡒 B) S.1 = S.1 by grind)] at this;
    ⟩
  else if h : (A 🡒 B) ∈ S.2 then ⟨
    ((insert A S.1) ⟹ (insert B S.2)),
    by
      contrapose! hS;
      have := Provable.impR hS;
      rwa [(show insert (A 🡒 B) S.2 = S.2 by grind)] at this;
  ⟩
  else ⟨S, hS⟩
| (_ :: l) => lindenbaum_indexed BS hS₀ l

lemma mem_lindenbaum_indexed {BS : Sequent} [Fact (⊬ BS)] {S₀} {S₀_unprovable : ⊬ S₀} :
  A ∈ (lindenbaum_indexed BS S₀_unprovable l).1.1 → A ∈ S₀.1 := by
  induction l with
  | nil => simp [lindenbaum_indexed];
  | cons A l ih =>
    match A with
    | #a | □A | ⊥ => simpa [lindenbaum_indexed];
    | (A 🡒 B) =>
      dsimp [lindenbaum_indexed];
      generalize eT : lindenbaum_indexed BS S₀_unprovable l = T at ih;
      split;
      . split;
        . sorry;
        . sorry;
      . sorry;

noncomputable def lindenbaum (BS : Sequent) [Fact (⊬ BS)]
  {S₀} (S₀_subfml : (S₀.ant ∪ S₀.suc) ⊆ BS.subfmls) (S₀_unprovable : ⊬ S₀)
  : ExpandedSequent BS :=
  let S := lindenbaum_indexed BS S₀_unprovable (BS.subfmls.toList);
  {
    toSequent := S.1,
    unprovable := S.2,
    saturated := {
      impL := by
        intro A B h;

        sorry;
      impR := by
        intro A B h;
        sorry;
    }
    subset_subfmls := by
      intro A hA;
      apply S₀_subfml;
      sorry;
  }

lemma subset_lindenbaum (BS : Sequent) [Fact (⊬ BS)] {S₀} (S₀_subfml : (S₀.ant ∪ S₀.suc) ⊆ BS.subfmls) (hS₀ : ⊬ S₀) : S₀ ⊆ (lindenbaum BS S₀_subfml hS₀).1 := by

  sorry

end


instance : Finite (ExpandedSequent BS) := by
  sorry;

instance [Fact (⊬ BS)] : Nonempty (ExpandedSequent BS) := ⟨lindenbaum BS (S₀ := BS) (by grind) (Fact.elim inferInstance)⟩

end ExpandedSequent


@[grind]
def countermodelOf (BS : Sequent) [Fact (⊬ BS)] : Model (ExpandedSequent BS) where
  Val S a := #a ∈ S.1.1
  Rel' S T :=
    S.1.1.prebox ⊂ T.1.1.prebox ∧
    S.1.1.prebox ⊆ T.1.1

variable {BS : Sequent} [Fact (⊬ BS)]

instance : (countermodelOf BS).IsFiniteGL where
  finite := inferInstance
  trans := by grind;
  irrefl := by grind;

variable {S : (countermodelOf BS).World} {A : Formula}

lemma truthlemma :
  (A ∈ S.1.1 → S ⊩ A) ∧ (A ∈ S.1.2 → ¬S ⊩ A)
  := by
  induction A generalizing S with
  | box A ih =>
    constructor;
    . intro h T RST;
      exact ih.1 $ RST.2 (by simpa [FormulaFinset.prebox]);
    . intro h;
      have : ⊬ (insert (□A) (S.1.1.prebox ∪ S.1.1.prebox.box) ⟹ {A}) := by
        have := S.unprovable;
        contrapose! this;
        exact Provable.wk (Provable.boxGL this)
          (show S.1.1.prebox.box ⊆ S.1.1 by grind)
          (show {□A} ⊆ S.1.2 by grind);
      let T := ExpandedSequent.lindenbaum BS (by
        intro B;
        sorry;
        /-
        simp only [Finset.insert_union, Finset.union_assoc, Finset.union_singleton,
          Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_image];
        rintro (rfl | rfl | hB | ⟨B, hB, rfl⟩);
        . app@apply S.subset_subfmls (□A);
          sorry
        . exact S.subset_subfmls (by grind);
        . apply S.subset_subfmls
          simp;
          sorry;
        . sorry;
        -/
      ) this;
      have hT := ExpandedSequent.subset_lindenbaum BS (by sorry) this;
      apply Formula.iff_not_forced_box.mpr;
      use T;
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      . intro B hB;
        simp only [FormulaFinset.iff_mem_prebox_mem]
        apply hT.1;
        sorry;
        -- grind;
      . apply Set.not_subset.mpr;
        use A;
        constructor;
        . apply FormulaFinset.iff_mem_prebox_mem.mpr;
          apply hT.1;
          simp;
        . sorry;
          -- grind [ExpandedSequent.not_mem_both (S := S) (A := A)]
      . intro B hB;
        apply hT.1;
        grind;
      . exact ih.2 $ hT.2 (by simp);
  | _ => sorry; -- grind;

lemma truthlemma_ant : A ∈ S.1.1 → S ⊩ A := truthlemma.1
lemma truthlemma_suc : A ∈ S.1.2 → ¬S ⊩ A := truthlemma.2

theorem completeness {S : Sequent} (h : ∀ {κ : Type 0}, [Nonempty κ] → ∀ M : Model κ, [M.IsFiniteGL] → M ⊧ S) : ⊢ S := by
  contrapose! h;
  replace h : Fact (⊬ S) := ⟨iff_unprovable_isEmpty_proof.mpr h⟩;
  use (ExpandedSequent S), inferInstance, (countermodelOf S);
  constructor;
  . infer_instance;
  . dsimp [Sequent.Forced, Sequent.Valid];
    push Not;
    use (ExpandedSequent.lindenbaum S (S₀ := S) (by grind) (Fact.elim inferInstance))
    constructor;
    . intro C hC; exact truthlemma_ant $ ExpandedSequent.subset_lindenbaum S _ _ |>.1 hC;
    . intro D hD; exact truthlemma_suc $ ExpandedSequent.subset_lindenbaum S _ _ |>.2 hD;

lemma deduction_theorem : ⊢ (insert A Γ ⟹ {B}) ↔ ⊢ (Γ ⟹ {A 🡒 B}) := by
  constructor;
  . intro h;
    apply completeness;
    intro κ _ M _ x _;
    use A 🡒 B;
    constructor;
    . simp;
    . intro hA;
      exact (Sequent.forced_succ_singleton.mp $ finite_soundness h M x) (by grind);
  . intro h;
    apply completeness;
    intro κ _ M _ x;
    apply Sequent.forced_succ_singleton.mpr;
    intro H;
    exact (Sequent.forced_succ_singleton.mp $ finite_soundness h M x) (by grind) (by grind);

end completeness

end Semantics




inductive ProofWithCut : Sequent → Type
| axm (A) : ProofWithCut ({A} ⟹ {A})
| botL : ProofWithCut ({⊥} ⟹ ∅)
| wkL  {Γ Γ' Δ}  : ProofWithCut (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofWithCut (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : ProofWithCut (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofWithCut (Γ ⟹ Δ')
| impL {Γ Δ A B} : ProofWithCut (Γ ⟹ (insert A Δ)) → ProofWithCut (insert B Γ ⟹ Δ) → ProofWithCut ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : ProofWithCut ((insert A Γ) ⟹ (insert B Δ)) → ProofWithCut (Γ ⟹ (insert (A 🡒 B) Δ))
| boxGL {Γ A} : ProofWithCut ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) → ProofWithCut (Γ.box ⟹ {□A})
| cut {Γ₁ Γ₂ Δ₁ Δ₂ A} : ProofWithCut (Γ₁ ⟹ insert A Δ₁) → ProofWithCut (insert A Γ₂ ⟹ Δ₂) → ProofWithCut (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂)

prefix:120 "⊢ᶜ! " => ProofWithCut

abbrev ProvableWithCut (S : Sequent) : Prop := Nonempty (⊢ᶜ! S)
prefix:120 "⊢ᶜ " => ProvableWithCut

namespace ProvableWithCut

def ofProof : ⊢! S → ⊢ᶜ! S
| .axm A => .axm A
| .botL => .botL
| .wkL h h' => .wkL (ofProof h) h'
| .wkR h h' => .wkR (ofProof h) h'
| .impL h₁ h₂ => .impL (ofProof h₁) (ofProof h₂)
| .impR h => .impR (ofProof h)
| .boxGL h => .boxGL (ofProof h)

lemma axm (A) : ⊢ᶜ ({A} ⟹ {A}) := ⟨ProofWithCut.axm A⟩
lemma botL : ⊢ᶜ ({⊥} ⟹ ∅) := ⟨ProofWithCut.botL⟩
lemma wkL {Γ Γ' Δ} (h : ⊢ᶜ (Γ ⟹ Δ)) (h' : Γ ⊆ Γ') : ⊢ᶜ (Γ' ⟹ Δ) := ⟨ProofWithCut.wkL h.some h'⟩
lemma wkR {Γ Δ Δ'} (h : ⊢ᶜ (Γ ⟹ Δ)) (h' : Δ ⊆ Δ') : ⊢ᶜ (Γ ⟹ Δ') := ⟨ProofWithCut.wkR h.some h'⟩
lemma impL {Γ Δ A B} (h₁ : ⊢ᶜ (Γ ⟹ insert A Δ)) (h₂ : ⊢ᶜ (insert B Γ ⟹ Δ)) : ⊢ᶜ ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨ProofWithCut.impL h₁.some h₂.some⟩
lemma impR {Γ Δ A B} (h : ⊢ᶜ ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᶜ (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨ProofWithCut.impR h.some⟩
lemma boxGL {Γ A} (h : ⊢ᶜ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : ⊢ᶜ (Γ.box ⟹ {□A}) := ⟨ProofWithCut.boxGL h.some⟩
lemma cut {Γ₁ Γ₂ Δ₁ Δ₂ A} (h₁ : ⊢ᶜ (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᶜ (insert A Γ₂ ⟹ Δ₂)) : ⊢ᶜ (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := ⟨ProofWithCut.cut h₁.some h₂.some⟩

lemma rec
  {motive : (S : Sequent) → ⊢ᶜ S → Prop}
  (axm : ∀ A, motive ({A} ⟹ {A}) (ProvableWithCut.axm A))
  (botL : motive ({⊥} ⟹ ∅) ProvableWithCut.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᶜ (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᶜ (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᶜ (Γ ⟹ insert A Δ)) (h₂ : ⊢ᶜ (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᶜ ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxGL : ∀ {Γ A} (h : ⊢ᶜ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A}) h → motive (Γ.box ⟹ {□A}) (boxGL h)
  )
  (cut : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A}
    (h₁ : ⊢ᶜ (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᶜ (insert A Γ₂ ⟹ Δ₂)),
    (motive (Γ₁ ⟹ insert A Δ₁) h₁) → (motive (insert A Γ₂ ⟹ Δ₂) h₂) →
    motive (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) (ProvableWithCut.cut h₁ h₂)
  )
  : ∀ {S : Sequent} (h : ⊢ᶜ S), motive S h := by
    rintro S ⟨h⟩;
    induction h with
    | axm A => apply axm;
    | botL => apply botL;
    | wkL h h' ih => apply wkL ⟨h⟩ h' ih;
    | wkR h h' ih => apply wkR ⟨h⟩ h' ih;
    | cut h₁ h₂ ih₁ ih₂ => apply cut ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impL h₁ h₂ ih₁ ih₂ => apply impL ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impR h ih => apply impR ⟨h⟩ ih;
    | boxGL h ih => apply boxGL ⟨h⟩ ih;

end ProvableWithCut

lemma provableWithCut_of_provable : ⊢ S → ⊢ᶜ S := λ ⟨p⟩ => ⟨ProvableWithCut.ofProof p⟩

/-- Semantical cut-elimination -/
theorem provable_of_provableWithCut : ⊢ᶜ S → ⊢ S := by
  intro h;
  induction h using ProvableWithCut.rec with
  | axm A => exact Provable.axm A
  | botL => exact Provable.botL
  | wkL _ h ih => exact Provable.wkL ih h
  | wkR _ h ih => exact Provable.wkR ih h
  | impL _ _ ih₁ ih₂ => exact Provable.impL ih₁ ih₂
  | impR _ ih => exact Provable.impR ih
  | boxGL _ ih => exact Provable.boxGL ih
  | cut _ _ ih₁ ih₂ =>
    apply completeness;
    intro κ _ M _ x;
    have := finite_soundness ih₁ M x;
    have := finite_soundness ih₂ M x;
    grind;
alias cut_elimination := provable_of_provableWithCut

namespace Provable

lemma mdp : ⊢ (∅ ⟹ {A 🡒 B}) → ⊢ (∅ ⟹ {A}) → ⊢ (∅ ⟹ {B}) := λ p q => by
  replace p : ⊢ᶜ (insert A ∅ ⟹ {B}) := provableWithCut_of_provable $ deduction_theorem.mpr p;
  replace q : ⊢ᶜ (∅ ⟹ insert A ∅) := provableWithCut_of_provable q;
  exact cut_elimination $ ProvableWithCut.cut q p;

end Provable

abbrev LogicGL := { A | ⊢ (∅ ⟹ {A}) }
