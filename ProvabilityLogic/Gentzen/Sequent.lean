module

public import ProvabilityLogic.Formula.Basic

/-!
This file defines the two-sided sequent `Γ ⟹ Δ`. Every sequent calculus in this repository
(`GL`, `Grz`, `S`, `GL.3`) shares this type.
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

structure Sequent (α : Type u) where
  ant : FormulaFinset α
  suc : FormulaFinset α

infix:50 " ⟹ " => Sequent.mk

namespace Sequent

@[grind]
def subfmls (S : Sequent α) : Finset (Formula α) := S.ant.subfmls ∪ S.suc.subfmls

structure subset (S T : Sequent α) : Prop where
  ant_subset : S.ant ⊆ T.ant
  suc_subset : S.suc ⊆ T.suc

instance : HasSubset (Sequent α) := ⟨subset⟩

variable {S : Sequent α}

@[grind .] lemma subset_self_subfmls : S.ant ∪ S.suc ⊆ S.subfmls := by grind;

@[grind →]
lemma mem_subfmls_subfmls {S : Sequent α} {B C : Formula α} (hB : B ∈ S.subfmls) (hC : C ∈ B.subfmls) : C ∈ S.subfmls := by
  simp only [Sequent.subfmls, Finset.mem_union] at hB ⊢
  grind [FormulaFinset.mem_subfmls_subfmls]

structure Saturated (S : Sequent α) where
  impL : ∀ {A B}, A 🡒 B ∈ S.1 → A ∈ S.2 ∨ B ∈ S.1
  impR : ∀ {A B}, A 🡒 B ∈ S.2 → A ∈ S.1 ∧ B ∈ S.2

end Sequent

/-- A `Sequent` with a level `l : Fin 2`, used by the two-level sequent calculi for `S` and `A`. -/
structure TwoLayeredSequent (α : Type u) extends Sequent α where
  level : Fin 2
notation:50 Γ:51 " ⟹[" l "] " Δ:51 => TwoLayeredSequent.mk (Γ ⟹ Δ) l

end
