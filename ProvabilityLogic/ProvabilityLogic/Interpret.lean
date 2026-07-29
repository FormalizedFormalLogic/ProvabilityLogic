module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import ProvabilityLogic.Logic.GL.Basic

@[expose] public section

open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T U : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

/-- A realization mapping modal propositional variables to first-order sentences. -/
structure Realization (α : Type*) (𝔅 : Provability T₀ T) where
  val : α → FirstOrder.Sentence L

abbrev StandardRealization (α : Type*) (T : FirstOrder.ArithmeticTheory) [T.Δ₁] := Realization α T.standardProvability


namespace Formula

@[grind]
def interpret (f : Realization α 𝔅) : Formula α → FirstOrder.Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => (A.interpret f) 🡒 (B.interpret f)
  | □A    => 𝔅 (A.interpret f)

instance : CoeFun (Realization α 𝔅) (fun _ ↦ Formula α → FirstOrder.Sentence L) := ⟨interpret⟩

variable {f : Realization α 𝔅} {A : Formula α}

@[simp, grind =]
lemma interpret_boxItr {n : ℕ} : (□^[n]A).interpret f = 𝔅^[n] (f A) := by
  induction n with
  | zero => simp [Formula.boxItr];
  | succ n ih => simp only [boxItr, Function.iterate_succ_apply', interpret, ih];

end Formula


section interpret_map

variable {β : Type*}

/-- Interpreting a renamed formula is interpreting under the pulled-back realization. -/
lemma Formula.interpret_map {f : Realization β 𝔅} {g : α → β} {A : Formula α} :
    Formula.interpret f (A.map g) = Formula.interpret (⟨f.val ∘ g⟩ : Realization α 𝔅) A := by
  induction A with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [Formula.subst_imp, Formula.interpret, ihA, ihB]
  | box A ih => simp only [Formula.subst_box, Formula.interpret, ih]

/-- Two realizations agreeing on the atoms of `A` interpret `A` identically. -/
lemma Formula.interpret_congr_atoms [DecidableEq α] {f₁ f₂ : Realization α 𝔅} {A : Formula α}
    (h : ∀ a ∈ A.atoms, f₁.val a = f₂.val a) :
    Formula.interpret f₁ A = Formula.interpret f₂ A := by
  induction A with
  | atom a => exact h a (by simp [Formula.atoms])
  | bot => rfl
  | imp A B ihA ihB =>
    simp only [Formula.interpret];
    rw [ihA (fun a ha => h a (by simp [Formula.atoms, ha])),
      ihB (fun a ha => h a (by simp [Formula.atoms, ha]))];
  | box A ih =>
    simp only [Formula.interpret];
    rw [ih (fun a ha => h a (by simpa [Formula.atoms] using ha))];

/-- Interpreting a substituted formula is interpreting under the realization composed with
the substitution's own interpretation. -/
lemma Formula.interpret_subst {f : Realization α 𝔅} {s : Formula.Substitution α α} {A : Formula α} :
    Formula.interpret f (A⟦s⟧) = Formula.interpret (⟨fun a => Formula.interpret f (s a)⟩ : Realization α 𝔅) A := by
  induction A with
  | atom a => rfl
  | _ => simp_all [Formula.interpret, Formula.subst_imp, Formula.subst_box]

/-- Realizations that agree on every atom up to `T₀`-provable equivalence interpret every
formula equivalently. -/
lemma Formula.interpret_iff_congr [L.DecidableEq] [T₀ ⪯ T] [𝔅.Ext] {f₁ f₂ : Realization α 𝔅}
    (h : ∀ a, T₀ ⊢ (f₁.val a) 🡘 (f₂.val a)) (A : Formula α) :
    T₀ ⊢ (f₁ A) 🡘 (f₂ A) := by
  induction A with
  | atom a => exact h a
  | bot => dsimp [Formula.interpret]; cl_prover
  | imp A B ihA ihB => dsimp [Formula.interpret]; cl_prover [ihA, ihB]
  | box A ih => exact 𝔅.ext' ih

/-- The interpretation of `⊡A` is `T`-provably equivalent to `(f A) ⋏ 𝔅 (f A)`. -/
lemma Formula.interpret_boxdot_inside [L.DecidableEq] {f : Realization α 𝔅} {A : Formula α} :
    T ⊢ f (⊡A) 🡘 (f A) ⋏ 𝔅 (f A) := by
  dsimp [Formula.interpret];
  cl_prover;

end interpret_map


abbrev LetterlessRealization (𝔅 : Provability T₀ T) := Realization Empty 𝔅

namespace LetterlessFormula

variable {A B : LetterlessFormula} {f f₁ f₂ : LetterlessRealization 𝔅}

@[grind .]
lemma eq_interpret : f₁ A = f₂ A := by induction A <;> grind;

@[grind .]
lemma iff_provable_interpret : T ⊢ f₁ A ↔ T ⊢ f₂ A := by
  rw [eq_interpret];

end LetterlessFormula



@[grind]
def LO.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := {A | ∀ f : StandardRealization α T, U ⊢ f A}

abbrev LO.FirstOrder.ArithmeticTheory.provabilityLogic (T : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T



end
