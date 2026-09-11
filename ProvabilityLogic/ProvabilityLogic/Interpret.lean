module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import ProvabilityLogic.Logic.GL.Basic

@[expose] public section

open FFL
open FFL.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T U : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

/-- A realization mapping modal propositional variables to first-order sentences. -/
structure Realization (α : Type*) (L : FirstOrder.Language) where
  val : α → FirstOrder.Sentence L


namespace Formula

@[grind]
def interpret (f : Realization α L) {T₀ T : FirstOrder.Theory L} (𝔅 : Provability T₀ T) :
  Formula α → FirstOrder.Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => (A.interpret f 𝔅) 🡒 (B.interpret f 𝔅)
  | □A    => 𝔅 (A.interpret f 𝔅)

-- `T` and `[T.Δ₁]` are bound after `f` so that the coercion below can be `standardInterpret`
-- itself: routing it through a lambda leaves a beta-redex in every statement written as `f T A`.
noncomputable abbrev standardInterpret (f : Realization α _) (T : FirstOrder.ArithmeticTheory)
  [T.Δ₁] := interpret f T.standardProvability

/-- The standard interpretation is the default reading of a realization: `f T A` means
`A.standardInterpret f T`. The generic one is written explicitly as `A.interpret f 𝔅`. -/
noncomputable instance : CoeFun (Realization α ℒₒᵣ)
  (fun _ ↦ (T : FirstOrder.ArithmeticTheory) → [T.Δ₁] → Formula α → FirstOrder.Sentence ℒₒᵣ) :=
  ⟨standardInterpret⟩

variable {f : Realization α L} {A : Formula α}

@[simp, grind =]
lemma interpret_boxItr {n : ℕ} : (□^[n]A).interpret f 𝔅 = 𝔅^[n] (A.interpret f 𝔅) := by
  induction n with
  | zero => simp [Formula.boxItr];
  | succ n ih => simp only [boxItr, Function.iterate_succ_apply', interpret, ih];

end Formula


namespace Formula

variable {β : Type*}

lemma interpret_map {f : Realization β L} {g : α → β} {A : Formula α} :
  (A.map g).interpret f 𝔅 = A.interpret (⟨f.val ∘ g⟩ : Realization α L) 𝔅 := by
  induction A with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [subst_imp, interpret, ihA, ihB]
  | box A ih => simp only [subst_box, interpret, ih]

lemma interpret_congr_atoms [DecidableEq α] {f₁ f₂ : Realization α L} {A : Formula α}
  (h : ∀ a ∈ A.atoms, f₁.val a = f₂.val a) :
  A.interpret f₁ 𝔅 = A.interpret f₂ 𝔅 := by
  induction A with
  | atom a => exact h a (by simp [atoms])
  | bot => rfl
  | imp A B ihA ihB =>
    simp only [interpret];
    rw [ihA (fun a ha => h a (by simp [atoms, ha])),
      ihB (fun a ha => h a (by simp [atoms, ha]))];
  | box A ih =>
    simp only [interpret];
    rw [ih (fun a ha => h a (by simpa [atoms] using ha))];

lemma interpret_subst {f : Realization α L} {s : Substitution α α} {A : Formula α} :
  (A⟦s⟧).interpret f 𝔅 = A.interpret (⟨fun a ↦ (s a).interpret f 𝔅⟩ : Realization α L) 𝔅 := by
  induction A with
  | atom a => rfl
  | _ => simp_all [interpret, subst_imp, subst_box]

lemma interpret_iff_congr [L.DecidableEq] [T₀ ⪯ T] [𝔅.Ext] {f₁ f₂ : Realization α L}
  (h : ∀ a, T₀ ⊢ (f₁.val a) 🡘 (f₂.val a)) (A : Formula α) :
  T₀ ⊢ (A.interpret f₁ 𝔅) 🡘 (A.interpret f₂ 𝔅) := by
  induction A with
  | atom a => exact h a
  | bot => dsimp [interpret]; cl_prover
  | imp A B ihA ihB => dsimp [interpret]; cl_prover [ihA, ihB]
  | box A ih => exact 𝔅.ext' ih

lemma interpret_boxdot_inside [L.DecidableEq] {f : Realization α L} {A : Formula α} :
  T ⊢ (⊡A).interpret f 𝔅 🡘 (A.interpret f 𝔅) ⋏ 𝔅 (A.interpret f 𝔅) := by
  dsimp [interpret];
  cl_prover;

end Formula


abbrev LetterlessRealization (L) := Realization Empty L

namespace LetterlessFormula

variable {A B : LetterlessFormula} {f f₁ f₂ : LetterlessRealization L}

@[grind .]
lemma eq_interpret : A.interpret f₁ 𝔅 = A.interpret f₂ 𝔅 := by induction A <;> grind;

@[grind .]
lemma iff_provable_interpret : T ⊢ A.interpret f₁ 𝔅 ↔ T ⊢ A.interpret f₂ 𝔅 := by
  rw [eq_interpret];

end LetterlessFormula



@[grind]
def FFL.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α :=
  {A | ∀ f : Realization α ℒₒᵣ, U ⊢ f T A}

abbrev FFL.FirstOrder.ArithmeticTheory.provabilityLogic (T : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T



end
