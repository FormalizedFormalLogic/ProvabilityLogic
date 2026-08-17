module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import ProvabilityLogic.Logic.GL.Basic

@[expose] public section

open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T U : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

/-- A realization mapping modal propositional variables to first-order sentences. -/
structure Realization (α : Type*) (L : FirstOrder.Language) where
  val : α → FirstOrder.Sentence L


namespace Formula

-- `{T₀ T}` are bound after `f` so that the coercion below can be `interpret` itself: routing it
-- through a lambda leaves a beta-redex in every statement written as `f 𝔅 A`.
@[grind]
def interpret (f : Realization α L) {T₀ T : FirstOrder.Theory L} (𝔅 : Provability T₀ T) :
  Formula α → FirstOrder.Sentence L
  | #a    => f.val a
  | ⊥     => ⊥
  | A 🡒 B => (A.interpret f 𝔅) 🡒 (B.interpret f 𝔅)
  | □A    => 𝔅 (A.interpret f 𝔅)

instance : CoeFun (Realization α L)
  (fun _ ↦ ∀ {T₀ T : FirstOrder.Theory L}, Provability T₀ T → Formula α → FirstOrder.Sentence L) :=
  ⟨interpret⟩

noncomputable abbrev standardInterpret (f : Realization α _) (T : FirstOrder.ArithmeticTheory)
  [T.Δ₁] := interpret f T.standardProvability

variable {f : Realization α L} {A : Formula α}

@[simp, grind =]
lemma interpret_boxItr {n : ℕ} : f 𝔅 (□^[n]A) = 𝔅^[n] (f 𝔅 A) := by
  induction n with
  | zero => simp [Formula.boxItr];
  | succ n ih => simp only [boxItr, Function.iterate_succ_apply', interpret, ih];

end Formula


section interpret_map

variable {β : Type*}

/-- Interpreting a renamed formula is interpreting under the pulled-back realization. -/
lemma Formula.interpret_map {f : Realization β L} {g : α → β} {A : Formula α} :
  f 𝔅 (A.map g) = (⟨f.val ∘ g⟩ : Realization α L) 𝔅 A := by
  induction A with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [Formula.subst_imp, Formula.interpret, ihA, ihB]
  | box A ih => simp only [Formula.subst_box, Formula.interpret, ih]

/-- Two realizations agreeing on the atoms of `A` interpret `A` identically. -/
lemma Formula.interpret_congr_atoms [DecidableEq α] {f₁ f₂ : Realization α L} {A : Formula α}
    (h : ∀ a ∈ A.atoms, f₁.val a = f₂.val a) :
    f₁ 𝔅 A = f₂ 𝔅 A := by
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
lemma Formula.interpret_subst {f : Realization α L} {s : Formula.Substitution α α} {A : Formula α} :
  f 𝔅 (A⟦s⟧) = (⟨fun a ↦ f 𝔅 (s a)⟩ : Realization α L) 𝔅 A := by
  induction A with
  | atom a => rfl
  | _ => simp_all [Formula.interpret, Formula.subst_imp, Formula.subst_box]

/-- Realizations that agree on every atom up to `T₀`-provable equivalence interpret every
formula equivalently. -/
lemma Formula.interpret_iff_congr [L.DecidableEq] [T₀ ⪯ T] [𝔅.Ext] {f₁ f₂ : Realization α L}
    (h : ∀ a, T₀ ⊢ (f₁.val a) 🡘 (f₂.val a)) (A : Formula α) :
    T₀ ⊢ (f₁ 𝔅 A) 🡘 (f₂ 𝔅 A) := by
  induction A with
  | atom a => exact h a
  | bot => dsimp [Formula.interpret]; cl_prover
  | imp A B ihA ihB => dsimp [Formula.interpret]; cl_prover [ihA, ihB]
  | box A ih => exact 𝔅.ext' ih

/-- The interpretation of `⊡A` is `T`-provably equivalent to `(f 𝔅 A) ⋏ 𝔅 (f 𝔅 A)`. -/
lemma Formula.interpret_boxdot_inside [L.DecidableEq] {f : Realization α L} {A : Formula α} :
    T ⊢ f 𝔅 (⊡A) 🡘 (f 𝔅 A) ⋏ 𝔅 (f 𝔅 A) := by
  dsimp [Formula.interpret];
  cl_prover;

end interpret_map


abbrev LetterlessRealization (L) := Realization Empty L

namespace LetterlessFormula

variable {A B : LetterlessFormula} {f f₁ f₂ : LetterlessRealization L}

@[grind .]
lemma eq_interpret : f₁ 𝔅 A = f₂ 𝔅 A := by induction A <;> grind;

@[grind .]
lemma iff_provable_interpret : T ⊢ f₁ 𝔅 A ↔ T ⊢ f₂ 𝔅 A := by
  rw [eq_interpret];

end LetterlessFormula



@[grind]
def LO.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α :=
  {A | ∀ f : Realization α ℒₒᵣ, U ⊢ A.standardInterpret f T}

abbrev LO.FirstOrder.ArithmeticTheory.provabilityLogic (T : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T



end
