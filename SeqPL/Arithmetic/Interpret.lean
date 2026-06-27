module

public import Foundation.FirstOrder.Incompleteness.StandardProvability
public import SeqPL.Formula.Letterless

@[expose] public section

open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {α : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T U : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

/-- Mapping modal prop vars to first-order sentence -/
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

end Formula


abbrev LetterlessRealization (𝔅 : Provability T₀ T) := Realization Empty 𝔅

namespace LetterlessFormula

variable {A B : LetterlessFormula} {f f₁ f₂ : LetterlessRealization 𝔅}

@[grind .]
lemma eq_interpret : f₁ A = f₂ A := by induction A <;> grind;

@[grind .]
lemma iff_provable_interpret : T ⊢ f₁ A ↔ T ⊢ f₂ A := by
  rw [eq_interpret];

end LetterlessFormula





end
