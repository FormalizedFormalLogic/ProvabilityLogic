module

public import Foundation.FirstOrder.Incompleteness.Löb

@[expose] public section

open FFL
open FFL.Entailment
open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction

namespace FFL.FirstOrder.ArithmeticTheory

/-- The local reflection schema `Rfn_Γₙ(T) = { Pr_T(σ) 🡒 σ | σ a Γₙ-sentence }` for the
standard provability predicate of `T`.

- [AB05, §1.3]
-/
def localReflection
    (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ) :
    FirstOrder.ArithmeticTheory :=
  { (T.standardProvability σ) 🡒 σ | (σ) (_ : Arithmetic.Hierarchy Γ n σ) }

lemma mem_localReflection
    {T : FirstOrder.ArithmeticTheory} [T.Δ₁] {Γ : Polarity} {n : ℕ}
    {σ : FirstOrder.ArithmeticSentence} (hσ : Arithmetic.Hierarchy Γ n σ) :
    ((T.standardProvability σ) 🡒 σ) ∈ T.localReflection Γ n :=
  ⟨σ, hσ, rfl⟩


section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁]

instance models_localReflection [ℕ↓[ℒₒᵣ] ⊧* T] {Γ : Polarity} {n : ℕ}
  : ℕ↓[ℒₒᵣ] ⊧* (T ∪ T.localReflection Γ n) := by
  apply Semantics.modelsSet_iff.mpr;
  rintro φ (hφ | ⟨σ, hσ, rfl⟩);
  . exact Semantics.modelsSet_iff.mp inferInstance hφ;
  . have : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability σ) → ℕ↓[ℒₒᵣ] ⊧ σ := fun h =>
      models_of_provable inferInstance (T.standardProvability.sound_on h);
    simpa using this;

/-- The **unboundedness theorem**: `T + Rfn_Σ₁(T)`, being a consistent extension of `T` by
`Π₂`-sentences, does not prove the full local reflection schema `Rfn(T)` — already its
`Σ₂`-instances are out of reach.

- [AB05, Theorem 23]
- [KL68]
-/
theorem unbounded_localReflection
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
  [Entailment.Consistent (T ∪ T.localReflection 𝚺 1)] :
  ¬∀ σ : FirstOrder.ArithmeticSentence, (T ∪ T.localReflection 𝚺 1) ⊢ (T.standardProvability σ) 🡒 σ := by
  intro h
  -- It suffices to reduce the schema `T + Rfn_Σ₁(T)` to a *finite* extension `T + π`
  -- (`π ∈ Π₂`): every reflection instance provable from the schema is already provable
  -- from finitely many of its instances, and finitely many `Σ₂`-instances (in particular
  -- the one at `∼π` for a suitable `Π₂`-sentence `π`) can be packaged into a single
  -- `Π₂`-sentence `π` by conjunction. This is the "trick, akin to Rosser's" omitted in
  -- [AB05]; it requires an arithmetized deduction theorem and a partial truth predicate
  -- for `Σ₁`-sentences, neither of which is currently available in Foundation.
  suffices key : ∀ π : FirstOrder.ArithmeticSentence,
      T ⊢ (T.standardProvability (∼π)) 🡒 ∼π →
      Entailment.Inconsistent (insert π T : FirstOrder.ArithmeticTheory) by
    sorry
  intro π h1
  have h2 : T ⊢ (∼π) := FFL.FirstOrder.Arithmetic.löb_theorem h1
  have h3 : (insert π T : FirstOrder.ArithmeticTheory) ⊢ π := Entailment.by_axm (Set.mem_insert π T)
  have h4 : (insert π T : FirstOrder.ArithmeticTheory) ⊢ (∼π) := Entailment.wk! (Set.subset_insert π T) h2
  exact Entailment.inconsistent_of_provable (by cl_prover [h3, h4])

end

end FFL.FirstOrder.ArithmeticTheory
