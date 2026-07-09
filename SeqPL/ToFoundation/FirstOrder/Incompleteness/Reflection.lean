module

public import Foundation.FirstOrder.Incompleteness.StandardProvability

@[expose] public section

open LO
open LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

namespace LO.FirstOrder.ArithmeticTheory

/-- The local reflection schema `Rfn_Γₙ(T) = { Pr_T(σ) 🡒 σ | σ a Γₙ-sentence }` for the
standard provability predicate of `T` (cf. §1.3 of [AB05]). -/
def localReflection
    (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ) :
    FirstOrder.ArithmeticTheory :=
  { (T.standardProvability σ) 🡒 σ | (σ) (_ : Arithmetic.Hierarchy Γ n σ) }

/-- The reflection instance at a `Γₙ`-sentence `σ` belongs to `Rfn_Γₙ(T)`. -/
lemma mem_localReflection
    {T : FirstOrder.ArithmeticTheory} [T.Δ₁] {Γ : Polarity} {n : ℕ}
    {σ : FirstOrder.ArithmeticSentence} (hσ : Arithmetic.Hierarchy Γ n σ) :
    ((T.standardProvability σ) 🡒 σ) ∈ T.localReflection Γ n :=
  ⟨σ, hσ, rfl⟩


section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁]

/-- For sound `T`, every local reflection instance for `T` is true in the standard
model: if `Pr_T(σ)` holds in `ℕ` then `T ⊢ σ` (`Provability.SoundOn`), hence `σ` is
true by the soundness of `T`. So `T + Rfn_Γₙ(T)` is sound as well. -/
instance models_localReflection [ℕ↓[ℒₒᵣ] ⊧* T] {Γ : Polarity} {n : ℕ}
  : ℕ↓[ℒₒᵣ] ⊧* (T ∪ T.localReflection Γ n) := by
  apply Semantics.modelsSet_iff.mpr;
  rintro φ (hφ | ⟨σ, hσ, rfl⟩);
  . exact Semantics.modelsSet_iff.mp inferInstance hφ;
  . have : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability σ) → ℕ↓[ℒₒᵣ] ⊧ σ := fun h =>
      models_of_provable inferInstance (T.standardProvability.sound_on h);
    simpa using this;

/--
  The instance of the **unboundedness theorem** ([AB05] Theorem 23, Kreisel–Lévy 1968)
  needed for the `⊆` half of Example 60: `T + Rfn_Σ₁(T)`, being a consistent extension
  of `T` by `Π₂`-sentences, cannot prove the full local reflection schema `Rfn(T)`
  (already its `Σ₂`-instances are out of reach).

  The proof for a *finite* extension `T + π` (`π ∈ Π₂`) is a three-line Löb argument:
  `T + π ⊢ Pr_T(¬π) 🡒 ¬π` (the instance at the `Σ₂`-sentence `¬π`) gives
  `T ⊢ Pr_T(¬π) 🡒 ¬π` by deduction, hence `T ⊢ ¬π` by Löb's theorem, contradicting
  the consistency of `T + π`. The reduction of the schema case to the finite case is
  the "trick, akin to Rosser's" omitted in [AB05]; it requires an arithmetized
  deduction theorem and a partial truth predicate for `Σ₁`-sentences, neither of which
  is currently available in Foundation. See `.claude/directions/d-completeness.md` for
  the detailed analysis.
-/
theorem unbounded_localReflection
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
  [Entailment.Consistent (T ∪ T.localReflection 𝚺 1)] :
  ¬∀ σ : FirstOrder.ArithmeticSentence, (T ∪ T.localReflection 𝚺 1) ⊢ (T.standardProvability σ) 🡒 σ := by
  sorry

end

end LO.FirstOrder.ArithmeticTheory
