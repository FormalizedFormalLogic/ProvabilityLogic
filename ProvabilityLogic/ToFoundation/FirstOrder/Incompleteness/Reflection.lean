module

public import Foundation.FirstOrder.Incompleteness.Löb

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

/-- If `T` is sound, then `T + Rfn_Γₙ(T)` is sound as well: every local reflection
instance for `T` is true in the standard model. -/
instance models_localReflection [ℕ↓[ℒₒᵣ] ⊧* T] {Γ : Polarity} {n : ℕ}
  : ℕ↓[ℒₒᵣ] ⊧* (T ∪ T.localReflection Γ n) := by
  apply Semantics.modelsSet_iff.mpr;
  rintro φ (hφ | ⟨σ, hσ, rfl⟩);
  . exact Semantics.modelsSet_iff.mp inferInstance hφ;
  . -- if `Pr_T(σ)` holds in `ℕ` then `T ⊢ σ` (`Provability.SoundOn`), hence `σ` is
    -- true by the soundness of `T`.
    have : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability σ) → ℕ↓[ℒₒᵣ] ⊧ σ := fun h =>
      models_of_provable inferInstance (T.standardProvability.sound_on h);
    simpa using this;

/--
  The instance of the **unboundedness theorem**, originally due to Kreisel and Lévy (1968),
  needed for the `⊆` half of Example 60: `T + Rfn_Σ₁(T)`, being a consistent extension
  of `T` by `Π₂`-sentences, cannot prove the full local reflection schema `Rfn(T)`
  (already its `Σ₂`-instances are out of reach).

  - [AB05, Theorem 23]
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
  -- for `Σ₁`-sentences, neither of which is currently available in Foundation. See
  -- `.claude/directions/d-completeness.md` for the detailed analysis.
  suffices key : ∀ π : FirstOrder.ArithmeticSentence,
      T ⊢ (T.standardProvability (∼π)) 🡒 ∼π →
      Entailment.Inconsistent (insert π T : FirstOrder.ArithmeticTheory) by
    sorry
  intro π h1
  have h2 : T ⊢ (∼π) := LO.FirstOrder.Arithmetic.löb_theorem h1
  have h3 : (insert π T : FirstOrder.ArithmeticTheory) ⊢ π := Entailment.by_axm (Set.mem_insert π T)
  have h4 : (insert π T : FirstOrder.ArithmeticTheory) ⊢ (∼π) := Entailment.wk! (Set.subset_insert π T) h2
  exact Entailment.inconsistent_of_provable (by cl_prover [h3, h4])

end

end LO.FirstOrder.ArithmeticTheory
