module

public import ProvabilityLogic.ProvabilityLogic.D.Basic
public import ProvabilityLogic.ToFoundation.FirstOrder.Incompleteness.UniformReflection

/-!
# Logic D as the provability logic of `T` extended by two `𝚷₂` sentences

`PL_T(T + {RFN₂(⊥), RFN₂(Pr ⋎ Pr)}) = D`, where the two axioms are the binary uniform reflection
sentences of `ProvabilityLogic.ToFoundation.FirstOrder.Incompleteness.UniformReflection`.

This is the `sorry`-free counterpart of `LogicD.eq_provabilityLogicRelativeTo_localReflection`,
which states the same result for the extension by the full local reflection schema
`Rfn_{𝚺 1}(T)` and still rests on `exists_delta1_strictHierarchy_equiv_localReflection`. The two
sentences here are exactly what the soundness direction consumes — `⊥` for the axiom `P` and
`provOrProv T` for the axiom `D` — and being finitely many `𝚷₂` sentences they fall directly
under `inconsistent_of_localReflectionOnHierarchy_weakerThan_union_of_finite`, with no `Δ₁`
presentation or strict prenex form needed.

## References

- [AB05, Example 60]
- [AB05, Theorem 23]
-/

@[expose] public section

open FFL
open FFL.Entailment
open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction
open FFL.FirstOrder.Arithmetic

namespace LogicD

variable {α : Type*} {A : Formula α}
variable (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- The two `𝚷₂` sentences that suffice for the arithmetical soundness of `D`. -/
abbrev uniformAxioms : FirstOrder.ArithmeticTheory :=
  {uniformReflection₂ T (⊥ : ArithmeticSemisentence 2), uniformReflection₂ T (provOrProv T)}

variable {T}

set_option maxHeartbeats 2000000 in
/--
**Arithmetical soundness of `D`** over the two uniform reflection axioms: the `⊇` half of
`PL_T(T + {RFN₂(⊥), RFN₂(Pr ⋎ Pr)}) = D`.

- [AB05, Example 60]
-/
theorem arithmetical_soundness_uniform (h : A ∈ LogicD) (f : Realization α ℒₒᵣ) :
  (T ∪ uniformAxioms T) ⊢ f T A := by
  have : 𝗜𝚺₁ ⪯ (T ∪ uniformAxioms T : FirstOrder.ArithmeticTheory) :=
    Entailment.WeakerThan.trans (𝓣 := T) inferInstance inferInstance;
  induction h using LogicD.substlessInduction with
  | provable_GL h => exact Entailment.WeakerThan.pbl $ LogicGL.arithmetical_soundness' h;
  | axiomP =>
    have h₁ : (T ∪ uniformAxioms T) ⊢ uniformReflection₂ T (⊥ : ArithmeticSemisentence 2) :=
      Entailment.by_axm (Or.inr (Set.mem_insert _ _));
    have h₂ : (T ∪ uniformAxioms T) ⊢
        uniformReflection₂ T (⊥ : ArithmeticSemisentence 2) 🡒 ∼T.standardProvability ⊥ :=
      Entailment.WeakerThan.pbl (𝓢 := 𝗜𝚺₁) (provable_uniformReflection₂_bot_imp_con T);
    have h₃ : f T (∼□⊥ : Formula α) =
        ((T.standardProvability ⊥ : ArithmeticSentence) 🡒 (⊥ : ArithmeticSentence)) := by
      simp [Formula.interpret];
    rw [h₃];
    cl_prover [h₂ ⨀ h₁];
  | @axiomD A B =>
    have h₁ : (T ∪ uniformAxioms T) ⊢ uniformReflection₂ T (provOrProv T) :=
      Entailment.by_axm (Or.inr (Set.mem_insert_of_mem _ rfl));
    have h₂ := Entailment.WeakerThan.pbl (𝓢 := 𝗜𝚺₁)
      (𝓣 := (T ∪ uniformAxioms T : FirstOrder.ArithmeticTheory))
      (provable_uniformReflection₂_imp_axiomD T (f T A) (f T B));
    simp only [Formula.interpret];
    exact h₂ ⨀ h₁;
  | mdp ihAB ihA => exact ihAB ⨀ ihA;

section completeness

variable (T)

instance models_uniformAxioms [ℕ↓[ℒₒᵣ] ⊧* T] :
  ℕ↓[ℒₒᵣ] ⊧* (T ∪ uniformAxioms T : FirstOrder.ArithmeticTheory) := by
  apply Semantics.modelsSet_iff.mpr;
  rintro φ (hφ | rfl | rfl);
  . exact Semantics.modelsSet_iff.mp inferInstance hφ;
  . exact models_uniformReflection₂ T _;
  . exact models_uniformReflection₂ T _;

omit [𝗜𝚺₁ ⪯ T] in
lemma finite_uniformAxioms : (uniformAxioms T).Finite :=
  Set.finite_insert.mpr (Set.finite_singleton _)

omit [𝗜𝚺₁ ⪯ T] in
lemma hierarchy_uniformAxioms : ∀ σ ∈ uniformAxioms T, Hierarchy 𝚷 2 σ := by
  rintro σ (rfl | rfl);
  . exact hierarchy_uniformReflection₂ T _ (by simp);
  . exact hierarchy_uniformReflection₂ T _ (hierarchy_provOrProv T);

variable {T}

omit [𝗜𝚺₁ ⪯ T] in
/-- Proving every reflection instance is the same as containing `Rfn_{𝚺 2}(T)`. -/
lemma localReflection_weakerThan_of_forall
  (h : ∀ σ : FirstOrder.ArithmeticSentence, (T ∪ uniformAxioms T) ⊢ T.standardProvability σ 🡒 σ) :
  (𝗥𝗳𝗻[𝚺 2] T : FirstOrder.ArithmeticTheory) ⪯ (T ∪ uniformAxioms T) := by
  apply Entailment.WeakerThan.ofAxm!;
  intro φ hφ;
  obtain ⟨σ, -, rfl⟩ := (ProvabilityAbstraction.Provability.mem_localReflectionOn_iff _).mp hφ;
  exact h σ;

variable [DecidableEq α]

/--
**`D` is the provability logic of `T` relative to `T` extended by two `𝚷₂` sentences**, for
`T` sound in the standard model. Unlike
`LogicD.eq_provabilityLogicRelativeTo_localReflection`, this rests on no `sorry`.

- [AB05, Example 60]
-/
theorem eq_provabilityLogicRelativeTo_uniform [ℕ↓[ℒₒᵣ] ⊧* T] :
  @LogicD α = T.provabilityLogicRelativeTo (T ∪ uniformAxioms T) := by
  have : 𝗜𝚺₁ ⪯ (T ∪ uniformAxioms T : FirstOrder.ArithmeticTheory) :=
    Entailment.WeakerThan.trans (𝓣 := T) inferInstance inferInstance;
  have hcon : Entailment.Consistent (T ∪ uniformAxioms T : FirstOrder.ArithmeticTheory) :=
    consistent_of_model _ ℕ;
  apply Set.Subset.antisymm;
  . grind [arithmetical_soundness_uniform];
  . intro A hAL;
    by_contra hAD;
    have h₁ : (T.provabilityLogicRelativeTo (T ∪ uniformAxioms T) : Logic α).trace = Set.univ := by
      apply Set.eq_univ_of_forall;
      intro n;
      exact mem_trace_of_provable_TBB (arithmetical_soundness_uniform provable_TBB);
    have h₂ := provable_reflection_of_mem_not_LogicD (A := A) h₁ hAL hAD;
    exact (inconsistent_of_localReflectionOnHierarchy_weakerThan_union_of_finite
      (Γ := 𝚷) (n := 2) (finite_uniformAxioms T) (hierarchy_uniformAxioms T)
      (localReflection_weakerThan_of_forall h₂)).not_con hcon;

/-- - [AB05, Example 60] -/
theorem eq_provabilityLogic_PA_uniform :
  @LogicD α = 𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ uniformAxioms 𝗣𝗔) :=
  eq_provabilityLogicRelativeTo_uniform

end completeness

end LogicD
