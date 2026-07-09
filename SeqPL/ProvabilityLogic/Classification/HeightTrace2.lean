module

public import SeqPL.ProvabilityLogic.Classification.Result
public import SeqPL.ProvabilityLogic.Classification.A_D
public import SeqPL.ProvabilityLogic.Classification.HeightTrace

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

section soundOnHierarchy

omit [𝗜𝚺₁ ⪯ T] in
/--
  If `T` is `Σ₁`-sound, then the `Σ₁`-reflection instance for `T` is true in the standard
  model, for any `Σ₁` sentence `σ`.
-/
lemma models_standardProvability_imp_of_soundOnHierarchy [T.SoundOnHierarchy 𝚺 1]
    {σ : ArithmeticSentence} (hσ : LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 σ) :
    ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability σ) 🡒 σ) := by
  rw [Semantics.Imp.models_imply];
  intro h;
  exact ArithmeticTheory.soundOnHierarchy T 𝚺 1 (models_standardProvability_iff.mp h) hσ;

omit [𝗜𝚺₁ ⪯ T] in
/--
  Converse of `models_standardProvability_imp_of_soundOnHierarchy`: if every `Σ₁`-reflection
  instance for `T` is true in the standard model, then `T` is `Σ₁`-sound.
-/
lemma soundOnHierarchy_of_models_standardProvability_imp
    (h : ∀ {σ : ArithmeticSentence}, LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 σ →
      ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability σ) 🡒 σ)) :
    T.SoundOnHierarchy 𝚺 1 := by
  constructor;
  intro σ hTσ hσ;
  exact (Semantics.Imp.models_imply.mp (h hσ)) (models_standardProvability_iff.mpr hTσ);

end soundOnHierarchy


section LogicD_TA

/--
  **Half of Corollary 41(ii) in [AB05]**: if `T` is `Σ₁`-sound, then `D` is contained in
  the truth provability logic of `T`. Mimics the case split on the generators of `D`
  (`GL`-fragment, axiom `P`, axiom `D`, `mdp`) used for
  `subset_LogicD_of_ssubset_LogicA_of_univ_trace`, but derives truth in the standard
  model directly in each case rather than provability in an extended theory.
-/
lemma LogicD_subset_provabilityLogicRelativeTo_TA [T.SoundOnHierarchy 𝚺 1] :
    (LogicD : Logic α) ⊆ T.provabilityLogicRelativeTo 𝗧𝗔 := by
  intro A hA;
  induction hA using LogicD.substlessInduction with
  | provable_GL h => exact provabilityLogic_of_GL h;
  | axiomP =>
    intro f;
    apply Arithmetic.TA.provable_iff.mpr;
    have e : Formula.interpret f (∼□⊥ : Formula α)
        = (T.standardProvability (⊥ : ArithmeticSentence)) 🡒 ⊥ := by
      simp [Formula.interpret];
    rw [e, Semantics.Imp.models_imply];
    intro h;
    exact absurd (models_standardProvability_iff.mp h)
      (inferInstance : Entailment.Consistent T).not_bot;
  | @axiomD B C =>
    intro f;
    apply Arithmetic.TA.provable_iff.mpr;
    have hσ : LO.FirstOrder.Arithmetic.Hierarchy 𝚺 1 (f (((□B) ⋎ (□C) : Formula α))) := by
      simp [Formula.interpret, Arithmetic.standardProvability_def];
    have hrfl := models_standardProvability_imp_of_soundOnHierarchy (T := T) hσ;
    simpa [Formula.interpret] using hrfl;
  | mdp ihAB ihA => exact provabilityLogic_mdp ihAB ihA;

end LogicD_TA

end
