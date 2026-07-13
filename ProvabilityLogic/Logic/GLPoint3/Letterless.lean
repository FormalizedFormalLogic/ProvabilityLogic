module

public import ProvabilityLogic.Logic.GLPoint3.Completeness
public import ProvabilityLogic.ProvabilityLogic.Classification.LetterlessTrace

@[expose]
public section

/-- The finite line model is a finite linear GL model, being a strict linear order. -/
instance {n : ℕ} : (finiteLineModel n).toModel.IsFiniteGLPoint3 where
  toIsFiniteGL := inferInstance
  linear _ _ := lt_trichotomy _ _

namespace LogicGLPoint3

variable {α : Type u}

/-- Collapsing all atoms to `⊥` preserves `LogicGLPoint3`-provability. -/
lemma projectEmpty_of_provable {A : Formula α} (h : A ∈ LogicGLPoint3) :
    (A.projectEmpty : LetterlessFormula) ∈ LogicGLPoint3 (α := Empty) := by
  induction h using LogicGLPoint3.substlessInduction with
  | provable_GL h => exact provable_of_provable_GL (ProvableHilbert.project h);
  | axiomWeakPoint3 => exact provable_axiomWeakPoint3;
  | mdp ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA;
  | nec ih => exact Logic.sumNormal.nec ih;

/-- Over letterless formulas, `LogicGLPoint3` and `LogicGL` prove exactly the same formulas.

- [SV82, Theorem 2]
-/
theorem eq_LogicGL_on_letterless : @LogicGLPoint3 Empty = @LogicGL Empty := by
  apply Set.ext;
  intro A;
  constructor;
  . intro h;
    apply iff_GL_proves_spectrum_univ.mpr;
    rw [Set.eq_univ_iff_forall];
    intro n;
    have hforces : (finiteLineModel n).root.1 ⊩ A :=
      LogicGLPoint3.sound (M := (finiteLineModel n).toModel) h _;
    have := Model.iff_forces_rank_mem_spectrum.mp hforces;
    rwa [show ((finiteLineModel n).root.1).rank = n from finiteLineModel.height_eq] at this;
  . exact provable_of_provable_GL;

/-- On letterless formulas lifted into an arbitrary `α`, `LogicGLPoint3` proves exactly what `LogicGL` proves.

- [SV82, Theorem 2]
-/
theorem iff_provable_GLPoint3_provable_GL_of_letterless {A : LetterlessFormula} :
    (LetterlessFormula.lift A : Formula α) ∈ LogicGLPoint3 ↔
    (LetterlessFormula.lift A : Formula α) ∈ LogicGL := by
  constructor;
  . intro h;
    apply iff_lift_mem_LogicGL.mpr;
    have := projectEmpty_of_provable h;
    rw [Formula.projectEmpty_lift] at this;
    rwa [eq_LogicGL_on_letterless] at this;
  . exact provable_of_provable_GL;

end LogicGLPoint3

end
