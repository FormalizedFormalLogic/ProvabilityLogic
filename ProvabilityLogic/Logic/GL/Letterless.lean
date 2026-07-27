module

public import ProvabilityLogic.Logic.GL.Basic
public import ProvabilityLogic.Hilbert.GL.Letterless

@[expose]
public section

variable {α : Type u}

open LogicGL

lemma iff_lift_mem_LogicGL {B : LetterlessFormula} :
    (LetterlessFormula.lift B : Formula α) ∈ LogicGL ↔ B ∈ (LogicGL : Logic Empty) := by
  constructor;
  · intro h;
    have := ProvableHilbert.project (α := α) h;
    rwa [Formula.projectEmpty_lift] at this;
  · exact ProvableHilbert.lift;
