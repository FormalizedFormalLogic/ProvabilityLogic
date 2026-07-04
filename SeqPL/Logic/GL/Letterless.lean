module

public import SeqPL.Formula.Letterless
public import SeqPL.Logic.GL.Basic

@[expose]
public section

variable {α : Type u}

lemma ProvableHilbert.project {A : Formula α} (h : ⊢ʰ A) : ⊢ʰ (A.projectEmpty : LetterlessFormula) := by
  induction h using ProvableHilbert.rec with
  | implyK => exact ProvableHilbert.implyK
  | implyS => exact ProvableHilbert.implyS
  | dne => exact ProvableHilbert.dne
  | andElimL => exact ProvableHilbert.andElimL
  | andElimR => exact ProvableHilbert.andElimR
  | andIntro => exact ProvableHilbert.andIntro
  | orIntroL => exact ProvableHilbert.orIntroL
  | orIntroR => exact ProvableHilbert.orIntroR
  | orElim => exact ProvableHilbert.orElim
  | modalK => exact ProvableHilbert.modalK
  | modal4 => exact ProvableHilbert.modal4
  | modalL => exact ProvableHilbert.modalL
  | mdp h₁ h₂ ih₁ ih₂ => exact ProvableHilbert.mdp ih₁ ih₂
  | nec h ih => exact ProvableHilbert.nec ih

lemma ProvableHilbert.lift {B : LetterlessFormula} (h : ⊢ʰ B) : ⊢ʰ (LetterlessFormula.lift B : Formula α) := by
  induction h using ProvableHilbert.rec with
  | implyK => exact ProvableHilbert.implyK
  | implyS => exact ProvableHilbert.implyS
  | dne => exact ProvableHilbert.dne
  | andElimL => exact ProvableHilbert.andElimL
  | andElimR => exact ProvableHilbert.andElimR
  | andIntro => exact ProvableHilbert.andIntro
  | orIntroL => exact ProvableHilbert.orIntroL
  | orIntroR => exact ProvableHilbert.orIntroR
  | orElim => exact ProvableHilbert.orElim
  | modalK => exact ProvableHilbert.modalK
  | modal4 => exact ProvableHilbert.modal4
  | modalL => exact ProvableHilbert.modalL
  | mdp h₁ h₂ ih₁ ih₂ => exact ProvableHilbert.mdp ih₁ ih₂
  | nec h ih => exact ProvableHilbert.nec ih

lemma iff_lift_mem_LogicGL {B : LetterlessFormula} :
    (LetterlessFormula.lift B : Formula α) ∈ LogicGL ↔ B ∈ (LogicGL : Logic Empty) := by
  constructor;
  · intro h;
    have := ProvableHilbert.project (α := α) h;
    rwa [Formula.projectEmpty_lift] at this;
  · exact ProvableHilbert.lift;
