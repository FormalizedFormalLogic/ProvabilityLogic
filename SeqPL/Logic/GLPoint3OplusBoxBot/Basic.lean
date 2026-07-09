module

public import Mathlib.Data.ENat.Basic
public import SeqPL.Logic.GL.Theorems
public import SeqPL.Logic.GLPoint2.Basic
public import SeqPL.Logic.GLPoint3.Basic
meta import SeqPL.Logic.GL.Basic

@[expose]
public section

/-- `GLPoint3OplusBoxBot n`: the normal extension of `GLPoint3` by the boxbot axiom
`□^[n]⊥` for a finite `n`, and `GLPoint3` itself for `n = ∞`. -/
def LogicGLPoint3OplusBoxBot {α} : ℕ∞ → Logic α
  | .some n => LogicGLPoint3 ⊕ᴸ {□^[n]⊥}
  | .none   => LogicGLPoint3

namespace LogicGLPoint3OplusBoxBot

variable {α : Type*} [DecidableEq α] {n : ℕ} {A B C : Formula α}

omit [DecidableEq α] in
/-- `GLPoint3OplusBoxBot n` unfolds to `GLPoint3 ⊕ᴸ {□^[n]⊥}` for finite `n`. -/
@[simp]
lemma eq_some : LogicGLPoint3OplusBoxBot (α := α) (n : ℕ∞) = (LogicGLPoint3 ⊕ᴸ {□^[n]⊥}) := rfl

omit [DecidableEq α] in
/-- Lift a `GLPoint3` theorem into `GLPoint3OplusBoxBot n`. -/
lemma provable_of_provable_GLPoint3 (h : A ∈ LogicGLPoint3) : A ∈ LogicGLPoint3OplusBoxBot n :=
  Logic.sumNormal.mem₁ h

omit [DecidableEq α] in
/-- The boxbot axiom `□^[n]⊥` is provable in `GLPoint3OplusBoxBot n`. -/
lemma boxbot : (□^[n]⊥ : Formula α) ∈ LogicGLPoint3OplusBoxBot n :=
  Logic.sumNormal.mem₂ rfl

/-- `□^[n]A` is provable in `GLPoint3OplusBoxBot n`. -/
lemma axiomNVer : (□^[n]A) ∈ LogicGLPoint3OplusBoxBot n := by
  have himp : (□^[n]⊥ 🡒 □^[n]A) ∈ LogicGLPoint3 := by
    apply LogicGLPoint3.provable_of_provable_GL
    apply ProvableHilbert.Kripke.completeness
    intro κ _ M _ x
    grind
  exact Logic.sumNormal.mdp (provable_of_provable_GLPoint3 himp) boxbot

omit [DecidableEq α] in
/-- Lift a GL theorem into `GLPoint3OplusBoxBot n`. -/
lemma of_GL (h : A ∈ LogicGL) : A ∈ LogicGLPoint3OplusBoxBot n :=
  provable_of_provable_GLPoint3 (LogicGLPoint3.provable_of_provable_GL h)

/-- Transitivity of implication inside `GLPoint3OplusBoxBot n`. -/
lemma imp_trans (hAB : (A 🡒 B) ∈ LogicGLPoint3OplusBoxBot n)
    (hBC : (B 🡒 C) ∈ LogicGLPoint3OplusBoxBot n) : (A 🡒 C) ∈ LogicGLPoint3OplusBoxBot n :=
  Logic.sumNormal.imp_trans (LogicGLPoint3.provable_of_provable_GL LogicGL.imp_trans) hAB hBC

/-- The axiom `◇C 🡒 □C` is provable in `GLPoint3OplusBoxBot 2`. -/
lemma provable_CD : (◇C 🡒 □C) ∈ LogicGLPoint3OplusBoxBot 2 := by
  have c1 : (◇C 🡒 (◇C ⋏ □^[2]C)) ∈ LogicGLPoint3OplusBoxBot 2 := by
    have t : (□^[2]C 🡒 ◇C 🡒 (◇C ⋏ □^[2]C)) ∈ LogicGLPoint3OplusBoxBot 2 := by
      apply of_GL;
      suffices h : (□^[2](#0) 🡒 ◇(#0) 🡒 (◇(#0) ⋏ □^[2](#0))) ∈ @LogicGL ℕ by
        simpa using ProvableHilbert.subst (s := fun _ => C) h;
      native_decide;
    exact Logic.sumNormal.mdp t axiomNVer;
  have c2 : ((◇C ⋏ □^[2]C) 🡒 ∼□(⊡C 🡒 ∼C)) ∈ LogicGLPoint3OplusBoxBot 2 := by
    apply of_GL;
    suffices h : ((◇(#0) ⋏ □^[2](#0)) 🡒 ∼□(⊡(#0) 🡒 ∼(#0))) ∈ @LogicGL ℕ by
      simpa using ProvableHilbert.subst (s := fun _ => C) h;
    native_decide;
  have c3 : (∼□(⊡C 🡒 ∼C) 🡒 □(⊡(∼C) 🡒 C)) ∈ LogicGLPoint3OplusBoxBot 2 := by
    have h3 : (□(⊡C 🡒 ∼C) ⋎ □(⊡(∼C) 🡒 C)) ∈ LogicGLPoint3OplusBoxBot 2 :=
      provable_of_provable_GLPoint3 (LogicGLPoint3.provable_axiomWeakPoint3 (A := C) (B := ∼C));
    have t : ((□(⊡C 🡒 ∼C) ⋎ □(⊡(∼C) 🡒 C)) 🡒 ∼□(⊡C 🡒 ∼C) 🡒 □(⊡(∼C) 🡒 C))
        ∈ LogicGLPoint3OplusBoxBot 2 := by
      apply of_GL;
      suffices h : ((□(⊡(#0) 🡒 ∼(#0)) ⋎ □(⊡(∼(#0)) 🡒 #0)) 🡒 ∼□(⊡(#0) 🡒 ∼(#0)) 🡒 □(⊡(∼(#0)) 🡒 #0))
          ∈ @LogicGL ℕ by
        exact ProvableHilbert.subst (s := fun _ => C) h;
      native_decide;
    exact Logic.sumNormal.mdp t h3;
  have c4 : (□(⊡(∼C) 🡒 C) 🡒 □^[2](∼C) 🡒 □C) ∈ LogicGLPoint3OplusBoxBot 2 := by
    apply of_GL;
    suffices h : (□(⊡(∼(#0)) 🡒 #0) 🡒 □^[2](∼(#0)) 🡒 □(#0)) ∈ @LogicGL ℕ by
      exact ProvableHilbert.subst (s := fun _ => C) h;
    native_decide;
  have chain : (◇C 🡒 □^[2](∼C) 🡒 □C) ∈ LogicGLPoint3OplusBoxBot 2 :=
    imp_trans (imp_trans (imp_trans c1 c2) c3) c4;
  have t : ((◇C 🡒 □^[2](∼C) 🡒 □C) 🡒 □^[2](∼C) 🡒 ◇C 🡒 □C) ∈ LogicGLPoint3OplusBoxBot 2 := by
    apply of_GL;
    suffices h : ((◇(#0) 🡒 □^[2](∼(#0)) 🡒 □(#0)) 🡒 □^[2](∼(#0)) 🡒 ◇(#0) 🡒 □(#0)) ∈ @LogicGL ℕ by
      exact ProvableHilbert.subst (s := fun _ => C) h;
    native_decide;
  exact Logic.sumNormal.mdp (Logic.sumNormal.mdp t chain) axiomNVer;

/-- The convergence axiom `.2` (`WeakPoint2`) is provable in `GLPoint3OplusBoxBot 2`. -/
lemma provable_weakPoint2_in_2 : (◇(□A ⋏ B) 🡒 □(◇A ⋎ B)) ∈ LogicGLPoint3OplusBoxBot 2 := by
  have cdInst : (◇(□A ⋏ B) 🡒 □(□A ⋏ B)) ∈ LogicGLPoint3OplusBoxBot 2 := provable_CD;
  have w : (□(□A ⋏ B) 🡒 □(◇A ⋎ B)) ∈ LogicGLPoint3OplusBoxBot 2 := by
    apply of_GL;
    suffices h : (□(□(#0) ⋏ #1) 🡒 □(◇(#0) ⋎ #1)) ∈ @LogicGL ℕ by
      simpa using ProvableHilbert.subst (s := fun n =>
        match n with
        | 0 => A
        | _ => B
      ) h;
    native_decide;
  exact imp_trans cdInst w;

end LogicGLPoint3OplusBoxBot


/-- `GLPoint3OplusBoxBot 2 = GLPoint2`. -/
lemma eq_GLPoint3OplusBoxBot_2_GLPoint2 [DecidableEq α] :
    LogicGLPoint3OplusBoxBot 2 = (LogicGLPoint2 : Logic α) := by
  have e : LogicGLPoint3OplusBoxBot (α := α) 2 = (LogicGLPoint3 ⊕ᴸ {□^[2]⊥}) := rfl
  rw [e]
  ext A
  constructor
  · intro h
    induction h with
    | mem₁ h => exact LogicGLPoint3_subset_LogicGLPoint2 h
    | mem₂ h =>
      subst h
      exact LogicGLPoint2.provable_boxboxbot
    | mdp _ _ ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA
    | subst _ ih => exact Logic.sumNormal.subst ih
    | nec _ ih => exact Logic.sumNormal.nec ih
  · intro h
    induction h using LogicGLPoint2.substlessInduction with
    | provable_GL h =>
      exact Logic.sumNormal.mem₁ (LogicGLPoint3.provable_of_provable_GL h)
    | axiomWeakPoint2 => exact LogicGLPoint3OplusBoxBot.provable_weakPoint2_in_2
    | mdp ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA
    | nec ih => exact Logic.sumNormal.nec ih

end
