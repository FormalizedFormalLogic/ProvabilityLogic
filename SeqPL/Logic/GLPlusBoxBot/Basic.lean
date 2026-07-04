module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height
public import SeqPL.Logic.GL.Basic
public import SeqPL.Logic.SumQuasiNormal

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

def LogicGLPlusBoxBot {α} : ℕ∞ → Logic α
  | .some n => LogicGL +ᴸ □^[n]⊥
  | .none   => LogicGL

lemma LogicGLPlusBoxBot.iff_provable_provable_GL {n : ℕ} : A ∈ LogicGLPlusBoxBot n ↔ (□^[n]⊥ 🡒 A) ∈ LogicGL := by
  constructor;
  . intro h;
    induction h with
    | mem₁ hA =>
      exact ProvableHilbert.af hA;
    | mem₂ hB =>
      subst hB;
      exact ProvableHilbert.impId;
    | mdp _ _ ihAB ihA =>
      exact ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.prop2 ihAB) ihA;
    | subst _ ihA =>
      simpa using ProvableHilbert.subst ihA;
  . intro h;
    apply Logic.sumQuasiNormal.mdp;
    . exact Logic.sumQuasiNormal.mem₁ h;
    . exact Logic.sumQuasiNormal.mem₂ rfl;

end
