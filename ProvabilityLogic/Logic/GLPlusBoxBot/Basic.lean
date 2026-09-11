module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height
public import ProvabilityLogic.Logic.GL.Basic

@[expose] public section

open Classical
open FFL
open FFL.FirstOrder.ProvabilityAbstraction
open LogicGL
open Logic.sumQuasiNormal

/-- `LogicGLPlusBoxBot n`: the quasi-normal extension of `GL` by the boxbot axiom `□^[n]⊥`
for a finite `n`, and `GL` itself for `n = ∞`. -/
def LogicGLPlusBoxBot {α} : ℕ∞ → Logic α
  | .some n => LogicGL +ᴸ □^[n]⊥
  | .none   => LogicGL

@[grind =]
lemma LogicGLPlusBoxBot.iff_provable_provable_GL {n : ℕ} :
  A ∈ LogicGLPlusBoxBot n ↔ (□^[n]⊥ 🡒 A) ∈ LogicGL := by
  constructor;
  . intro h;
    induction h with
    | mem₁ hA => exact ProvableHilbert.af hA;
    | mem₂ hB => subst hB; exact ProvableHilbert.impId;
    | mdp _ _ ihAB ihA => exact ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.prop2 ihAB) ihA;
    | subst _ ihA => simpa using ProvableHilbert.subst ihA;
  . intro h;
    exact mdp (mem₁ h) (mem₂ rfl);

end
