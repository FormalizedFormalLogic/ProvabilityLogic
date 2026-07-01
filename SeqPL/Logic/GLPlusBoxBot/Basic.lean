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
      sorry;
    | mem₂ hB =>
      sorry;
    | mdp _ _ ihAB ihA =>
      sorry;
    | subst _ ihA =>

      sorry;
  . intro h;
    apply Logic.sumQuasiNormal.mdp;
    . exact Logic.sumQuasiNormal.mem₁ h;
    . exact Logic.sumQuasiNormal.mem₂ rfl;

end
