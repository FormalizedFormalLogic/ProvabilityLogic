module

public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height
public import SeqPL.Logic.Basic
public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Arithmetic.Interpret

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL]
variable {A : Formula α}
         {f : Realization α 𝔅}

def LogicGLPlusBoxBot {α} : ℕ∞ → Logic α
  | .some n => LogicGL α +ᴸ □^[n]⊥
  | .none   => LogicGL α

lemma LogicGL.arithmetical_soundness (hA : A ∈ LogicGL _)  : U ⊢ f A := by
  replace hA := LogicGL_TFAE.out 0 1 |>.mp hA;
  induction hA with
  | nec _ ihA => exact Entailment.WeakerThan.pbl $ 𝔅.D1 ihA;
  | mdp _ _ ihAB ihA => exact ihAB ⨀ ihA;
  | modalK => exact Entailment.WeakerThan.pbl $ 𝔅.D2;
  | modal4 => exact Entailment.WeakerThan.pbl $ 𝔅.D3;
  | modalL => exact Entailment.WeakerThan.pbl $ formalized_löb_theorem;
  | _ =>
    dsimp [Formula.interpret];
    cl_prover;

lemma LogicGLPlusBoxBot.iff_provable_provable_GL {n : ℕ} : A ∈ LogicGLPlusBoxBot n ↔ (□^[n]⊥ 🡒 A) ∈ LogicGL _ := by
  constructor;
  . intro h;
    induction h with
    | mem₁ hA =>
      sorry;
    | mem₂ hB =>
      sorry;
    | mdp _ _ ihAB ihA =>
      sorry;
    | subst _ ihA => sorry;
  . intro h;
    apply Logic.sumQuasiNormal.mdp;
    . exact Logic.sumQuasiNormal.mem₁ h;
    . exact Logic.sumQuasiNormal.mem₂ rfl;

lemma LogicGLPlusBoxBot.arithmetical_soundness (hA : A ∈ LogicGLPlusBoxBot 𝔅.height) {f : Realization α 𝔅} : U ⊢ f A := by
  cases h : 𝔅.height
  case _ =>
    simp [LogicGLPlusBoxBot, h] at hA;
    exact LogicGL.arithmetical_soundness $ hA;
  case _ n =>
    have : U ⊢ f (□^[n]⊥) 🡒 f A := LogicGL.arithmetical_soundness $ LogicGLPlusBoxBot.iff_provable_provable_GL.mp $ h ▸ hA;
    apply this ⨀ ?_;
    rw [Formula.interpret_boxItr];
    apply 𝔅.height_le_iff_boxBot.mp;
    simp_all;

end
