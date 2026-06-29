module

public import SeqPL.ProvabilityLogic.GL.Basic
public import SeqPL.Logic.GLPlusBoxBot.Basic

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {κ : Type*} [Nonempty κ]
         {α : Type*}
         {A B : _root_.Formula α}

namespace LogicGLPlusBoxBot

section

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL] {f : Realization α 𝔅}

lemma arithmetical_soundness (hA : A ∈ LogicGLPlusBoxBot 𝔅.height) {f : Realization α 𝔅} : U ⊢ f A := by
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

section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]
variable {M : RootedModel κ α}

theorem arithmetical_completeness {n : ℕ∞} (hn : n ≤ T.height)
  (h : ∀ f : StandardRealization α T, T ⊢ f A) : A ∈ LogicGLPlusBoxBot n := by
  match n with
  | .none =>
    apply LogicGL.arithmetical_completeness_of_infinity_height (T := T) ?_ h;
    exact eq_top_iff.mpr hn;
  | .some n =>
    apply LogicGLPlusBoxBot.iff_provable_provable_GL.mpr;
    apply LogicGL.arithmetical_completeness_of_finite_le (T := T) ?_ h;
    exact hn;

theorem arithmetical_completeness_iff
  : A ∈ LogicGLPlusBoxBot T.height ↔ (∀ f : StandardRealization α T, T ⊢ f A) := by
  constructor;
  . intro h f; exact arithmetical_soundness h;
  . exact arithmetical_completeness (by simp);

lemma eq_provabilityLogic : LogicGLPlusBoxBot (α := α) T.height = T.provabilityLogic := by
  ext A;
  exact arithmetical_completeness_iff;

end

end LogicGLPlusBoxBot

end
