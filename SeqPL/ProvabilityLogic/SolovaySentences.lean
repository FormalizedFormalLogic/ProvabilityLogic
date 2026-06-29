module

public import SeqPL.Kripke.Rank
public import Foundation.Vorspiel.List.ChainI
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height
public import SeqPL.Logic.GL.Basic
public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.ProvabilityLogic.Interpret

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
         {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] {𝔅 : Provability T₀ T} [𝔅.HBL]

variable {κ : Type*} [Nonempty κ]
         {α : Type*}
         {A B : _root_.Formula α}
         {M : RootedModel κ α}

structure LO.FirstOrder.ProvabilityAbstraction.Provability.SolovaySentences
  (𝔅 : Provability T₀ T) (M : RootedModel κ α) [Fintype M.World] where
  σ : M.World → FirstOrder.Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢ σ i 🡒 ∼σ j
  protected SC2 : ∀ i j, i ≺ j → T₀ ⊢ σ i 🡒 𝔅.dia (σ j)
  protected SC3 : ∀ i : M.World, M.root ≠ i → T₀ ⊢ σ i 🡒 𝔅 (⩖ j ∈ { j : M.World | i ≺ j }, σ j)
  protected SC4 : T₀ ⊢ ⩖ j, σ j

namespace LO.FirstOrder.ProvabilityAbstraction.Provability.SolovaySentences

attribute [coe] σ

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL] {i : M.World}
         {S : SolovaySentences 𝔅 M}

noncomputable def realization : Realization α 𝔅 := ⟨fun a ↦ ⩖ i ∈ { i : M.World | i ⊩ (.atom a) }, S.σ i⟩

private lemma mainlemma_aux (hri : M.root ≠ i)
  : (i ⊩ A → T₀ ⊢ S.σ i 🡒 S.realization A) ∧ (i ⊮ A → T₀ ⊢ S.σ i 🡒 ∼(S.realization A)) := by
  induction A generalizing i with
  | bot => simp [Formula.interpret];
  | atom a =>
    constructor;
    . intro h;
      sorry;
    . intro h;
      sorry;
  | imp A B ihA ihB =>
    sorry;
  | box A ihA =>
    sorry;

theorem mainlemma (hri : M.root ≠ i) : i ⊩ A → T₀ ⊢ S.σ i 🡒 A.interpret S.realization := (mainlemma_aux hri).1
theorem mainlemma_neg (hri : M.root ≠ i) : i ⊮ A → T₀ ⊢ S.σ i 🡒 ∼(A.interpret S.realization) := (mainlemma_aux hri).2

lemma root_of_iterated_inconsistency : T₀ ⊢ (∼𝔅^[M.height] ⊥) 🡒 (S.σ M.root) := by sorry;

lemma theory_height (hSound : ∀ {σ}, T₀ ⊢ 𝔅 σ → T ⊢ σ) (h : M.root.1 ⊩ ◇(∼A)) (b : T ⊢ S.realization A) : 𝔅.height < M.height := by
  sorry;

end LO.FirstOrder.ProvabilityAbstraction.Provability.SolovaySentences

def LO.FirstOrder.Theory.standardProvability.solovaySentences (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (M : RootedModel κ α) [Fintype M.World] : T.standardProvability.SolovaySentences M := by sorry


theorem unprovable_realization_exists
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
  (M : RootedModel κ α) [Fintype M.World] [M.IsGL]
  (hA : M.root.1 ⊮ A) (h : M.height < T.height)
  : ∃ f : StandardRealization α T, T ⊬ f A := by
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences (M := M.extendRoot 1) (T := T);
  use S.realization;
  contrapose! h;
  apply Order.le_of_lt_add_one;
  calc
    T.height < (M.extendRoot 1).height := S.theory_height (T.standardProvability.syntactical_sound ℕ) (A := A) ?_ h
    _        = _                       := by
      have := RootedModel.extendRoot.Ext1.eq_height_original_height_succ (M := M);
      simp_all only [ne_eq, PNat.val_ofNat, Nat.cast_add, Nat.cast_one];
  . apply Model.World.forces_dia.mpr;
    use M.root;
    constructor;
    . tauto;
    . exact RootedModel.extendRoot.same_forces_embed.not.mpr hA;


end
