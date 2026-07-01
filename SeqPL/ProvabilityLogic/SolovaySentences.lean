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
open LO.Entailment
open LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

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
      apply right_Fdisj'!_intro;
      simpa using h;
    . intro h;
      apply CN!_of_CN!_right;
      apply left_Fdisj'!_intro;
      intro j hj;
      apply S.SC1;
      by_contra hC; subst hC;
      apply h;
      simpa using hj;
  | imp A B ihA ihB =>
    simp only [Formula.interpret];
    constructor;
    . intro h;
      rcases forces_imp.mp h with (hA | hB);
      . exact C!_trans ((ihA hri).2 hA) CNC!;
      . exact C!_trans ((ihB hri).1 hB) implyK!;
    . intro h;
      obtain ⟨hA, hB⟩ := not_forces_imp.mp h;
      exact not_imply_prem''! ((ihA hri).1 hA) ((ihB hri).2 hB);
  | box A ihA =>
    simp only [Formula.interpret];
    constructor;
    . intro h;
      apply C!_trans $ S.SC3 i hri;
      apply 𝔅.mono';
      apply left_Fdisj'!_intro;
      rintro j Rij;
      replace Rij : i ≺ j := by simpa using Rij;
      have hrj : ↑M.root ≠ j := by
        rintro rfl;
        exact Std.Irrefl.irrefl i $ IsTrans.trans i (↑M.root) i Rij (M.root.2 i (Ne.symm hri));
      exact (ihA hrj).1 (forces_box.mp h j Rij);
    . intro h;
      obtain ⟨j, Rij, hA⟩ := not_forces_box.mp h;
      have hrj : ↑M.root ≠ j := by
        rintro rfl;
        exact Std.Irrefl.irrefl i $ IsTrans.trans i (↑M.root) i Rij (M.root.2 i (Ne.symm hri));
      have : T₀ ⊢ 𝔅.dia (S.σ j) 🡒 ∼(𝔅 (S.realization A)) :=
        contra! $ 𝔅.mono' $ CN!_of_CN!_right $ (ihA hrj).2 hA;
      exact C!_trans (S.SC2 i j Rij) this;

theorem mainlemma (hri : M.root ≠ i) : i ⊩ A → T₀ ⊢ S.σ i 🡒 A.interpret S.realization := (mainlemma_aux hri).1
theorem mainlemma_neg (hri : M.root ≠ i) : i ⊮ A → T₀ ⊢ S.σ i 🡒 ∼(A.interpret S.realization) := (mainlemma_aux hri).2

lemma root_of_iterated_inconsistency : T₀ ⊢ (∼𝔅^[M.height] ⊥) 🡒 (S.σ M.root) := by
  suffices T₀ ⊢ (⩖ j, S.σ j) 🡒 ((∼(S.σ M.root)) 🡒 (𝔅^[M.height] ⊥)) by
    cl_prover [this, S.SC4];
  apply left_Udisj!_intro;
  intro i;
  by_cases hir : i = ↑M.root;
  . rcases hir;
    cl_prover;
  . have : T₀ ⊢ S.σ i 🡒 𝔅^[M.height] ⊥ := by
      simpa [Formula.interpret] using
        S.mainlemma (Ne.symm hir) (A := □^[M.height] ⊥)
          $ iff_rank_lt_forces_boxItr_bot.mp
          $ RootedModel.rank_lt_height
          $ M.root.2 i hir;
    cl_prover [this];

lemma theory_height (hSound : ∀ {σ}, T₀ ⊢ 𝔅 σ → T ⊢ σ) (h : M.root.1 ⊩ ◇(∼A)) (b : T ⊢ S.realization A) : 𝔅.height < M.height := by
  apply 𝔅.height_lt_pos_of_boxBot hSound (n := M.height) (pos_rank_of_forces_dia h);
  obtain ⟨i, hi, hiA⟩ : ∃ i : M.World, M.root.1 ≺ i ∧ i ⊮ A := by
    obtain ⟨i, hi, hiA⟩ := forces_dia.mp h;
    exact ⟨i, hi, forces_neg.mp hiA⟩;
  have hri : ↑M.root ≠ i := by
    rintro rfl;
    exact Std.Irrefl.irrefl _ hi;
  have b₀ : T₀ ⊢ 𝔅 (S.realization A) := 𝔅.D1 b;
  have b₁ : T₀ ⊢ (∼𝔅^[M.height] ⊥) 🡒 (S.σ M.root) := S.root_of_iterated_inconsistency;
  have b₂ : T₀ ⊢ S.σ M.root 🡒 𝔅.dia (S.σ i) := S.SC2 M.root i hi;
  have b₃ : T₀ ⊢ 𝔅.dia (S.σ i) 🡒 (∼(𝔅 (S.realization A))) := by
    simpa [Provability.dia] using! 𝔅.dia_mono <| WeakerThan.pbl <| S.mainlemma_neg hri hiA;
  cl_prover [b₀, b₁, b₂, b₃];

end LO.FirstOrder.ProvabilityAbstraction.Provability.SolovaySentences

end
