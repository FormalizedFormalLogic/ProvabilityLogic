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

section

open RootedModel.extendRoot

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [DecidableEq α]

/--
  **Reflexive main lemma** (cf. `SolovaySentences.rfl_mainlemma` in Foundation, used in
  the proofs of Lemma 49 and the arithmetical completeness of `S` in [AB05]):
  when the root of `M` forces all axiom T instances for boxed subformulas of `A`
  (i.e. the root is `A`-reflexive), the Solovay sentence of the *new* root of
  `M.extendRoot 1` decides the realizations of all subformulas of `A` according to
  their truth at the root of `M`.
-/
lemma rfl_mainlemma
    {S : T.standardProvability.SolovaySentences (M.extendRoot 1)}
    (ha : ∀ B, (□B) ∈ A.subfmls → M.root.1 ⊩ ((□B) 🡒 B)) :
    ∀ {B : _root_.Formula α}, B ∈ A.subfmls →
      (M.root.1 ⊩ B → 𝗜𝚺₁ ⊢ S.σ (M.extendRoot 1).root.1 🡒 (B.interpret S.realization)) ∧
      (M.root.1 ⊮ B → 𝗜𝚺₁ ⊢ S.σ (M.extendRoot 1).root.1 🡒 ∼(B.interpret S.realization)) := by
  intro B;
  induction B with
  | bot =>
    intro _;
    constructor;
    . intro h;
      exact absurd h (by simp);
    . intro _;
      simp only [Formula.interpret];
      cl_prover;
  | atom a =>
    intro _;
    constructor;
    . intro h;
      apply right_Fdisj'!_intro;
      grind [Model.World.Forces];
    . intro h;
      apply CN!_of_CN!_right;
      apply left_Fdisj'!_intro;
      intro j hj;
      apply S.SC1;
      rintro rfl;
      apply h;
      grind [Model.World.Forces];
  | imp B C ihB ihC =>
    intro hBC;
    replace ihB := ihB (by grind);
    replace ihC := ihC (by grind);
    simp only [Formula.interpret];
    constructor;
    . intro h;
      rcases Model.World.forces_imp.mp h with (hB | hC);
      . exact C!_trans (ihB.2 hB) CNC!;
      . exact C!_trans (ihC.1 hC) implyK!;
    . intro h;
      obtain ⟨hB, hC⟩ := Model.World.not_forces_imp.mp h;
      exact not_imply_prem''! (ihB.1 hB) (ihC.2 hC);
  | box B ihB =>
    intro hBox;
    replace ihB := ihB (by grind);
    simp only [Formula.interpret];
    constructor;
    . intro h;
      apply C!_of_conseq!;
      apply T.standardProvability.D1;
      apply Entailment.WeakerThan.pbl (𝓢 := 𝗜𝚺₁);
      have all : ∀ i : (M.extendRoot 1).World, 𝗜𝚺₁ ⊢ S.σ i 🡒 (B.interpret S.realization) := by
        rintro (x | i);
        . apply S.mainlemma (by simp [RootedModel.extendRoot, Fin.posLast]);
          apply RootedModel.extendRoot.same_forces_embed.mpr;
          by_cases hx : x = M.root.1;
          . subst hx;
            exact ha B hBox h;
          . exact h x (M.root.2 x hx);
        . rw [show (Sum.inr i : (M.extendRoot 1).World) = (M.extendRoot 1).root.1 by
            congr 1;
            apply Fin.ext;
            have := i.2;
            simp only [Fin.posLast, PNat.natPred, PNat.val_ofNat] at this ⊢;
            omega];
          exact ihB.1 (ha B hBox h);
      have := left_Udisj!_intro _ all;
      cl_prover [this, S.SC4];
    . intro h;
      obtain ⟨y, Rxy, hy⟩ := Model.World.not_forces_box.mp h;
      have hmn : 𝗜𝚺₁ ⊢ S.σ (Sum.inl y) 🡒 ∼(B.interpret S.realization) :=
        S.mainlemma_neg (by simp [RootedModel.extendRoot, Fin.posLast])
          (RootedModel.extendRoot.same_forces_embed.not.mpr hy);
      have b : 𝗜𝚺₁ ⊢ T.standardProvability.dia (S.σ (Sum.inl y)) 🡒
          ∼(T.standardProvability (B.interpret S.realization)) :=
        contra! $ T.standardProvability.mono' $ CN!_of_CN!_right hmn;
      exact C!_trans (S.SC2 _ _ (by simp [Model.Rel])) b;

end

end LO.FirstOrder.ProvabilityAbstraction.Provability.SolovaySentences

end
