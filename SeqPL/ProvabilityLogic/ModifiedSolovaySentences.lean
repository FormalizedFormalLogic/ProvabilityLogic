module

public import SeqPL.ProvabilityLogic.SolovaySentences
public import SeqPL.Kripke.GraftChain
public import SeqPL.Logic.S.Basic

/-!
# Modified Solovay sentences (Theorem 2 in §6 of [Bek90])

The abstract interface of the modified Solovay construction used in the proof of
Theorem 2 in §6 of [Bek90] (the arithmetical core of Lemma 51 in [AB05], "refugees
jump to a reflexive node").

Given a `StrongReflexiveCountermodel` `X` of a formula `A ∉ GLαω` and a sentence `σ`,
a family of sentences `Λ i` indexed by the worlds of `X.extendRoot 1` is a
`ModifiedSolovaySentences` when it satisfies the properties of Lemma 1 in §6 of
[Bek90] (stated over the base theory `T₀`):

- `SC1`, `SC4`: the usual exclusive/exhaustive Solovay conditions;
- `SC2`: `Λ i 🡒 ◇Λ j` for `i ≺ j`, but only for `j ≠ r` (the reflexive point `r`
  is reachable only by the special jump, never by a refutation proof);
- `SC3`: the usual box-disjunction condition, but only away from the root and `r`;
- `SC3r`: at `r`, the box-disjunction includes `r` itself (Lemma 1.4a in [Bek90],
  reflecting that the limit provably stays at or above `r` once it jumped there);
- `SC5`: `Pr(σ) 🡒 ∼Λ 0` — if `σ` is provable, the limit provably left the root
  (Lemma 1.5 in [Bek90]);
- `SC6`: `∼σ 🡒 ∼Λ r` — if `σ` is false, the limit never jumped to `r`
  (Lemma 1.6 in [Bek90]).

From these, Lemma 2 of [Bek90] (`mainlemma`), the depth-induction property
(Lemma 1.7, `provable_boxItr_bot`), the limit-location property (Lemma 1.8,
`provable_root_orig`) and the resulting reflection principle (`reflection`) are
derived. The arithmetical construction of such a family is the remaining input
(`exists_realization_sigma1_reflection_of_not_mem_LogicA` in
`SeqPL.ProvabilityLogic.Classification.A_D`).
-/

@[expose] public section

open Classical
open LO
open LO.Entailment
open LO.FirstOrder.ProvabilityAbstraction
open Model Model.World
open RootedModel.extendRoot
open RootedModel.extendRoot (embed)

universe u

variable {α : Type u}

namespace LO.FirstOrder.ProvabilityAbstraction.Provability

variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T]

/-- The `n`-times iterated consistency statement `∼(𝔅^[n]⊥)`. -/
def conItr (𝔅 : Provability T₀ T) (n : ℕ) : FirstOrder.Sentence L := ∼(𝔅^[n] ⊥)

end LO.FirstOrder.ProvabilityAbstraction.Provability

variable (κ : Type u) [Nonempty κ] [Finite κ] [DecidableEq α] (A : _root_.Formula α)

/-- A `Fintype` instance for `κ` derived classically from `Finite κ`, local to this file
and to this specific section variable `κ` (not a generic instance over all `Finite` types,
so it cannot conflict with unrelated structural `Fintype` instances elsewhere): `κ` is only
ever finite here, never canonically enumerated, so the enumeration itself never matters,
only its existence (needed for `Model.World.rank` and for the finite disjunctions `⩖` in
`ModifiedSolovaySentences` below). This whole development is already classical (`open
Classical` above) and noncomputable, so deriving `Fintype` via choice here loses nothing. -/
noncomputable local instance : Fintype κ := Fintype.ofFinite κ

/--
  A finite rooted GL countermodel of `A` with an `A`-reflexive point `r` above the root
  satisfying the two extra conditions of the corollary to Lemma 5 in §4 of [Bek90]:

  1. the rank of `r` is strictly greater than the rank of every world other than the
     root and `r` itself (Bek90's condition that the depth of `r` exceeds the depth of
     any other point covering the root), and
  2. `r` has a successor `r₁` forcing exactly the same subformulas of `A` (Bek90's
     unique covering condition),

  together with the structural condition that the root is the only predecessor of `r`
  (in [Bek90], `r` covers the root). This is the modal input of the modified Solovay
  construction of Theorem 2 in §6 of [Bek90].
-/
structure StrongReflexiveCountermodel extends RootedModel κ α where
  [isFiniteGL : toModel.IsFiniteGL]
  root_refutes : root.1 ⊮ A
  r : toModel.World
  root_rel_r : root.1 ≺ r
  r_reflexive : r ⊩ ⋀A.subfmlsS
  rel_r : ∀ z : toModel.World, z ≺ r → z = root.1
  rank_lt_rank_r : ∀ z : toModel.World, z ≠ root.1 → z ≠ r →
    Model.World.rank z < Model.World.rank r
  r₁ : toModel.World
  r_rel_r₁ : r ≺ r₁
  r₁_forces_iff : ∀ B ∈ A.subfmls, ((r₁ ⊩ B) ↔ (r ⊩ B))

attribute [instance] StrongReflexiveCountermodel.isFiniteGL

namespace StrongReflexiveCountermodel

variable {κ} {A} (X : StrongReflexiveCountermodel κ A)

/-- The extended model `𝒦⁰` of [Bek90] §6: the root is expanded to length 1. -/
abbrev N : RootedModel (κ ⊕ Fin 1) α := X.extendRoot 1

/-- The old root `b` of [Bek90] §6, viewed inside `X.N`. -/
abbrev b : X.N.World := embed X.root.1

/-- The reflexive point `r`, viewed inside `X.N`. -/
abbrev rN : X.N.World := embed X.r

variable {X}

lemma b_ne_root : X.N.root.1 ≠ X.b := by
  simp [embed, Fin.posLast];

lemma rN_ne_root : X.N.root.1 ≠ X.rN := by
  simp [embed, Fin.posLast];

lemma b_ne_rN : X.b ≠ X.rN := by
  intro hc;
  have : X.root.1 = X.r := by simpa [b, rN, embed] using hc;
  exact Std.Irrefl.irrefl _ (this ▸ X.root_rel_r);

lemma b_rel_rN : X.b ≺ X.rN := rel_embed_embed_iff_rel.mpr X.root_rel_r

/-- The only predecessors of `r` in `X.N` are the two roots. -/
lemma eq_root_or_b_of_rel_rN {z : X.N.World} (h : z ≺ X.rN) :
    z = X.N.root.1 ∨ z = X.b := by
  match z with
  | .inl y =>
    right;
    have : y ≺ X.r := by simpa [rN, embed, Model.Rel] using h;
    simp [b, embed, X.rel_r y this];
  | .inr i =>
    left;
    simp only [Fin.posLast];
    congr 1;
    omega;

/-- Worlds of `X.N` other than the root come from `X`. -/
lemma eq_embed_of_ne_root {z : X.N.World} (h : X.N.root.1 ≠ z) :
    ∃ z₀ : X.World, z = embed z₀ :=
  Ext1.eq_original_of_neq_extendRoot_root (fun hc => h (by rw [hc]))

end StrongReflexiveCountermodel


variable {κ} {A}

/--
  The interface of the modified Solovay construction (Lemma 1 in §6 of [Bek90]):
  sentences indexed by the worlds of `X.extendRoot 1` satisfying the exclusivity and
  provable-accessibility conditions of the construction whose limit jumps from the old
  root to `r` as soon as a witness of `σ` is found.
-/
structure LO.FirstOrder.ProvabilityAbstraction.Provability.ModifiedSolovaySentences
    {L : FirstOrder.Language} [L.ReferenceableBy L]
    {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T]
    (𝔅 : Provability T₀ T)
    (X : StrongReflexiveCountermodel κ A) (σ : FirstOrder.Sentence L) where
  Λ : X.N.World → FirstOrder.Sentence L
  protected SC1 : ∀ i j, i ≠ j → T₀ ⊢ Λ i 🡒 ∼Λ j
  protected SC2 : ∀ i j, i ≺ j → j ≠ X.rN → T₀ ⊢ Λ i 🡒 𝔅.dia (Λ j)
  protected SC3 : ∀ i : X.N.World, X.N.root.1 ≠ i → X.rN ≠ i →
    T₀ ⊢ Λ i 🡒 𝔅 (⩖ j ∈ { j : X.N.World | i ≺ j }, Λ j)
  protected SC3r : T₀ ⊢ Λ X.rN 🡒 𝔅 ((Λ X.rN) ⋎ (⩖ j ∈ { j : X.N.World | X.rN ≺ j }, Λ j))
  protected SC4 : T₀ ⊢ ⩖ j, Λ j
  protected SC5 : T₀ ⊢ 𝔅 σ 🡒 ∼(Λ X.N.root.1)
  protected SC6 : T₀ ⊢ ((∼σ : FirstOrder.Sentence L)) 🡒 ∼(Λ X.rN)

namespace LO.FirstOrder.ProvabilityAbstraction.Provability.ModifiedSolovaySentences

open StrongReflexiveCountermodel

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
         {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T] {𝔅 : Provability T₀ T} [𝔅.HBL]
         {X : StrongReflexiveCountermodel κ A} {σ : FirstOrder.Sentence L}
         {S : 𝔅.ModifiedSolovaySentences X σ}

/-- The Solovay realization: `f(p) := ⋁_{z ⊩ p} Λ z`. -/
noncomputable def realization (S : 𝔅.ModifiedSolovaySentences X σ) : Realization α 𝔅 :=
  ⟨fun a ↦ ⩖ i ∈ { i : X.N.World | i ⊩ (.atom a) }, S.Λ i⟩

/--
  **Lemma 2 in §6 of [Bek90]**: for every world `i` other than the root of the extended
  model and every subformula `B` of `A`, the sentence `Λ i` decides the realization of
  `B` according to the forcing at `i`. The box cases at `b` and `r` use the reflexivity
  of `r`, the twin `r₁` and the special conditions `SC2`/`SC3r`.
-/
private lemma mainlemma_aux {i : X.N.World} (hi : X.N.root.1 ≠ i) :
    ∀ {B : _root_.Formula α}, B ∈ A.subfmls →
      (i ⊩ B → T₀ ⊢ S.Λ i 🡒 (B.interpret S.realization)) ∧
      (i ⊮ B → T₀ ⊢ S.Λ i 🡒 ∼(B.interpret S.realization)) := by
  haveI := X.isFiniteGL;
  haveI hN : (X.extendRoot 1).IsFiniteGL := inferInstance;
  haveI : IsTrans X.N.World X.N.Rel := hN.toIsTrans;
  haveI : Std.Irrefl X.N.Rel := hN.toIrrefl;
  intro B;
  induction B generalizing i with
  | bot =>
    intro _;
    constructor;
    . intro h; exact absurd h (by simp);
    . intro _;
      simp only [Formula.interpret];
      cl_prover;
  | atom a =>
    intro _;
    constructor;
    . intro h;
      apply right_Fdisj'!_intro;
      simpa using h;
    . intro h;
      apply CN!_of_CN!_right;
      apply left_Fdisj'!_intro;
      intro j hj;
      apply S.SC1;
      rintro rfl;
      apply h;
      simpa using hj;
  | imp B C ihB ihC =>
    intro hBC;
    have hBm : B ∈ A.subfmls := Formula.subfmls_trans hBC Formula.mem_subfmls_imp_left;
    have hCm : C ∈ A.subfmls := Formula.subfmls_trans hBC Formula.mem_subfmls_imp_right;
    simp only [Formula.interpret];
    constructor;
    . intro h;
      rcases Model.World.forces_imp.mp h with (hB | hC);
      . exact C!_trans ((ihB hi hBm).2 hB) CNC!;
      . exact C!_trans ((ihC hi hCm).1 hC) implyK!;
    . intro h;
      obtain ⟨hB, hC⟩ := Model.World.not_forces_imp.mp h;
      exact not_imply_prem''! ((ihB hi hBm).1 hB) ((ihC hi hCm).2 hC);
  | box B ihB =>
    intro hBox;
    have hBm : B ∈ A.subfmls := Formula.subfmls_trans hBox Formula.mem_subfmls_box;
    simp only [Formula.interpret];
    have hne_root_of_rel : ∀ {x y : X.N.World}, x ≺ y → X.N.root.1 ≠ y := by
      intro x y Rxy hc;
      exact RootedModel.not_rel_root (hc ▸ Rxy);
    constructor;
    . intro h;
      by_cases hir : i = X.rN;
      . -- `i = r`: use `SC3r` and the reflexivity of `r`.
        subst hir;
        apply C!_trans S.SC3r;
        apply 𝔅.mono';
        have hrB : X.rN ⊩ B := by
          have h₁ : X.r ⊩ (□B) 🡒 B := Model.World.forces_fconj.mp X.r_reflexive _
            (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hBox));
          have h₂ : X.r ⊩ □B := same_forces_embed.mp h;
          exact same_forces_embed.mpr (h₁ h₂);
        apply left_A!_intro;
        . exact (ihB rN_ne_root hBm).1 hrB;
        . apply left_Fdisj'!_intro;
          rintro j Rij;
          replace Rij : X.rN ≺ j := by simpa using Rij;
          exact (ihB (hne_root_of_rel Rij) hBm).1 (Model.World.forces_box.mp h j Rij);
      . -- `i ≠ r`: use `SC3`; the successors of `i` may include `r`, but the inductive
        -- hypothesis applies there as well.
        apply C!_trans (S.SC3 i hi (Ne.symm hir));
        apply 𝔅.mono';
        apply left_Fdisj'!_intro;
        rintro j Rij;
        replace Rij : i ≺ j := by simpa using Rij;
        exact (ihB (hne_root_of_rel Rij) hBm).1 (Model.World.forces_box.mp h j Rij);
    . intro h;
      obtain ⟨j, Rij, hB⟩ := Model.World.not_forces_box.mp h;
      -- If the only refuting successor is `r` itself, replace it by the twin `r₁`.
      obtain ⟨j', Rij', hB', hj'r⟩ :
          ∃ j' : X.N.World, i ≺ j' ∧ j' ⊮ B ∧ j' ≠ X.rN := by
        by_cases hjr : j = X.rN;
        . subst hjr;
          refine ⟨embed X.r₁, ?_, ?_, ?_⟩;
          . -- `i ≺ r ≺ r₁`.
            exact IsTrans.trans _ _ _ Rij (rel_embed_embed_iff_rel.mpr X.r_rel_r₁);
          . intro hc;
            apply hB;
            apply same_forces_embed.mpr;
            apply (X.r₁_forces_iff B hBm).mp;
            exact same_forces_embed.mp hc;
          . intro hc;
            have : X.r₁ = X.r := by simpa [rN, embed] using hc;
            exact Std.Irrefl.irrefl _ (this ▸ X.r_rel_r₁);
        . exact ⟨j, Rij, hB, hjr⟩;
      have : T₀ ⊢ 𝔅.dia (S.Λ j') 🡒 ∼(𝔅 (B.interpret S.realization)) :=
        contra! $ 𝔅.mono' $ CN!_of_CN!_right $ (ihB (hne_root_of_rel Rij') hBm).2 hB';
      exact C!_trans (S.SC2 i j' Rij' hj'r) this;

theorem mainlemma {i : X.N.World} (hi : X.N.root.1 ≠ i) {B : _root_.Formula α}
    (hB : B ∈ A.subfmls) : i ⊩ B → T₀ ⊢ S.Λ i 🡒 (B.interpret S.realization) :=
  (mainlemma_aux hi hB).1

theorem mainlemma_neg {i : X.N.World} (hi : X.N.root.1 ≠ i) {B : _root_.Formula α}
    (hB : B ∈ A.subfmls) : i ⊮ B → T₀ ⊢ S.Λ i 🡒 ∼(B.interpret S.realization) :=
  (mainlemma_aux hi hB).2


section

omit [T₀ ⪯ T] in
/-- Provable monotonicity step of iterated inconsistency: `𝔅^[n]⊥ 🡒 𝔅^[n+1]⊥` over `T₀`. -/
private lemma provable_boxItr_bot_succ {n : ℕ} : T₀ ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[n + 1] ⊥ := by
  match n with
  | 0 =>
    simp only [Function.iterate_zero_apply];
    cl_prover;
  | n + 1 =>
    have : T₀ ⊢ 𝔅 (𝔅^[n] ⊥) 🡒 𝔅 (𝔅 (𝔅^[n] ⊥)) := 𝔅.D3;
    simpa only [Function.iterate_succ_apply'] using this;

omit [T₀ ⪯ T] in
/-- Provable monotonicity of iterated inconsistency over `T₀`. -/
private lemma provable_boxItr_bot_mono {n m : ℕ} (h : n ≤ m) : T₀ ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥ := by
  induction m with
  | zero =>
    obtain rfl : n = 0 := by omega;
    cl_prover;
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl;
    . exact C!_trans (ih (by omega)) provable_boxItr_bot_succ;
    . cl_prover;

/--
  **Lemma 1.7 in §6 of [Bek90]**: for every world `z` of `X.M` other than the old root
  and `r`, the sentence `Λ (embed z)` implies the `rank z + 1`-times iterated
  inconsistency of `T`, provably in `T₀`. By induction along the converse well-founded
  relation, using `SC3` (such a `z` is never the root of `X.N` nor `r`, and its
  successors are again such worlds).
-/
lemma provable_boxItr_bot_of_ne (S : 𝔅.ModifiedSolovaySentences X σ) :
    ∀ z : X.World, z ≠ X.root.1 → z ≠ X.r →
      T₀ ⊢ S.Λ (embed z) 🡒 𝔅^[Model.World.rank z + 1] ⊥ := by
  haveI := X.isFiniteGL;
  haveI hGL : X.IsGL := inferInstance;
  haveI : IsConverseWellFounded X.World X.Rel := hGL.toIsConverseWellFounded;
  intro z;
  apply WellFounded.induction this.cwf z;
  intro z ih hzb hzr;
  have h₁ : T₀ ⊢ S.Λ (embed z) 🡒 𝔅 (⩖ j ∈ { j : X.N.World | embed z ≺ j }, S.Λ j) := by
    apply S.SC3;
    . simp [embed, Fin.posLast];
    . intro hc;
      apply hzr;
      have : X.r = z := by simpa [rN, embed] using hc;
      exact this.symm;
  have h₂ : T₀ ⊢ (⩖ j ∈ { j : X.N.World | embed z ≺ j }, S.Λ j)
      🡒 𝔅^[Model.World.rank z] ⊥ := by
    apply left_Fdisj'!_intro;
    intro j hj;
    replace hj : embed z ≺ j := by simpa using hj;
    obtain ⟨y, rfl⟩ := exists_original_of_embed_rel hj;
    replace hj : z ≺ y := rel_embed_embed_iff_rel.mp hj;
    have hyb : y ≠ X.root.1 := fun hc => RootedModel.not_rel_root (hc ▸ hj);
    have hyr : y ≠ X.r := fun hc => hzb (X.rel_r z (hc ▸ hj));
    exact C!_trans (ih y hj hyb hyr)
      (provable_boxItr_bot_mono (by have := Model.rank_lt_of_rel hj; omega));
  simpa only [Function.iterate_succ_apply'] using C!_trans h₁ (𝔅.mono' h₂);

/--
  **Lemma 1.8 in §6 of [Bek90]**: provably in `T₀`, if `T` is `rank r`-times
  consistent while `σ` is provable but false, then the Solovay limit sits at the old
  root `b`. Combines `SC4` with `SC5` (excluding the new root), `SC6` (excluding `r`)
  and Lemma 1.7 (excluding every other world except `b`).
-/
lemma provable_b (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr (Model.World.rank X.r) 🡒 (𝔅 σ) 🡒
      ((∼σ : FirstOrder.Sentence L)) 🡒 S.Λ (embed X.root.1) := by
  haveI := X.isFiniteGL;
  have hall : ∀ j : X.N.World,
      T₀ ⊢ S.Λ j 🡒 (((∼(𝔅^[Model.World.rank X.r] ⊥)) : FirstOrder.Sentence L) 🡒 (𝔅 σ) 🡒
        ((∼σ : FirstOrder.Sentence L)) 🡒 S.Λ (embed X.root.1)) := by
    intro j;
    rcases Ext1.eq_original_or_eq_root j with ⟨z, rfl⟩ | rfl;
    . by_cases hzb : z = X.root.1;
      . subst hzb;
        cl_prover;
      . by_cases hzr : z = X.r;
        . subst hzr;
          have h₆ : T₀ ⊢ ((∼σ : FirstOrder.Sentence L)) 🡒 ∼(S.Λ (embed X.r)) := S.SC6;
          cl_prover [h₆];
        . have h₇ : T₀ ⊢ S.Λ (embed z) 🡒 𝔅^[Model.World.rank X.r] ⊥ :=
            C!_trans (S.provable_boxItr_bot_of_ne z hzb hzr)
              (provable_boxItr_bot_mono (X.rank_lt_rank_r z hzb hzr));
          cl_prover [h₇];
    . have h₅ : T₀ ⊢ (𝔅 σ) 🡒 ∼(S.Λ X.N.root.1) := S.SC5;
      cl_prover [h₅];
  have hdisj : T₀ ⊢ (⩖ j, S.Λ j) 🡒
      (((∼(𝔅^[Model.World.rank X.r] ⊥)) : FirstOrder.Sentence L) 🡒
      (𝔅 σ) 🡒 ((∼σ : FirstOrder.Sentence L)) 🡒 S.Λ (embed X.root.1)) := by
    apply left_Udisj!_intro;
    intro j;
    exact hall j;
  exact hdisj ⨀ S.SC4;

/--
  **Theorem 2 in §6 of [Bek90]**, given the modified Solovay sentences: provably in
  `T₀`, iterated consistency of `T` together with the Solovay realization of `A`
  implies the reflection instance `𝔅 σ 🡒 σ`. Combines Lemma 1.8 with Lemma 2 at the
  old root (which refutes `A`).
-/
theorem reflection (S : 𝔅.ModifiedSolovaySentences X σ) :
    T₀ ⊢ 𝔅.conItr (Model.World.rank X.r) 🡒
      (A.interpret S.realization) 🡒 ((𝔅 σ) 🡒 σ) := by
  haveI := X.isFiniteGL;
  have h₁ := S.provable_b;
  have h₂ : T₀ ⊢ S.Λ (embed X.root.1) 🡒 ∼(A.interpret S.realization) :=
    S.mainlemma_neg b_ne_root Formula.mem_subfmls_self
      ((same_forces_embed (x := X.root.1)).not.mpr X.root_refutes);
  cl_prover [h₁, h₂];

end

end LO.FirstOrder.ProvabilityAbstraction.Provability.ModifiedSolovaySentences

end
