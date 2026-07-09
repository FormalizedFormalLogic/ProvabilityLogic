module

public import SeqPL.ProvabilityLogic.SolovaySentences
public import SeqPL.Kripke.Graft
public import SeqPL.Logic.S.Basic
public import SeqPL.ToFoundation.FirstOrder.Arithmetic.Basic.Sigma1WitnessForm

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
          use embed X.r₁;
          refine ⟨?_, ?_, ?_⟩;
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


noncomputable section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

/-!
### Arithmetical construction of the modified Solovay sentences (§6 Theorem 2 of [Bek90])

Port of the construction in `SeqPL.ProvabilityLogic.SolovaySentences`
(`LO.FirstOrder.Arithmetic.Bootstrapping.SolovaySentences`), extended so that the limit
also jumps from the old root `b` to the reflexive point `r` as soon as a witness of a
fixed `𝚺₁` sentence `σ` is found. This realizes
`LO.FirstOrder.ProvabilityAbstraction.Provability.ModifiedSolovaySentences`.
-/

namespace ModifiedSolovaySentences

open LO LO.Entailment
open Model Model.World
open SolovaySentences (NegativeSuccessor negativeSuccessor WChain twoPointAux θChainAux θAux)

section model

variable (T : ArithmeticTheory) [T.Δ₁] {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/--
  The climb side wins (or ties) the witness race against `σ`: the negation of `φ` is
  provable no later than `ψ` (intended to be `σ`) is. Kept `𝚺₁` (unlike raw `∼σ`, which
  is `𝚷₁`) so that `modifiedTwoPointAux`/`modifiedθAux` below stay `𝚺₁` overall; the
  raw truth of `σ` is only additionally required, as a separate `𝚺₁` conjunct, for the
  jump itself (`jumpAux`), which is what SC6 needs.
-/
def ClimbBeatsSigma (φ ψ : V) : Prop := T.ProvabilityComparisonLE (neg ℒₒᵣ φ) ψ

/--
  `σ` (intended for `ψ`) strictly wins the witness race against the climb: `ψ`'s witness
  is provable strictly before the negation of `φ`'s.
-/
def SigmaBeatsClimb (φ ψ : V) : Prop := T.ProvabilityComparisonLT ψ (neg ℒₒᵣ φ)

section

def climbBeatsSigma : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ nφ, !(negGraph ℒₒᵣ) nφ φ ∧ !T.provabilityComparisonLE nφ ψ”

instance climbBeatsSigma_defined : 𝚺₁-Relation[V] ClimbBeatsSigma T via (climbBeatsSigma T) := .mk fun v ↦ by
  simp [climbBeatsSigma, ClimbBeatsSigma]

instance climbBeatsSigma_definable : 𝚺₁-Relation (ClimbBeatsSigma T : V → V → Prop) :=
  (climbBeatsSigma_defined T).to_definable

/-- instance for definability tactic-/
instance climbBeatsSigma_definable' : 𝚺-[0 + 1]-Relation (ClimbBeatsSigma T : V → V → Prop) :=
  (climbBeatsSigma_defined T).to_definable

def sigmaBeatsClimb : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ nφ, !(negGraph ℒₒᵣ) nφ φ ∧ !T.provabilityComparisonLT ψ nφ”

instance sigmaBeatsClimb_defined : 𝚺₁-Relation[V] SigmaBeatsClimb T via (sigmaBeatsClimb T) := .mk fun v ↦ by
  simp [sigmaBeatsClimb, SigmaBeatsClimb]

instance sigmaBeatsClimb_definable : 𝚺₁-Relation (SigmaBeatsClimb T : V → V → Prop) :=
  (sigmaBeatsClimb_defined T).to_definable

/-- instance for definability tactic-/
instance sigmaBeatsClimb_definable' : 𝚺-[0 + 1]-Relation (SigmaBeatsClimb T : V → V → Prop) :=
  (sigmaBeatsClimb_defined T).to_definable

end

/-- The climb side wins (or ties) the race against the witness of `θ`: some proof of the
negation of `φ` appears no later than any witness of `θ` does. -/
def ClimbBeatsWitness (θ : 𝚫₀.Semisentence 1) (φ : V) : Prop :=
  ∃ p, Proof T p (neg ℒₒᵣ φ) ∧ ∀ w < p, ¬(V ⊧/![w] θ.val)

/-- The witness side strictly wins the race against the climb: some witness of `θ` appears
strictly before any proof of the negation of `φ` does. -/
def WitnessBeatsClimb (θ : 𝚫₀.Semisentence 1) (φ : V) : Prop :=
  ∃ w, (V ⊧/![w] θ.val) ∧ ∀ p ≤ w, ¬Proof T p (neg ℒₒᵣ φ)

section

def climbBeatsWitness (θ : 𝚫₀.Semisentence 1) : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ nφ, !(negGraph ℒₒᵣ) nφ φ ∧ ∃ p, !(proof T).sigma p nφ ∧ ∀ w < p, ¬!θ.val w”

instance climbBeatsWitness_defined (θ : 𝚫₀.Semisentence 1) :
    𝚺₁-Predicate[V] (ClimbBeatsWitness T θ) via (climbBeatsWitness T θ) := .mk fun v ↦ by
  simp [climbBeatsWitness, ClimbBeatsWitness]

instance climbBeatsWitness_definable (θ : 𝚫₀.Semisentence 1) : 𝚺₁-Predicate (ClimbBeatsWitness T θ : V → Prop) :=
  (climbBeatsWitness_defined T θ).to_definable

/-- instance for definability tactic-/
instance climbBeatsWitness_definable' (θ : 𝚫₀.Semisentence 1) :
    𝚺-[0 + 1]-Predicate (ClimbBeatsWitness T θ : V → Prop) :=
  (climbBeatsWitness_defined T θ).to_definable

def witnessBeatsClimb (θ : 𝚫₀.Semisentence 1) : 𝚺₁.Semisentence 1 := .mkSigma
  “φ. ∃ nφ, !(negGraph ℒₒᵣ) nφ φ ∧ ∃ w, !θ.val w ∧ ∀ p <⁺ w, ¬!(proof T).pi p nφ”

instance witnessBeatsClimb_defined (θ : 𝚫₀.Semisentence 1) :
    𝚺₁-Predicate[V] (WitnessBeatsClimb T θ) via (witnessBeatsClimb T θ) := .mk fun v ↦ by
  simp [witnessBeatsClimb, WitnessBeatsClimb]

instance witnessBeatsClimb_definable (θ : 𝚫₀.Semisentence 1) : 𝚺₁-Predicate (WitnessBeatsClimb T θ : V → Prop) :=
  (witnessBeatsClimb_defined T θ).to_definable

/-- instance for definability tactic-/
instance witnessBeatsClimb_definable' (θ : 𝚫₀.Semisentence 1) :
    𝚺-[0 + 1]-Predicate (WitnessBeatsClimb T θ : V → Prop) :=
  (witnessBeatsClimb_defined T θ).to_definable

end

/-- The two race outcomes are mutually exclusive. -/
lemma ClimbBeatsWitness.not_witnessBeatsClimb {θ : 𝚫₀.Semisentence 1} {φ : V} :
    ClimbBeatsWitness T θ φ → ¬WitnessBeatsClimb T θ φ := by
  rintro ⟨p, hp, hpw⟩ ⟨w, hwθ, hwp⟩;
  rcases lt_or_ge w p with hlt | hge;
  · exact hpw w hlt hwθ;
  · exact hwp p hge hp;

/-- If `θ` has no witness at all, any provable refutation wins the race vacuously. -/
lemma ClimbBeatsWitness.of_no_witness {θ : 𝚫₀.Semisentence 1} {φ : V} (hw : ¬∃ w, V ⊧/![w] θ.val)
    (hp : Provable T (neg ℒₒᵣ φ)) : ClimbBeatsWitness T θ φ := by
  obtain ⟨p, hp⟩ := hp;
  exact ⟨p, hp, fun w _ hθw ↦ hw ⟨w, hθw⟩⟩;

/-- Totality: a provable refutation that the witness does not strictly beat wins the race. -/
lemma ClimbBeatsWitness.of_not_witnessBeatsClimb {θ : 𝚫₀.Semisentence 1} {φ : V}
    (hp : Provable T (neg ℒₒᵣ φ)) (h : ¬WitnessBeatsClimb T θ φ) : ClimbBeatsWitness T θ φ := by
  obtain ⟨d, hd⟩ := hp;
  obtain ⟨p, hp, hpmin⟩ : ∃ p, Proof T p (neg ℒₒᵣ φ) ∧ ∀ z < p, ¬Proof T z (neg ℒₒᵣ φ) :=
    InductionOnHierarchy.least_number_sigma 𝚺 1 (P := (Proof T · (neg ℒₒᵣ φ))) (by definability) hd;
  refine ⟨p, hp, fun w hw hθw ↦ ?_⟩;
  unfold WitnessBeatsClimb at h; push Not at h;
  obtain ⟨p', hp'w, hp'proof⟩ := h w hθw;
  exact hpmin p' (lt_of_le_of_lt hp'w hw) hp'proof;

/-- The climb-beats-witness race outcome transfers along an earlier-refuted formula. -/
lemma ClimbBeatsWitness.of_le {θ : 𝚫₀.Semisentence 1} {φ₁ φ₂ : V}
    (hle : T.ProvabilityComparisonLE (neg ℒₒᵣ φ₁) (neg ℒₒᵣ φ₂))
    (h : ClimbBeatsWitness T θ φ₂) : ClimbBeatsWitness T θ φ₁ := by
  obtain ⟨b, hb, hbmin⟩ := hle;
  obtain ⟨p₂, hp₂, hp₂w⟩ := h;
  have hble : b ≤ p₂ := by
    by_contra hc; push Not at hc; exact absurd hp₂ (hbmin p₂ hc);
  exact ⟨b, hb, fun w hw ↦ hp₂w w (lt_of_lt_of_le hw hble)⟩;

/-- If `θ` has a witness that does not strictly beat `φ`'s refutation in the race, that
refutation is provable. -/
lemma Provable.of_witness_of_not_witnessBeatsClimb {θ : 𝚫₀.Semisentence 1} {φ : V}
    (hw : ∃ w, V ⊧/![w] θ.val) (h : ¬WitnessBeatsClimb T θ φ) : Provable T (neg ℒₒᵣ φ) := by
  obtain ⟨w, hwθ⟩ := hw;
  unfold WitnessBeatsClimb at h; push Not at h;
  obtain ⟨p, hpw, hpProof⟩ := h w hwθ;
  exact ⟨p, hpProof⟩;

end model

section stx

variable (T : ArithmeticTheory) [T.Δ₁] (X : StrongReflexiveCountermodel κ A)
         (σ : FirstOrder.ArithmeticSentence) (hσ : Hierarchy 𝚺 1 σ) (θ : 𝚫₀.Semisentence 1)

/-- The ordinary-climb edge condition: every rival successor of `i` other than `r`
loses the witness race against `j`. -/
def climbAux (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i j : X.N.World) : ArithmeticSemisentence N :=
  ⩕ k ∈ { k : X.N.World | i ≺ k ∧ k ≠ X.rN }, (negativeSuccessor T)/[t j, t k]

/-- `σ`, embedded (with no bound variables used) at an arbitrary arity. This is `𝚺₁`
(unlike its negation), so it is safe to use directly inside `modifiedTwoPointAux`. -/
def sigmaEmb : ArithmeticSemisentence N := Rew.embSubsts ![] ▹ σ

lemma rew_climbAux (w : Fin N → FirstOrder.ArithmeticSemiterm Empty N') (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i j : X.N.World) :
    Rew.subst w ▹ climbAux T X t i j = climbAux T X (fun i ↦ Rew.subst w (t i)) i j := by
  simp [climbAux, Finset.map_conj', Function.comp_def, ←TransitiveRewriting.comp_app,
    Rew.subst_comp_subst, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

lemma rew_sigmaEmb (w : Fin N → FirstOrder.ArithmeticSemiterm Empty N') :
    Rew.subst w ▹ sigmaEmb (N := N) σ = sigmaEmb σ := by
  simp [sigmaEmb, ←TransitiveRewriting.comp_app, Rew.subst_comp_embSubsts, Matrix.empty_eq]

/--
  The jump edge condition (from `b` to `r`): `σ` holds outright (this is what makes
  SC6 provable, unlike requiring merely `Provable T σ`), and `σ`'s witness additionally
  strictly beats every rival climb-successor of `b` that does exist (needed to keep
  the exclusivity argument at a mixed climb/jump branch point working, exactly as in
  the ordinary climb-vs-climb case).
-/
def jumpAux (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) : ArithmeticSemisentence N :=
  sigmaEmb σ ⋏ ⩕ k ∈ { k : X.N.World | X.b ≺ k ∧ k ≠ X.rN }, (witnessBeatsClimb T θ)/[t k]

lemma rew_jumpAux (w : Fin N → FirstOrder.ArithmeticSemiterm Empty N') (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) :
    Rew.subst w ▹ jumpAux T X σ θ t = jumpAux T X σ θ (fun i ↦ Rew.subst w (t i)) := by
  simp [jumpAux, rew_sigmaEmb, Finset.map_conj', Function.comp_def, ←TransitiveRewriting.comp_app,
    Rew.subst_comp_subst, Matrix.constant_eq_singleton]

/--
  The single-step transition condition witnessing `j` as the successor of `i` in a
  chain: a jump into `r` (only possible from `b`), or an ordinary climb into some
  `j ≠ r`, additionally required to beat `σ` when climbing away from `b`.
-/
def modifiedTwoPointAux (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i j : X.N.World) : ArithmeticSemisentence N :=
  if j = X.rN then
    (if i = X.b then jumpAux T X σ θ t else ⊥)
  else
    (climbAux T X t i j) ⋏ (if i = X.b then (climbBeatsWitness T θ)/[t j] else ⊤)

lemma rew_modifiedTwoPointAux (w : Fin N → FirstOrder.ArithmeticSemiterm Empty N') (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i j : X.N.World) :
    Rew.subst w ▹ modifiedTwoPointAux T X σ θ t i j = modifiedTwoPointAux T X σ θ (fun i ↦ Rew.subst w (t i)) i j := by
  unfold modifiedTwoPointAux;
  split_ifs with h1 h2 h2 <;>
    simp [rew_climbAux, rew_jumpAux, Function.comp_def, ←TransitiveRewriting.comp_app,
      Rew.subst_comp_subst, Matrix.constant_eq_singleton]

private lemma sigmaEmb_sigma1 (hσ : Hierarchy 𝚺 1 σ) : Hierarchy 𝚺 1 (sigmaEmb (N := N) σ) := by
  unfold sigmaEmb; exact hσ.rew _

private lemma modifiedTwoPointAux_sigma1 (hσ : Hierarchy 𝚺 1 σ)
    (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i j : X.N.World) :
    Hierarchy 𝚺 1 (modifiedTwoPointAux T X σ θ t i j) := by
  unfold modifiedTwoPointAux;
  split_ifs <;> simp [climbAux, jumpAux, sigmaEmb_sigma1 σ hσ]

/-- The chain condition along a `WChain`-style list of worlds, folding
`modifiedTwoPointAux` along each consecutive pair. -/
def modifiedθChainAux (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) : List X.N.World → ArithmeticSemisentence N
  |          [] => ⊥
  |         [_] => ⊤
  | j :: i :: ε => (modifiedθChainAux t (i :: ε)) ⋏ (modifiedTwoPointAux T X σ θ t i j)

lemma rew_modifiedθChainAux (w : Fin N → FirstOrder.ArithmeticSemiterm Empty N') (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (ε : List X.N.World) :
    Rew.subst w ▹ modifiedθChainAux T X σ θ t ε = modifiedθChainAux T X σ θ (fun i ↦ Rew.subst w (t i)) ε := by
  match ε with
  |          [] => simp [modifiedθChainAux]
  |         [_] => simp [modifiedθChainAux]
  | j :: i :: ε => simp [modifiedθChainAux, rew_modifiedθChainAux w _ (i :: ε), rew_modifiedTwoPointAux]

private lemma modifiedθChainAux_sigma1 (hσ : Hierarchy 𝚺 1 σ)
    (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (ε : List X.N.World) :
    Hierarchy 𝚺 1 (modifiedθChainAux T X σ θ t ε) := by
  match ε with
  |          [] => simp [modifiedθChainAux]
  |         [_] => simp [modifiedθChainAux]
  | j :: i :: ε =>
    have h1 := modifiedθChainAux_sigma1 hσ t (i :: ε);
    have h2 := modifiedTwoPointAux_sigma1 T X σ θ hσ t i j;
    simp [modifiedθChainAux, h1, h2]

/-- The disjunction, over all chains from the root of `X.N` to `i`, of `modifiedθChainAux`. -/
def modifiedθAux (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i : X.N.World) : ArithmeticSemisentence N :=
  haveI := X.isFiniteGL;
  haveI : X.N.IsGL := (inferInstance : (X.extendRoot 1).IsGL);
  haveI := Fintype.ofFinite (WChain X.N X.N.root.1 i);
  ⩖ ε : WChain X.N X.N.root.1 i, modifiedθChainAux T X σ θ t ε

lemma rew_modifiedθAux (w : Fin N → FirstOrder.ArithmeticSemiterm Empty N') (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i : X.N.World) :
    Rew.subst w ▹ modifiedθAux T X σ θ t i = modifiedθAux T X σ θ (fun i ↦ Rew.subst w (t i)) i := by
  simp [Finset.map_udisj, modifiedθAux, rew_modifiedθChainAux]

lemma modifiedθAux_sigma1 (hσ : Hierarchy 𝚺 1 σ) (t : X.N.World → FirstOrder.ArithmeticSemiterm Empty N) (i : X.N.World) :
    Hierarchy 𝚺 1 (modifiedθAux T X σ θ t i) := by
  simp [modifiedθAux, modifiedθChainAux_sigma1 T X σ θ hσ]

/--
  The arithmetical fixed-point realizing the modified Solovay sentences of
  Theorem 2 in §6 of [Bek90]. Besides the usual box-disjunction ingredients, the
  fixed point at `b` also directly requires `σ` to stay unprovable: resting at `b`
  forever means the jump to `r` (which unconditionally requires `Provable σ`,
  regardless of whether `b` has any climb rival at all) never triggers.
-/
def _root_.LO.FirstOrder.Theory.modifiedSolovay (i : X.N.World) : ArithmeticSentence := exclusiveMultifixedpoint
  (fun j ↦
    let jj := (Fintype.equivFin X.N.World).symm j
    (modifiedθAux T X σ θ (fun i ↦ #(Fintype.equivFin X.N.World i)) jj) ⋏
      (⩕ k ∈ { k : X.N.World | jj ≺ k ∧ k ≠ X.rN }, T.consistentWith/[#(Fintype.equivFin X.N.World k)]) ⋏
      (if jj = X.b then ∼(sigmaEmb σ) else ⊤))
  (Fintype.equivFin X.N.World i)

@[simp] lemma modifiedSolovay_exclusive {i j : X.N.World} :
    T.modifiedSolovay X σ θ i = T.modifiedSolovay X σ θ j ↔ i = j := by
  simp [Theory.modifiedSolovay]

/-- The quoted counterpart of `modifiedTwoPointAux`. -/
def modifiedTwoPoint (i j : X.N.World) : ArithmeticSentence := modifiedTwoPointAux T X σ θ (fun i ↦ ⌜T.modifiedSolovay X σ θ i⌝) i j

/-- The quoted counterpart of `modifiedθChainAux`. -/
def modifiedθChain (ε : List X.N.World) : ArithmeticSentence := modifiedθChainAux T X σ θ (fun i ↦ ⌜T.modifiedSolovay X σ θ i⌝) ε

/-- The quoted counterpart of `modifiedθAux`, with each bound variable specialized to
the quoted code of the corresponding modified Solovay sentence. -/
def modifiedθ (i : X.N.World) : ArithmeticSentence := modifiedθAux T X σ θ (fun i ↦ ⌜T.modifiedSolovay X σ θ i⌝) i

/-- The diagonal fixed-point equation defining `T.modifiedSolovay`. -/
lemma modifiedSolovay_diag (i : X.N.World) :
    𝗜𝚺₁ ⊢ (T.modifiedSolovay X σ θ i) 🡘
      ((modifiedθ T X σ θ i) ⋏ (⩕ j ∈ { j : X.N.World | i ≺ j ∧ j ≠ X.rN }, T.consistentWith/[⌜T.modifiedSolovay X σ θ j⌝]) ⋏
        (if i = X.b then ∼(sigmaEmb σ) else ⊤)) := by
  have : 𝗜𝚺₁ ⊢ (T.modifiedSolovay X σ θ i) 🡘
      (Rew.subst fun j ↦ ⌜T.modifiedSolovay X σ θ ((Fintype.equivFin X.N.World).symm j)⌝) ▹
        ((modifiedθAux T X σ θ (fun i ↦ #(Fintype.equivFin X.N.World i)) i) ⋏
          (⩕ k ∈ { k : X.N.World | i ≺ k ∧ k ≠ X.rN }, T.consistentWith/[#(Fintype.equivFin X.N.World k)]) ⋏
          (if i = X.b then ∼(sigmaEmb σ) else ⊤)) := by
    simpa [Theory.modifiedSolovay, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
      exclusiveMultidiagonal (T := 𝗜𝚺₁) (i := Fintype.equivFin X.N.World i)
        (fun j ↦
          let jj := (Fintype.equivFin X.N.World).symm j
          (modifiedθAux T X σ θ (fun i ↦ #(Fintype.equivFin X.N.World i)) jj) ⋏
            (⩕ k ∈ { k : X.N.World | jj ≺ k ∧ k ≠ X.rN }, T.consistentWith/[#(Fintype.equivFin X.N.World k)]) ⋏
            (if jj = X.b then ∼(sigmaEmb σ) else ⊤))
  simpa [modifiedθ, Finset.map_conj', Function.comp_def, rew_modifiedθAux, rew_sigmaEmb, ←TransitiveRewriting.comp_app,
    Rew.subst_comp_subst, Matrix.comp_vecCons', Matrix.constant_eq_singleton, apply_ite] using! this

end stx

section model

variable (T : ArithmeticTheory) [T.Δ₁] (X : StrongReflexiveCountermodel κ A) (σ : FirstOrder.ArithmeticSentence)
         (θ : 𝚫₀.Semisentence 1)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/--
  The single-step transition relation between `i` and `j` mirroring `modifiedTwoPointAux`:
  an ordinary climb into `j ≠ r` (with the extra `σ`-beating condition when leaving `b`),
  or a jump from `b` into `r`.
-/
def ModifiedStep (i j : X.N.World) : Prop :=
  if j = X.rN then
    i = X.b ∧ (V ⊧/![] σ) ∧
      ∀ k, X.b ≺ k → k ≠ X.rN → WitnessBeatsClimb (V := V) T θ ⌜T.modifiedSolovay X σ θ k⌝
  else
    (∀ k, i ≺ k → k ≠ X.rN → NegativeSuccessor (V := V) T ⌜T.modifiedSolovay X σ θ j⌝ ⌜T.modifiedSolovay X σ θ k⌝) ∧
      (i = X.b → ClimbBeatsWitness (V := V) T θ ⌜T.modifiedSolovay X σ θ j⌝)

@[simp] lemma val_modifiedTwoPoint (i j : X.N.World) :
    V ⊧/![] (modifiedTwoPoint T X σ θ i j) ↔ ModifiedStep T X σ θ (V := V) i j := by
  unfold modifiedTwoPoint modifiedTwoPointAux ModifiedStep;
  split_ifs <;> simp [climbAux, jumpAux, sigmaEmb] <;> tauto

variable (V)

inductive ModifiedΘChain : List X.N.World → Prop where
  | singleton (i : X.N.World) : ModifiedΘChain [i]
  | cons {i j : X.N.World} {ε} :
      ModifiedStep T X σ θ (V := V) i j → ModifiedΘChain (i :: ε) → ModifiedΘChain (j :: i :: ε)

def ModifiedΘ (i : X.N.World) : Prop :=
  ∃ ε : List X.N.World, ε.ChainI (fun x y ↦ y ≺ x) i X.N.root.1 ∧ ModifiedΘChain T X σ θ V ε

def _root_.LO.FirstOrder.Theory.ModifiedSolovay (i : X.N.World) : Prop :=
  ModifiedΘ T X σ θ V i ∧
    (∀ j, i ≺ j → j ≠ X.rN → T.ConsistentWith (⌜T.modifiedSolovay X σ θ j⌝ : V)) ∧
    (i = X.b → ¬(V ⊧/![] σ))

variable {T X σ θ V}

attribute [simp] ModifiedΘChain.singleton

@[simp] lemma ModifiedΘChain.not_nil : ¬ModifiedΘChain T X σ θ V ([] : List X.N.World) := by
  rintro ⟨⟩

lemma ModifiedΘChain.cons_cons_iff {i j : X.N.World} {ε : List X.N.World} :
    ModifiedΘChain T X σ θ V (j :: i :: ε) ↔ ModifiedΘChain T X σ θ V (i :: ε) ∧ ModifiedStep T X σ θ (V := V) i j := by
  constructor
  · rintro ⟨⟩; simp_all
  · rintro ⟨ih, h⟩; exact .cons h ih

lemma ModifiedΘChain.doubleton_iff {i j : X.N.World} :
    ModifiedΘChain T X σ θ V [j, i] ↔ ModifiedStep T X σ θ (V := V) i j := by
  constructor
  · rintro ⟨⟩; simp_all
  · rintro h; exact .cons h (by simp)

lemma ModifiedΘChain.cons_cons_iff' {i j : X.N.World} {ε : List X.N.World} :
    ModifiedΘChain T X σ θ V (j :: i :: ε) ↔ ModifiedΘChain T X σ θ V [j, i] ∧ ModifiedΘChain T X σ θ V (i :: ε) := by
  constructor
  · rintro ⟨⟩; simp [ModifiedΘChain.doubleton_iff, *]
  · rintro ⟨ih, h⟩; exact h.cons (by rcases ih; assumption)

lemma ModifiedΘChain.cons_of {m i j : X.N.World} {ε : List X.N.World}
    (hc : List.ChainI (fun x y ↦ y ≺ x) i m ε)
    (hΘ : ModifiedΘChain T X σ θ V ε)
    (H : ModifiedStep T X σ θ (V := V) i j)
    (hij : i ≺ j) :
    ModifiedΘChain T X σ θ V (j :: ε) := by
  rcases hc
  case singleton => exact .cons H hΘ
  case cons => exact .cons H hΘ

lemma ModifiedΘChain.append_iff {ε₁ ε₂ : List X.N.World} {i : X.N.World} :
    ModifiedΘChain T X σ θ V (ε₁ ++ i :: ε₂) ↔
      ModifiedΘChain T X σ θ V (ε₁ ++ [i]) ∧ ModifiedΘChain T X σ θ V (i :: ε₂) := by
  match ε₁ with
  |           [] => simp
  |          [x] => simp [ModifiedΘChain.cons_cons_iff' (ε := ε₂)]
  | x :: y :: ε₁ =>
    have : ModifiedΘChain T X σ θ V (y :: (ε₁ ++ i :: ε₂)) ↔
        ModifiedΘChain T X σ θ V (y :: (ε₁ ++ [i])) ∧ ModifiedΘChain T X σ θ V (i :: ε₂) :=
      append_iff (ε₁ := y :: ε₁) (ε₂ := ε₂) (i := i)
    simp [cons_cons_iff' (ε := ε₁ ++ i :: ε₂), cons_cons_iff' (ε := ε₁ ++ [i]), and_assoc, this]

@[simp] lemma val_modifiedθChain (ε : List X.N.World) :
    V ⊧/![] (modifiedθChain T X σ θ ε) ↔ ModifiedΘChain T X σ θ V ε := by
  unfold modifiedθChain modifiedθChainAux
  match ε with
  |          [] => simp
  |         [i] => simp
  | j :: i :: ε =>
    suffices
      V ⊧/![] (modifiedθChain T X σ θ (i :: ε)) ∧ V ⊧/![] (modifiedTwoPoint T X σ θ i j) ↔
      ModifiedΘChain T X σ θ V (j :: i :: ε) by
      simpa [-val_modifiedTwoPoint] using! this
    simp [ModifiedΘChain.cons_cons_iff, val_modifiedθChain (i :: ε)]

@[simp] lemma val_modifiedθ {i : X.N.World} :
    V ⊧/![] (modifiedθ T X σ θ i) ↔ ModifiedΘ T X σ θ V i := by
  suffices
      (∃ ε, List.ChainI (fun x y ↦ y ≺ x) i X.N.root.1 ε ∧ V ⊧/![] (modifiedθChain T X σ θ ε)) ↔
      ModifiedΘ T X σ θ V i by
    simpa [-val_modifiedθChain, modifiedθ, modifiedθAux] using! this
  simp [ModifiedΘ]

@[simp] lemma val_modifiedSolovay {i : X.N.World} :
    V ⊧/![] (T.modifiedSolovay X σ θ i) ↔ T.ModifiedSolovay X σ θ V i := by
  unfold Theory.ModifiedSolovay;
  by_cases hb : i = X.b <;>
    simpa [models_iff, hb, sigmaEmb] using!
      consequence_iff.mp (Theory.Proof.sound (modifiedSolovay_diag T X σ θ i)) V inferInstance

/-- **Condition SC2.** -/
lemma Modified.consistent {i j : X.N.World} (hij : i ≺ j) (hjr : j ≠ X.rN) :
    T.ModifiedSolovay X σ θ V i → ¬Provable T (⌜∼T.modifiedSolovay X σ θ j⌝ : V) := fun h ↦
  (Theory.ConsistentWith.quote_iff T).mp (h.2.1 j hij hjr)

/-- Resting at `b` forever means `σ` never actually holds: the jump to `r`
(`ModifiedStep.models_sigma_of_jump`) would otherwise unconditionally trigger. -/
lemma Modified.not_models_sigma_of_rest_at_b :
    T.ModifiedSolovay X σ θ V X.b → ¬(V ⊧/![] σ) := fun h ↦ h.2.2 rfl

/-- A jump step unconditionally requires `σ` to hold, regardless of whether `b`
has any climb rival at all. -/
lemma ModifiedStep.models_sigma_of_jump {i : X.N.World} (h : ModifiedStep T X σ θ (V := V) i X.rN) :
    V ⊧/![] σ := by
  simp [ModifiedStep] at h; exact h.2.1

/--
  Totality of the witness race between a provable `φ` and any `ψ`: if `ψ`'s witness
  never comes strictly before `φ`'s, then `φ`'s witness comes no later than `ψ`'s.
  (A general fact about `ProvabilityComparisonLE`/`LT`, independent of the modified
  Solovay construction.)
-/
lemma ProvabilityComparison.le_of_not_lt {φ ψ : V} (hφ : Provable T (φ : V))
    (h : ¬T.ProvabilityComparisonLT (V := V) φ ψ) : T.ProvabilityComparisonLE (V := V) ψ φ := by
  obtain ⟨d, hd⟩ := hφ;
  obtain ⟨d, hd, hmin⟩ : ∃ d, Proof T d φ ∧ ∀ z < d, ¬Proof T z φ :=
    InductionOnHierarchy.least_number_sigma 𝚺 1 (P := (Proof T · φ)) (by definability) hd;
  simp only [Theory.ProvabilityComparisonLT, not_exists, not_and, not_forall] at h;
  obtain ⟨d', hd'd, hd'ψ⟩ := h d hd;
  rw [not_not] at hd'ψ;
  exact ⟨d', hd'ψ, fun z hz ↦ hmin z (lt_of_lt_of_le hz hd'd)⟩

private lemma Modified.exclusive.comparable {i₁ i₂ : X.N.World} {ε₁ ε₂ : List X.N.World}
    (ne : i₁ ≠ i₂)
    (h : ε₁ <:+ ε₂)
    (Hi₁ : ∀ j, i₁ ≺ j → j ≠ X.rN → T.ConsistentWith (⌜T.modifiedSolovay X σ θ j⌝ : V))
    (Hb₁ : i₁ = X.b → ¬(V ⊧/![] σ))
    (cε₁ : List.ChainI (fun x y ↦ y ≺ x) i₁ X.N.root.1 ε₁)
    (cε₂ : List.ChainI (fun x y ↦ y ≺ x) i₂ X.N.root.1 ε₂)
    (Θε₂ : ModifiedΘChain T X σ θ V ε₂) : False := by
  have : ∃ a, a :: ε₁ <:+ ε₂ := by
    rcases List.IsSuffix.eq_or_cons_suffix h with (e | h)
    · have : ε₁ ≠ ε₂ := by
        rintro rfl
        have : i₁ = i₂ := (List.ChainI.eq_of cε₁ cε₂).1
        contradiction
      contradiction
    · exact h
  rcases this with ⟨j, hj⟩
  have hji₁ε₂ : [j, i₁] <:+: ε₂ := by
    rcases cε₁.tail_exists with ⟨ε₁', rfl⟩
    exact List.infix_iff_prefix_suffix.mpr ⟨j :: i₁ :: ε₁', by simp, hj⟩
  have hij₁ : i₁ ≺ j := cε₂.rel_of_infix j i₁ hji₁ε₂
  have hstep : ModifiedStep T X σ θ (V := V) i₁ j := by
    have hΘ : ModifiedΘChain T X σ θ V [j, i₁] := by
      rcases hji₁ε₂ with ⟨η₁, η₂, rfl⟩
      have Θε₂ : ModifiedΘChain T X σ θ V (η₁ ++ j :: i₁ :: η₂) := by simpa using! Θε₂
      exact ModifiedΘChain.cons_cons_iff'.mp (ModifiedΘChain.append_iff.mp Θε₂).2 |>.1
    exact ModifiedΘChain.doubleton_iff.mp hΘ
  by_cases hjr : j = X.rN
  · -- Jump case: `i₁ = X.b` and `σ` provable, contradicting `Hb₁`.
    subst hjr
    simp only [ModifiedStep] at hstep
    exact Hb₁ hstep.1 hstep.2.1
  · -- Climb case: `j` beats itself as a rival of `i₁`, the standard self-comparison trick.
    have hne : ¬Provable T (⌜∼T.modifiedSolovay X σ θ j⌝ : V) := by
      simpa [Theory.ConsistentWith.quote_iff] using! Hi₁ j hij₁ hjr
    have hpr : Provable T (⌜∼T.modifiedSolovay X σ θ j⌝ : V) := by
      simp only [ModifiedStep, if_neg hjr] at hstep
      have hcomp : T.ProvabilityComparisonLE (V := V) ⌜∼T.modifiedSolovay X σ θ j⌝ ⌜∼T.modifiedSolovay X σ θ j⌝ := by
        simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using! hstep.1 j hij₁ hjr
      exact (ProvabilityComparison.iff_le_refl_provable (L := ℒₒᵣ)).mp hcomp
    contradiction

/-- **Condition SC1.** -/
lemma Modified.exclusive {i₁ i₂ : X.N.World} (ne : i₁ ≠ i₂) :
    T.ModifiedSolovay X σ θ V i₁ → ¬T.ModifiedSolovay X σ θ V i₂ := by
  intro S₁ S₂
  obtain ⟨⟨ε₁, cε₁, Θε₁⟩, Hi₁, Hb₁⟩ := S₁
  obtain ⟨⟨ε₂, cε₂, Θε₂⟩, Hi₂, Hb₂⟩ := S₂
  by_cases hε₁₂ : ε₁ <:+ ε₂
  · exact Modified.exclusive.comparable ne hε₁₂ Hi₁ Hb₁ cε₁ cε₂ Θε₂
  by_cases hε₂₁ : ε₂ <:+ ε₁
  · exact Modified.exclusive.comparable (Ne.symm ne) hε₂₁ Hi₂ Hb₂ cε₂ cε₁ Θε₁
  have : ∃ ε k j₁ j₂, j₁ ≠ j₂ ∧ j₁ :: k :: ε <:+ ε₁ ∧ j₂ :: k :: ε <:+ ε₂ := by
    rcases List.suffix_trichotomy hε₁₂ hε₂₁ with ⟨ε', j₁, j₂, nej, h₁, h₂⟩
    match ε' with
    |     [] =>
      rcases show j₁ = X.N.root.1 from List.single_suffix_uniq h₁ cε₁.prefix_suffix.2
      rcases show j₂ = X.N.root.1 from List.single_suffix_uniq h₂ cε₂.prefix_suffix.2
      contradiction
    | k :: ε =>
      exact ⟨ε, k, j₁, j₂, nej, h₁, h₂⟩
  obtain ⟨ε, k, j₁, j₂, nej, hj₁, hj₂⟩ := this
  have C₁ : ModifiedΘChain T X σ θ V [j₁, k] := by
    rcases hj₁ with ⟨_, rfl⟩
    have : ModifiedΘChain T X σ θ V ([j₁] ++ k :: ε) := (ModifiedΘChain.append_iff.mp Θε₁).2
    simpa using! (ModifiedΘChain.append_iff.mp this).1
  have C₂ : ModifiedΘChain T X σ θ V [j₂, k] := by
    rcases hj₂ with ⟨_, rfl⟩
    have : ModifiedΘChain T X σ θ V ([j₂] ++ k :: ε) := (ModifiedΘChain.append_iff.mp Θε₂).2
    simpa using! (ModifiedΘChain.append_iff.mp this).1
  have hstep₁ : ModifiedStep T X σ θ (V := V) k j₁ := ModifiedΘChain.doubleton_iff.mp C₁
  have hstep₂ : ModifiedStep T X σ θ (V := V) k j₂ := ModifiedΘChain.doubleton_iff.mp C₂
  have hkj₁ : k ≺ j₁ :=
    cε₁.rel_of_infix _ _ (List.infix_iff_prefix_suffix.mpr ⟨j₁ :: k :: ε, by simp, hj₁⟩)
  have hkj₂ : k ≺ j₂ :=
    cε₂.rel_of_infix _ _ (List.infix_iff_prefix_suffix.mpr ⟨j₂ :: k :: ε, by simp, hj₂⟩)
  by_cases h1 : j₁ = X.rN
  · by_cases h2 : j₂ = X.rN
    · exact nej (h1.trans h2.symm)
    · -- `j₁` is the jump target, `j₂` an ordinary climb rival of the same `k = b`.
      subst h1
      simp only [ModifiedStep] at hstep₁
      obtain ⟨hkb, hprov, hbeat⟩ := hstep₁
      subst hkb
      have hWBC : WitnessBeatsClimb (V := V) T θ ⌜T.modifiedSolovay X σ θ j₂⌝ := hbeat j₂ hkj₂ h2
      have hCBW : ClimbBeatsWitness (V := V) T θ ⌜T.modifiedSolovay X σ θ j₂⌝ := by
        simp only [ModifiedStep, if_neg h2] at hstep₂
        exact hstep₂.2 trivial
      exact ClimbBeatsWitness.not_witnessBeatsClimb (T := T) hCBW hWBC
  · by_cases h2 : j₂ = X.rN
    · -- Symmetric: `j₂` is the jump target, `j₁` an ordinary climb rival of `k = b`.
      subst h2
      simp only [ModifiedStep] at hstep₂
      obtain ⟨hkb, hprov, hbeat⟩ := hstep₂
      subst hkb
      have hWBC : WitnessBeatsClimb (V := V) T θ ⌜T.modifiedSolovay X σ θ j₁⌝ := hbeat j₁ hkj₁ h1
      have hCBW : ClimbBeatsWitness (V := V) T θ ⌜T.modifiedSolovay X σ θ j₁⌝ := by
        simp only [ModifiedStep, if_neg h1] at hstep₁
        exact hstep₁.2 trivial
      exact ClimbBeatsWitness.not_witnessBeatsClimb (T := T) hCBW hWBC
    · -- Both `j₁` and `j₂` are ordinary climb rivals: the standard antisymmetry argument.
      simp only [ModifiedStep, if_neg h1] at hstep₁
      simp only [ModifiedStep, if_neg h2] at hstep₂
      have P₁ : T.ProvabilityComparisonLE (V := V) ⌜∼T.modifiedSolovay X σ θ j₁⌝ ⌜∼T.modifiedSolovay X σ θ j₂⌝ := by
        simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using! hstep₁.1 j₂ hkj₂ h2
      have P₂ : T.ProvabilityComparisonLE (V := V) ⌜∼T.modifiedSolovay X σ θ j₂⌝ ⌜∼T.modifiedSolovay X σ θ j₁⌝ := by
        simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using! hstep₂.1 j₁ hkj₁ h1
      have : j₁ = j₂ := by simpa using! ProvabilityComparison.le_antisymm (V := V) P₁ P₂
      contradiction

/-- **Condition SC4**, first form: every reachable point either is itself stable, or
sees a stable point. -/
lemma ModifiedΘ.disjunction [𝗜𝚺₁ ⪯ T] (_hσ : Hierarchy 𝚺 1 σ)
    (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
    (i : X.N.World) : ModifiedΘ T X σ θ V i →
    T.ModifiedSolovay X σ θ V i ∨ ∃ j, i ≺ j ∧ T.ModifiedSolovay X σ θ V j := by
  haveI := X.isFiniteGL;
  haveI hN : X.N.IsGL := (inferInstance : (X.extendRoot 1).IsGL);
  haveI : IsTrans X.N.World X.N.Rel := hN.toIsTrans;
  have hcwf : IsConverseWellFounded X.N.World X.N.Rel := hN.toIsConverseWellFounded;
  apply WellFounded.induction hcwf.cwf i;
  intro i ih hΘ;
  by_cases hS : T.ModifiedSolovay X σ θ V i;
  · left; exact hS;
  · right;
    have hstep : ∃ j, i ≺ j ∧ ModifiedStep T X σ θ (V := V) i j := by
      by_cases hjump : i = X.b ∧ (V ⊧/![] σ) ∧
          ∀ k, X.b ≺ k → k ≠ X.rN → WitnessBeatsClimb (V := V) T θ ⌜T.modifiedSolovay X σ θ k⌝;
      · -- The jump condition holds outright: `b` jumps to `r`.
        obtain ⟨hib, hσV, hbeat⟩ := hjump;
        refine ⟨X.rN, hib ▸ StrongReflexiveCountermodel.b_rel_rN, ?_⟩;
        simp only [ModifiedStep];
        exact ⟨hib, hσV, hbeat⟩;
      · -- No outright jump: some climb rival `k₀ ≠ r` is refuted (possibly having
        -- won a race against `θ`'s witness at `b`), so we may climb to the overall winner.
        have hex : ∃ k₀ : X.N.World, i ≺ k₀ ∧ k₀ ≠ X.rN ∧
            Provable T (⌜∼T.modifiedSolovay X σ θ k₀⌝ : V) ∧
            (i = X.b → ClimbBeatsWitness (V := V) T θ ⌜T.modifiedSolovay X σ θ k₀⌝) := by
          by_cases hib : i = X.b;
          · by_cases hσV : V ⊧/![] σ;
            · obtain ⟨w₀, hw₀⟩ : ∃ w, V ⊧/![w] θ.val := hθσ.mp hσV;
              have hnwin : ¬∀ k, X.b ≺ k → k ≠ X.rN →
                  WitnessBeatsClimb (V := V) T θ ⌜T.modifiedSolovay X σ θ k⌝ :=
                fun h ↦ hjump ⟨hib, hσV, h⟩;
              push Not at hnwin;
              obtain ⟨k₀, hbk₀, hk₀r, hk₀nwin⟩ := hnwin;
              have hk₀prov : Provable T (⌜∼T.modifiedSolovay X σ θ k₀⌝ : V) := by
                have := Provable.of_witness_of_not_witnessBeatsClimb (T := T) (θ := θ) ⟨w₀, hw₀⟩ hk₀nwin;
                simpa [Sentence.quote_def, Semiformula.quote_def] using! this;
              refine ⟨k₀, hib ▸ hbk₀, hk₀r, hk₀prov, fun _ ↦ ?_⟩;
              exact ClimbBeatsWitness.of_not_witnessBeatsClimb (T := T)
                (by simpa [Sentence.quote_def, Semiformula.quote_def] using! hk₀prov) hk₀nwin;
            · have hnc : ¬(∀ j, i ≺ j → j ≠ X.rN → T.ConsistentWith (⌜T.modifiedSolovay X σ θ j⌝ : V)) :=
                fun h ↦ hS ⟨hΘ, h, fun _ ↦ hσV⟩;
              push Not at hnc;
              obtain ⟨k₀, hk₀, hk₀r, hk₀c⟩ := hnc;
              have hk₀prov : Provable T (⌜∼T.modifiedSolovay X σ θ k₀⌝ : V) := by
                simpa [Theory.ConsistentWith.quote_iff] using! hk₀c;
              refine ⟨k₀, hk₀, hk₀r, hk₀prov, fun _ ↦ ?_⟩;
              have hnw : ¬∃ w, V ⊧/![w] θ.val := fun ⟨w, hw⟩ ↦ hσV (hθσ.mpr ⟨w, hw⟩);
              exact ClimbBeatsWitness.of_no_witness (T := T) hnw
                (by simpa [Sentence.quote_def, Semiformula.quote_def] using! hk₀prov);
          · have hnc : ¬(∀ j, i ≺ j → j ≠ X.rN → T.ConsistentWith (⌜T.modifiedSolovay X σ θ j⌝ : V)) :=
              fun h ↦ hS ⟨hΘ, h, fun hc ↦ absurd hc hib⟩;
            push Not at hnc;
            obtain ⟨k₀, hk₀, hk₀r, hk₀c⟩ := hnc;
            exact ⟨k₀, hk₀, hk₀r, by simpa [Theory.ConsistentWith.quote_iff] using! hk₀c,
              fun hc ↦ absurd hc hib⟩;
        obtain ⟨k₀, hik₀, hk₀r, hk₀prov, hk₀cbs⟩ := hex;
        haveI hfin : Fintype X.N.World := inferInstance;
        haveI hfinite : Finite X.N.World := Fintype.finite hfin;
        haveI : Finite {k : X.N.World // i ≺ k ∧ k ≠ X.rN} := Subtype.finite;
        haveI := Fintype.ofFinite {k : X.N.World // i ≺ k ∧ k ≠ X.rN};
        obtain ⟨⟨j, hij, hjr⟩, hbest⟩ :=
          ProvabilityComparison.find_minimal_proof_fintype (T := T) (V := V)
            (ι := {k : X.N.World // i ≺ k ∧ k ≠ X.rN}) (i := ⟨k₀, hik₀, hk₀r⟩)
            (fun k ↦ ⌜∼T.modifiedSolovay X σ θ k.val⌝) (by simpa using hk₀prov);
        refine ⟨j, hij, ?_⟩;
        simp only [ModifiedStep, if_neg hjr];
        refine ⟨fun k hik hkr ↦ ?_, fun hib ↦ ?_⟩;
        · simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using! hbest ⟨k, hik, hkr⟩;
        · have hjk₀ : T.ProvabilityComparisonLE (V := V)
              ⌜∼T.modifiedSolovay X σ θ j⌝ ⌜∼T.modifiedSolovay X σ θ k₀⌝ := hbest ⟨k₀, hik₀, hk₀r⟩;
          have hle : T.ProvabilityComparisonLE (V := V)
              (neg ℒₒᵣ (⌜T.modifiedSolovay X σ θ j⌝ : V)) (neg ℒₒᵣ (⌜T.modifiedSolovay X σ θ k₀⌝ : V)) := by
            simpa [Sentence.quote_def, Semiformula.quote_def] using! hjk₀;
          exact ClimbBeatsWitness.of_le (T := T) hle (hk₀cbs hib);
    obtain ⟨j, hij, hstepij⟩ := hstep;
    have hΘj : ModifiedΘ T X σ θ V j := by
      obtain ⟨ε, hε, cε⟩ := hΘ;
      exact ⟨j :: ε, hε.cons hij, cε.cons_of hε hstepij hij⟩;
    rcases ih j hij hΘj with (hSj | ⟨k, hjk, hSk⟩);
    · exact ⟨j, hij, hSj⟩;
    · exact ⟨k, IsTrans.trans _ _ _ hij hjk, hSk⟩;

/--
  Any stable point other than the root and `r` is provably refuted by `T₀`: the
  standard self-comparison trick, using that `i` is its own climb rival.
-/
lemma Modified.refute {i : X.N.World} (ne : X.N.root.1 ≠ i) (ner : X.rN ≠ i) :
    T.ModifiedSolovay X σ θ V i → Provable T (⌜∼T.modifiedSolovay X σ θ i⌝ : V) := by
  intro h
  rcases show ModifiedΘ T X σ θ V i from h.1 with ⟨ε, hε, cε⟩
  rcases List.ChainI.prec_exists_of_ne hε (Ne.symm ne) with ⟨ε', i', hii', rfl, hε'⟩
  have hstep : ModifiedStep T X σ θ (V := V) i' i := (ModifiedΘChain.cons_cons_iff.mp cε).2
  simp only [ModifiedStep, if_neg (Ne.symm ner)] at hstep
  have : T.ProvabilityComparisonLE (V := V) ⌜∼T.modifiedSolovay X σ θ i⌝ ⌜∼T.modifiedSolovay X σ θ i⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using! hstep.1 i hii' (Ne.symm ner)
  exact (ProvabilityComparison.iff_le_refl_provable (T := T)).mp this

/-- **Condition SC4.** -/
lemma modified_disjunctive [𝗜𝚺₁ ⪯ T] (hσ : Hierarchy 𝚺 1 σ)
    (hθσ : V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) :
    ∃ i : X.N.World, T.ModifiedSolovay X σ θ V i := by
  rcases ModifiedΘ.disjunction (V := V) (T := T) hσ hθσ X.N.root.1 ⟨[X.N.root.1], by simp⟩ with (H | ⟨i, _, H⟩);
  · exact ⟨X.N.root.1, H⟩;
  · exact ⟨i, H⟩;

/-- **Condition SC3.** -/
lemma Modified.box_disjunction [𝗜𝚺₁ ⪯ T] (hσ : Hierarchy 𝚺 1 σ)
    (hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val)
    {i : X.N.World} (ne : X.N.root.1 ≠ i) (ner : X.rN ≠ i) :
    T.ModifiedSolovay X σ θ V i →
      Provable T (⌜⩖ j ∈ {j : X.N.World | i ≺ j}, T.modifiedSolovay X σ θ j⌝ : V) := by
  intro hS
  have TP : T.internalize V ⊢
      ⌜(modifiedθ T X σ θ i) 🡒
        ((T.modifiedSolovay X σ θ i) ⋎ (⩖ j ∈ {j : X.N.World | i ≺ j}, T.modifiedSolovay X σ θ j))⌝ :=
    internal_provable_of_outer_provable <| by
      have : 𝗜𝚺₁ ⊢ (modifiedθ T X σ θ i) 🡒
          ((T.modifiedSolovay X σ θ i) ⋎ (⩖ j ∈ {j : X.N.World | i ≺ j}, T.modifiedSolovay X σ θ j)) :=
        complete _ _ fun (V : Type) _ _ ↦ by
          simpa [models_iff] using! ModifiedΘ.disjunction hσ (hθσ V) i
      exact Entailment.WeakerThan.pbl this
  have Tθ : T.internalize V ⊢ ⌜modifiedθ T X σ θ i⌝ :=
    Bootstrapping.Arithmetic.sigma_one_provable_of_models T
      (modifiedθAux_sigma1 T X σ θ hσ _ i)
      (by simpa [models_iff] using! hS.1)
  have hP : T.internalize V ⊢
      (⌜T.modifiedSolovay X σ θ i⌝ ⋎ ⌜⩖ j ∈ {j : X.N.World | i ≺ j}, T.modifiedSolovay X σ θ j⌝ :
        Arithmetic.Bootstrapping.Formula V ℒₒᵣ) := (by simpa using! TP) ⨀ Tθ
  have hn : T.internalize V ⊢ (∼⌜T.modifiedSolovay X σ θ i⌝ : Arithmetic.Bootstrapping.Formula V ℒₒᵣ) := by
    simpa using! (tprovable_tquote_iff_provable_quote (T := T)).mpr (Modified.refute ne ner hS)
  have hd : T.internalize V ⊢ ⌜⩖ j ∈ {j : X.N.World | i ≺ j}, T.modifiedSolovay X σ θ j⌝ :=
    Entailment.of_a!_of_n! hP hn
  exact (tprovable_tquote_iff_provable_quote (T := T)).mp hd

/-- **Condition SC3r**: at `r`, the box-disjunction includes `r` itself, since the
limit provably stays at or above `r` once it has jumped there. -/
lemma Modified.box_disjunction_rN [𝗜𝚺₁ ⪯ T] (hσ : Hierarchy 𝚺 1 σ)
    (hθσ : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val) :
    T.ModifiedSolovay X σ θ V X.rN → Provable T
      (⌜(T.modifiedSolovay X σ θ X.rN) ⋎ (⩖ j ∈ {j : X.N.World | X.rN ≺ j}, T.modifiedSolovay X σ θ j)⌝ : V) := by
  intro hS
  have TP : T.internalize V ⊢
      ⌜(modifiedθ T X σ θ X.rN) 🡒
        ((T.modifiedSolovay X σ θ X.rN) ⋎ (⩖ j ∈ {j : X.N.World | X.rN ≺ j}, T.modifiedSolovay X σ θ j))⌝ :=
    internal_provable_of_outer_provable <| by
      have : 𝗜𝚺₁ ⊢ (modifiedθ T X σ θ X.rN) 🡒
          ((T.modifiedSolovay X σ θ X.rN) ⋎ (⩖ j ∈ {j : X.N.World | X.rN ≺ j}, T.modifiedSolovay X σ θ j)) :=
        complete _ _ fun (V : Type) _ _ ↦ by
          simpa [models_iff] using! ModifiedΘ.disjunction hσ (hθσ V) X.rN
      exact Entailment.WeakerThan.pbl this
  have Tθ : T.internalize V ⊢ ⌜modifiedθ T X σ θ X.rN⌝ :=
    Bootstrapping.Arithmetic.sigma_one_provable_of_models T
      (modifiedθAux_sigma1 T X σ θ hσ _ X.rN)
      (by simpa [models_iff] using! hS.1)
  have hP : T.internalize V ⊢
      (⌜T.modifiedSolovay X σ θ X.rN⌝ ⋎ ⌜⩖ j ∈ {j : X.N.World | X.rN ≺ j}, T.modifiedSolovay X σ θ j⌝ :
        Arithmetic.Bootstrapping.Formula V ℒₒᵣ) := (by simpa using! TP) ⨀ Tθ
  have hd : T.internalize V ⊢
      ⌜(T.modifiedSolovay X σ θ X.rN) ⋎ (⩖ j ∈ {j : X.N.World | X.rN ≺ j}, T.modifiedSolovay X σ θ j)⌝ := by
    simpa using! hP
  exact (tprovable_tquote_iff_provable_quote (T := T)).mp hd

/-- Resting at `X.rN` forever means `σ` holds: the step into `X.rN` that must have
occurred just before (necessarily a jump from `X.b`) unconditionally requires `σ`. -/
lemma Modified.models_sigma_of_rest_at_rN :
    T.ModifiedSolovay X σ θ V X.rN → V ⊧/![] σ := by
  intro h;
  rcases show ModifiedΘ T X σ θ V X.rN from h.1 with ⟨ε, hε, cε⟩;
  rcases List.ChainI.prec_exists_of_ne hε (Ne.symm StrongReflexiveCountermodel.rN_ne_root) with
    ⟨ε', i', hii', rfl, hε'⟩;
  have hstep : ModifiedStep T X σ θ (V := V) i' X.rN := (ModifiedΘChain.cons_cons_iff.mp cε).2;
  exact ModifiedStep.models_sigma_of_jump hstep

/-- **Condition SC6.** -/
lemma Modified.not_sigma_imp_not_rN [𝗜𝚺₁ ⪯ T] :
    𝗜𝚺₁ ⊢ ((∼σ : FirstOrder.ArithmeticSentence)) 🡒 ∼(T.modifiedSolovay X σ θ X.rN) :=
  complete _ _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using! (Modified.models_sigma_of_rest_at_rN (T := T) (X := X) (σ := σ) (θ := θ) (V := V)).mt

/-- **Condition SC5.** -/
lemma Modified.provable_sigma_imp_not_root [𝗜𝚺₁ ⪯ T] :
    𝗜𝚺₁ ⊢ (T.standardProvability σ) 🡒 ∼(T.modifiedSolovay X σ θ X.N.root.1) := by
  have hΛbσ : 𝗜𝚺₁ ⊢ (T.modifiedSolovay X σ θ X.b) 🡒 ∼σ :=
    complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! Modified.not_models_sigma_of_rest_at_b (T := T) (X := X) (σ := σ) (θ := θ) (V := V);
  have hσΛb : 𝗜𝚺₁ ⊢ σ 🡒 ∼(T.modifiedSolovay X σ θ X.b) := by cl_prover [hΛbσ];
  have hD1 : 𝗜𝚺₁ ⊢ T.standardProvability (σ 🡒 ∼(T.modifiedSolovay X σ θ X.b)) :=
    T.standardProvability.D1 (Entailment.WeakerThan.pbl hσΛb);
  have hboxImp : 𝗜𝚺₁ ⊢ (T.standardProvability σ) 🡒 (T.standardProvability (∼(T.modifiedSolovay X σ θ X.b))) :=
    T.standardProvability.D2 ⨀ hD1;
  refine complete _ _ fun (V : Type) _ _ ↦ ?_;
  have hcon :
      V ⊧/![] (T.standardProvability σ) → V ⊧/![] (T.standardProvability (∼(T.modifiedSolovay X σ θ X.b))) := by
    simpa [models_iff] using consequence_iff.mp (Theory.Proof.sound hboxImp) V inferInstance;
  suffices hsuff :
      Provable T (⌜σ⌝ : V) → ¬T.ModifiedSolovay X σ θ V X.N.root.1 by
    simpa [models_iff, standardProvability_def] using! hsuff;
  intro hp hroot;
  have hpb : Provable T (⌜∼(T.modifiedSolovay X σ θ X.b)⌝ : V) := by
    simpa [models_iff, standardProvability_def] using! hcon (by simpa [models_iff, standardProvability_def] using! hp);
  have hbrel : X.N.root.1 ≺ X.b :=
    X.N.root.2 X.b (Ne.symm StrongReflexiveCountermodel.b_ne_root);
  exact (Modified.consistent hbrel StrongReflexiveCountermodel.b_ne_rN hroot) hpb;

/--
  The modified Solovay construction of Theorem 2 in §6 of [Bek90], realized for a
  `𝚺₁` sentence `σ`: the witness formula `θ` is obtained from `exists_delta0_witness_form`
  applied to `σ` (viewed as a `𝚺₁`-formula with no free variables), and the resulting
  family of modified Solovay sentences `T.modifiedSolovay X σ θ` satisfies all the
  conditions `SC1`–`SC6` by the lemmas above.
-/
noncomputable def _root_.LO.FirstOrder.Theory.standardProvability.modifiedSolovaySentences
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (X : StrongReflexiveCountermodel κ A) {σ : FirstOrder.ArithmeticSentence}
    (hσ : Hierarchy 𝚺 1 σ) :
    T.standardProvability.ModifiedSolovaySentences X σ :=
  have hex := exists_delta0_witness_form (n := 0) (φ := σ) hσ;
  let θraw := hex.choose;
  have hθraw : Hierarchy 𝚺 0 θraw := hex.choose_spec.1;
  have hval := hex.choose_spec.2;
  let θ : 𝚫₀.Semisentence 1 :=
    HierarchySymbol.Semiformula.ofZero (HierarchySymbol.Semiformula.mkPolarity θraw 𝚺 hθraw) 𝚫₀;
  have hθval : θ.val = θraw := by
    show (HierarchySymbol.Semiformula.mkPolarity θraw 𝚺 hθraw).val = θraw;
    exact HierarchySymbol.Semiformula.val_mkPolarity θraw hθraw;
  have hθσ :
      ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
        V ⊧/![] σ ↔ ∃ w, V ⊧/![w] θ.val := fun V _ _ ↦ by
    rw [hθval]; exact hval V ![];
  { Λ := T.modifiedSolovay X σ θ
    SC1 := fun _ _ ne ↦ complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! Modified.exclusive (T := T) (X := X) (σ := σ) (θ := θ) ne
    SC2 := fun _ _ hij hjr ↦ complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using!
        Modified.consistent (T := T) (X := X) (σ := σ) (θ := θ) hij hjr
    SC3 := fun _ ne ner ↦ complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! Modified.box_disjunction hσ hθσ ne ner
    SC3r := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! Modified.box_disjunction_rN hσ hθσ
    SC4 := complete _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! modified_disjunctive hσ (hθσ V)
    SC5 := Modified.provable_sigma_imp_not_root
    SC6 := Modified.not_sigma_imp_not_rN }

end model

end ModifiedSolovaySentences

end LO.FirstOrder.Arithmetic.Bootstrapping

end


end
