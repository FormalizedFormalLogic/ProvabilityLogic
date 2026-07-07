module

public import SeqPL.Kripke.Preservation
public import SeqPL.Kripke.Cone
public import SeqPL.Kripke.GraftChain
public import SeqPL.Kripke.Rank

/-!
# `P`-simplification of GL-models (Bek90 §4, item 3 + Lemmas 6, 8)

This file formalizes "removal of a redundant cone" from [Bek90] §4 and the
`P`-simplification lemmas (Lemma 6 for finite GL-models, Lemma 8 for ω-models).

**A note on scope.** The classical "GL-model" of [Bek90]/[12] (going back to
Segerberg/Boolos) is a finite irreflexive TREE frame, not an arbitrary finite transitive
converse-well-founded frame. SeqPL's `Model.IsFiniteGL` class does not encode tree-ness
(no requirement that ancestors of a point be linearly ordered), so we make this a
standing explicit hypothesis (`RootedModel.IsTree`) on the lemmas below, matching the
paper's implicit convention. Without it, a point could be reached from outside its
"cone" through more than one branch, and the local cone-removal argument does not go
through as stated. Also, "cone `𝒳_a`, `𝒳_y` are `p̄`-isomorphic" from the paper is
formalized here via `Model.BisimulationUnder` (bisimilarity restricted to atoms in `P`)
rather than a literal frame isomorphism -- the modally correct and sufficient notion,
see `SeqPL/Kripke/Preservation.lean`.
-/

@[expose]
public section

universe u

variable [Nonempty κ] {α : Type u} [DecidableEq α]

namespace RootedModel

/--
  `M` has the tree property if the `≺`-ancestors of any point are linearly ordered:
  whenever `x ≺ z` and `y ≺ z`, `x` and `y` are comparable. This is the standing
  assumption on "GL-models" in the classification literature ([Bek90], [12]).
-/
class IsTree (M : RootedModel κ α) : Prop where
  tree : ∀ x y z : M.World, x ≺ z → y ≺ z → x = y ∨ x ≺ y ∨ y ≺ x

/--
  A *finite GL tree* model: a finite GL-model whose frame is a tree. This is the
  model class of the classical "GL-models" in the classification literature
  ([Bek90], [12]): finite irreflexive transitive trees.
-/
class IsFiniteGLTree (M : RootedModel κ α) : Prop extends Model.IsFiniteGL M.toModel, IsTree M

instance {M : RootedModel κ α} [M.IsFiniteGL] [M.IsTree] : M.IsFiniteGLTree where

variable {M : RootedModel κ α} {P : Finset α}

open Model (BisimulationUnder World.forces_iff_of_pbisimilar)
open Model.World (IsInConeOf IsProperPredecessorOf)

/--
  A point `a` is `P`-redundant (Bek90 §4, item 3, "Removal of a redundant cone") if it
  is not the minimum point, and every ancestor `x ≺ a` has an alternative successor
  `y` -- incomparable with `a` (so that its cone is disjoint from `a`'s) -- whose cone
  is `P`-bisimilar to the cone above `a`.
-/
structure Redundant (M : RootedModel κ α) (P : Finset α) (a : M.World) : Prop where
  ne_root : a ≠ M.root.1
  exists_alt : ∀ x : M.World, x ≺ a →
    ∃ (y : M.World) (Bi : BisimulationUnder P M.toModel M.toModel),
      x ≺ y ∧ ¬ y ≺ a ∧ ¬ a ≺ y ∧ y ≠ a ∧ Bi y a

/-- `M` is simple-under-`P` if it has no `P`-redundant point. -/
def IsSimpleUnder (M : RootedModel κ α) (P : Finset α) : Prop := ∀ a : M.World, ¬ Redundant M P a

section RemoveCone

variable [M.IsGL]

omit [DecidableEq α] in
lemma not_isInConeOf_root_of_ne {a : M.World} (ha : a ≠ M.root.1) :
  ¬ M.root.1.IsInConeOf a := by
  rintro (h | h);
  . exact ha h.symm;
  . exact Std.Irrefl.irrefl M.root.1 (IsTrans.trans _ _ _ (M.root.2 a ha) h);

/-- The carrier of `removeCone`. -/
abbrev removeCone.World (M : RootedModel κ α) (a : M.NonRoot) : Type _ :=
  {x : M.World // ¬ x.IsInConeOf a.1}

omit [DecidableEq α] in
instance removeCone.instNonempty (a : M.NonRoot) : Nonempty (removeCone.World M a) :=
  ⟨⟨M.root.1, not_isInConeOf_root_of_ne a.2⟩⟩

/-- Removal of the cone above `a` (Bek90 §4, item 3): the sub-model on the points that
are not successors of `a`. -/
def removeCone (M : RootedModel κ α) [M.IsGL] (a : M.NonRoot) :
  RootedModel (removeCone.World M a) α where
  Rel' x y := M.Rel x.1 y.1
  Val' x q := M.Val x.1 q
  root := ⟨⟨M.root.1, not_isInConeOf_root_of_ne a.2⟩, by
    rintro ⟨x, hx⟩ hne;
    show M.Rel M.root.1 x;
    exact M.root.2 x (by rintro rfl; exact hne rfl)⟩

namespace removeCone

instance (a : M.NonRoot) : IsTrans _ (M.removeCone a).Rel :=
  ⟨fun x y z => IsTrans.trans x.1 y.1 z.1⟩
instance (a : M.NonRoot) : Std.Irrefl (M.removeCone a).Rel :=
  ⟨fun x => Std.Irrefl.irrefl x.1⟩

omit [DecidableEq α] in
lemma isTree {a : M.NonRoot} [hTree : M.IsTree] :
  (M.removeCone a).IsTree := by
  refine ⟨fun x y z hxz hyz => ?_⟩;
  rcases hTree.tree x.1 y.1 z.1 hxz hyz with h | h | h;
  . exact Or.inl (Subtype.ext h);
  . exact Or.inr (Or.inl h);
  . exact Or.inr (Or.inr h);

section Finite

set_option linter.overlappingInstances false

variable [M.IsFiniteGL]

instance (a : M.NonRoot) : Finite (M.removeCone a).World :=
  Subtype.finite

instance (a : M.NonRoot) : (M.removeCone a).IsFiniteGL where

omit [DecidableEq α] [M.IsFiniteGL] in
lemma card_lt (a : M.NonRoot) [Fintype M.World] [Fintype (M.removeCone a).World] :
  Fintype.card (M.removeCone a).World < Fintype.card M.World :=
  Fintype.card_subtype_lt (p := fun x : M.World => ¬ x.IsInConeOf a.1) (x := a.1)
    (not_not_intro (Or.inl rfl))

end Finite

/--
  **Forcing preservation under removal of a redundant cone** (core of the proof of
  Lemma 6 in [Bek90] §4): if `M` is a tree and `a` is `P`-redundant, then for every
  point `x` outside `a`'s cone and every formula `C` depending on `P`, forcing of `C`
  at `x` in `M.removeCone a` agrees with forcing of `C` at `x` in `M`.
-/
theorem forces_iff {a : M.NonRoot} [hTree : M.IsTree] (hred : Redundant M P a.1) :
  ∀ {C : Formula α}, C.atoms ⊆ P →
  ∀ x : (M.removeCone a).World,
  x ⊩ C ↔ x.1 ⊩ C := by
  intro C;
  induction C with
  | atom => tauto;
  | bot => grind;
  | imp => grind;
  | box B ihB =>
    intro hC ⟨x, hx⟩;
    replace hC : B.atoms ⊆ P := by simpa [Formula.atoms] using hC;
    constructor;
    . intro h z hxz;
      by_cases hzS : z.IsInConeOf a.1;
      . -- `z` was removed: transport the box-witness through the redundancy of `a`.
        have hxa : x ≺ a.1 := by
          rcases hzS with rfl | haz;
          . exact hxz;
          . rcases hTree.tree x a.1 z hxz haz with (rfl | hxa | hax);
            . exact absurd (Or.inl rfl) hx;
            . exact hxa;
            . exact absurd (Or.inr hax) hx;
        obtain ⟨y, Bi, hxy, hyna, hnay, hyne, hBiya⟩ := hred.exists_alt x hxa;
        have hynS : ¬ y.IsInConeOf a.1 := by rintro (rfl | h); exacts [hyne rfl, hnay h];
        have hyB : y ⊩ B := (ihB hC ⟨y, hynS⟩).mp (h ⟨y, hynS⟩ hxy);
        have haB : a.1 ⊩ B := (World.forces_iff_of_pbisimilar Bi hBiya hC).mp hyB;
        rcases hzS with rfl | haz;
        . exact haB;
        . obtain ⟨z', hBiz'z, hyz'⟩ := Bi.back hBiya haz;
          have hxz' : x ≺ z' := IsTrans.trans _ _ _ hxy hyz';
          have hz'nS : ¬ z'.IsInConeOf a.1 := by
            rintro (rfl | haz');
            . exact hyna hyz';
            . rcases hTree.tree y a.1 z' hyz' haz' with (hya | hya | hya);
              . exact hyne hya;
              . exact hyna hya;
              . exact hnay hya;
          have hz'B : z' ⊩ B := (ihB hC ⟨z', hz'nS⟩).mp (h ⟨z', hz'nS⟩ hxz');
          exact (World.forces_iff_of_pbisimilar Bi hBiz'z hC).mp hz'B;
      . exact (ihB hC ⟨z, hzS⟩).mp (h ⟨z, hzS⟩ hxz);
    . intro h ⟨z, hz⟩ hxz;
      exact (ihB hC ⟨z, hz⟩).mpr (h z hxz);

end removeCone

end RemoveCone


section Simplification

open Classical in
/--
  **Simplification-under-`P` of a finite GL-model** (Lemma 6 in [Bek90] §4, under the
  standing tree hypothesis, see the module docstring): iterating removal of redundant
  cones terminates (the model is finite) in a model simple-under-`P` with the same
  forcing, at the root, of every formula depending on `P`.
-/
theorem exists_simplificationUnder :
  ∀ (n : ℕ) {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsFiniteGL]
    [M.IsTree], Fintype.card M.World = n →
  ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : Fintype M'.World)
    (_ : M'.IsFiniteGL), M'.IsTree ∧ IsSimpleUnder M' P ∧
  ∀ C : Formula α, C.atoms ⊆ P → (M.root.1 ⊩ C ↔ M'.root.1 ⊩ C) := by
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ _ M _ _ _ hcard;
    by_cases hex : ∃ a, Redundant M P a;
    . obtain ⟨a, hred⟩ := hex;
      let a' : M.NonRoot := ⟨a, hred.ne_root⟩;
      haveI hfin : Fintype (M.removeCone a').World := Fintype.ofFinite _;
      haveI : (M.removeCone a').IsTree := removeCone.isTree;
      obtain ⟨κ', hNe', M', hFin', hGL', hTree', hSimple', hEq'⟩ :=
        ih (Fintype.card (M.removeCone a').World) (by rw [← hcard]; exact removeCone.card_lt a')
          (M.removeCone a') rfl;
      exact ⟨κ', hNe', M', hFin', hGL', hTree', hSimple', fun C hC =>
        (removeCone.forces_iff hred hC (M.removeCone a').root.1).symm.trans (hEq' C hC)⟩;
    . exact ⟨κ, ‹Nonempty κ›, M, ‹Fintype M.World›, ‹M.IsFiniteGL›, ‹M.IsTree›,
        fun a hA => hex ⟨a, hA⟩, fun C _ => Iff.rfl⟩;

end Simplification


section OmegaSimplification

omit [DecidableEq α] in
/--
  **`M.graftChainOmega a` is a tree** (`RootedModel.IsTree`), provided `M` is a tree and
  `a` *covers* the root directly (no point strictly between `M.root.1` and `a`). The
  "covers the root" hypothesis is condition 6/7 of [Bek90]'s ω-model definition and is
  necessary for tree-ness.
-/
lemma graftChainOmega.isTree {M : RootedModel κ α} [M.IsFiniteGL] {a : M.World}
  [hTree : M.IsTree] (_Rra : M.root.1 ≺ a)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1) :
  (M.graftChainOmega a).IsTree := by
  have hcov' : ∀ x : M.World, M.root.1 ≺ x → ¬ x ≺ a := by
    intro x Rrx Rxa;
    exact not_rel_root (hcov x ⟨fun h => Std.Irrefl.irrefl a (h ▸ Rxa), Rxa⟩ ▸ Rrx);
  constructor;
  rintro (x₀ | i) (y₀ | j) (z₀ | k) hxz hyz;
  . grind [hTree.tree];
  . grind;
  . grind [hTree.tree, not_rel_root];
  . grind;
  . grind [hTree.tree, not_rel_root];
  . grind;
  . grind;
  . grind;

omit [DecidableEq α] in
/-- **Chain points of an ω-model are never `P`-redundant** (Lemma 8 in [Bek90] §4). -/
lemma graftChainOmega.not_redundant_chainPoint {M : RootedModel κ α} [M.IsFiniteGL]
  (a : M.World) (P : Finset α) (i : ℕ) :
  ¬ (M.graftChainOmega a).Redundant P (Sum.inr i : (M.graftChainOmega a).World) := by
  rintro ⟨-, hred⟩;
  -- `chainPoint (i + 1)` is the unique point covering `chainPoint i` (its immediate
  -- `≺`-predecessor), and every other successor of `chainPoint (i + 1)` already lies
  -- inside `chainPoint i`'s own cone. So testing `Redundant` at `chainPoint (i + 1)`,
  -- every candidate witness `u` is comparable to `chainPoint i`, contradicting the
  -- mutual-incomparability clause.
  have hwa : (M.graftChainOmega a).Rel (Sum.inr (i + 1)) (Sum.inr i) := by
    show i < i + 1;
    omega;
  obtain ⟨u, Bi, hxu, hune, hnau, hyne, hBiua⟩ := hred (Sum.inr (i + 1)) hwa;
  apply hnau;
  rcases u with z | j;
  . show z = a ∨ M.Rel a z;
    exact hxu;
  . have hj : j < i + 1 := hxu;
    have hji : j ≠ i := fun h => hyne (by rw [h]);
    show j < i;
    omega;

omit [DecidableEq α] in
/-- **The grafted point `a` itself is never `P`-redundant either** (Lemma 8 in [Bek90] §4). -/
lemma graftChainOmega.not_redundant_embed_a {M : RootedModel κ α} [M.IsFiniteGL]
  (a : M.World) (P : Finset α) :
  ¬ (M.graftChainOmega a).Redundant P (Sum.inl a : (M.graftChainOmega a).World) := by
  rintro ⟨-, hred⟩;
  -- `chainPoint 0` is the unique point covering `embed a`, and every other successor of
  -- `chainPoint 0` (a proper descendant of `a`) is already comparable to `a`.
  have hwa : (M.graftChainOmega a).Rel (Sum.inr 0) (Sum.inl a) := by
    show a = a ∨ M.Rel a a;
    exact Or.inl rfl;
  obtain ⟨u, Bi, hxu, hune, hnau, hyne, hBiua⟩ := hred (Sum.inr 0) hwa;
  apply hnau;
  rcases u with z | j;
  . have hz : z = a ∨ M.Rel a z := hxu;
    rcases hz with rfl | hMaz;
    . exact absurd rfl hyne;
    . exact hMaz;
  . exact absurd hxu (by omega);

omit [DecidableEq α] in
/-- Any `P`-redundant point of `M.graftChainOmega a` is embedded and distinct from `a`
(an immediate corollary of `not_redundant_chainPoint` and `not_redundant_embed_a`). -/
lemma graftChainOmega.exists_of_redundant {M : RootedModel κ α} [M.IsFiniteGL] {a : M.World}
  {P : Finset α} {a' : (M.graftChainOmega a).World} (hred : (M.graftChainOmega a).Redundant P a') :
  ∃ m : M.World, m ≠ a ∧ a' = Sum.inl m := by
  rcases a' with m | i;
  . exact ⟨m, fun h => not_redundant_embed_a a P (h ▸ hred), rfl⟩;
  . exact absurd hred (not_redundant_chainPoint a P i);

omit [DecidableEq α] in
/-- `a` is never a successor of a `P`-redundant (embedded) point of `M.graftChainOmega a`. -/
lemma graftChainOmega.not_isInConeOf_of_redundant {M : RootedModel κ α} [M.IsFiniteGL]
  {a : M.World} (_Rra : M.root.1 ≺ a)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1)
  {P : Finset α} {m : M.World} (hm : m ≠ M.root.1)
  (hred : (M.graftChainOmega a).Redundant P (Sum.inl m)) :
  ¬ a.IsInConeOf m := by
  rintro (rfl | ham);
  . exact not_redundant_embed_a a P hred;
  . exact hm (hcov m ⟨fun h => Std.Irrefl.irrefl a (h ▸ ham), ham⟩);

omit [DecidableEq α] in
/-- The embedded copy of a non-root point is not the root of `M.graftChainOmega a`. -/
lemma graftChainOmega.inl_ne_root {M : RootedModel κ α} {a m : M.World} (hm : m ≠ M.root.1) :
  (Sum.inl m : (M.graftChainOmega a).World) ≠ (M.graftChainOmega a).root.1 :=
  fun h => hm (Sum.inl.inj h)

omit [DecidableEq α] in
/-- An embedded point of `M.graftChainOmega a` is a successor of the embedded `m` iff it
is a successor of `m` in `M`. -/
lemma graftChainOmega.inl_isInConeOf_inl_iff {M : RootedModel κ α} {a m x : M.World} :
  IsInConeOf (M := (M.graftChainOmega a).toModel) (Sum.inl x) (Sum.inl m) ↔
  x.IsInConeOf m := by
  constructor;
  . rintro (h | h);
    . exact Or.inl (Sum.inl.inj h);
    . exact Or.inr h;
  . rintro (rfl | h);
    . exact Or.inl rfl;
    . exact Or.inr h;

omit [DecidableEq α] in
/-- Chain points of `M.graftChainOmega a` are never successors of an embedded non-root
point, so they all survive removal of its cone. -/
lemma graftChainOmega.not_inr_isInConeOf_inl {M : RootedModel κ α} {a m : M.World}
  (hm : m ≠ M.root.1) (i : ℕ) :
  ¬ IsInConeOf (M := (M.graftChainOmega a).toModel) (Sum.inr i) (Sum.inl m) := by
  rintro (h | h);
  . simp at h;
  . exact hm h;

omit [DecidableEq α] in
/--
  **Removing an embedded cone commutes with grafting the ω-chain**: the evident
  identification of `(M.graftChainOmega a).removeCone (Sum.inl m)` with
  `(M.removeCone m).graftChainOmega a` is a pseudo-epimorphism (in fact an isomorphism).
-/
def graftChainOmega.removeConePseudoEpimorphism {M : RootedModel κ α} [M.IsGL]
  {a m : M.World} [(M.graftChainOmega a).IsGL]
  (hm : m ≠ M.root.1) (hma : ¬ a.IsInConeOf m) :
  ((M.graftChainOmega a).removeCone ⟨Sum.inl m, inl_ne_root hm⟩).toModel →ₚ
  ((M.removeCone ⟨m, hm⟩).graftChainOmega ⟨a, hma⟩).toModel where
  toFun := fun
    | ⟨.inl x, hx⟩ => .inl ⟨x, fun h => hx (inl_isInConeOf_inl_iff.mpr h)⟩
    | ⟨.inr i, _⟩ => .inr i
  forth := by
    rintro ⟨(x | i), hx⟩ ⟨(y | j), hy⟩ Rxy;
    . exact Rxy;
    . exact Subtype.ext Rxy;
    . rcases Rxy with rfl | h;
      . exact Or.inl (Subtype.ext rfl);
      . exact Or.inr h;
    . exact Rxy;
  back := by
    rintro ⟨(x | i), hx⟩ (⟨y, hy⟩ | j) h;
    . exact ⟨⟨.inl y, fun hs => hy (inl_isInConeOf_inl_iff.mp hs)⟩, rfl, h⟩;
    . exact ⟨⟨.inr j, not_inr_isInConeOf_inl hm j⟩, rfl, congrArg Subtype.val h⟩;
    . refine ⟨⟨.inl y, fun hs => hy (inl_isInConeOf_inl_iff.mp hs)⟩, rfl, ?_⟩;
      rcases h with h | h;
      . exact Or.inl (congrArg Subtype.val h);
      . exact Or.inr h;
    . exact ⟨⟨.inr j, not_inr_isInConeOf_inl hm j⟩, rfl, h⟩;
  atomic := by
    rintro ⟨(x | i), hx⟩ b;
    . exact Iff.rfl;
    . exact Iff.rfl;

omit [DecidableEq α] in
/-- Root forcing transfers between `(M.graftChainOmega a).removeCone (Sum.inl m)` and
`(M.removeCone m).graftChainOmega a`. -/
lemma graftChainOmega.removeCone_root_forces_iff {M : RootedModel κ α} [M.IsGL]
  {a m : M.World} [(M.graftChainOmega a).IsGL]
  (hm : m ≠ M.root.1) (hma : ¬ a.IsInConeOf m) {C : Formula α} :
  ((M.graftChainOmega a).removeCone ⟨Sum.inl m, inl_ne_root hm⟩).root.1 ⊩ C ↔
  ((M.removeCone ⟨m, hm⟩).graftChainOmega ⟨a, hma⟩).root.1 ⊩ C :=
  (removeConePseudoEpimorphism hm hma).modal_equivalence _ (A := C)

open Classical in
/-- Strong-induction workhorse for `exists_simplificationUnder_omega` (Lemma 8 in
[Bek90] §4), running on the cardinality of the underlying finite tree. -/
theorem exists_simplificationUnder_omega_aux :
  ∀ (n : ℕ) {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsFiniteGL]
    [M.IsTree] (a : M.World), M.root.1 ≺ a →
  (∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1) →
  Fintype.card M.World = n →
  ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsGL),
  M'.IsTree ∧ IsSimpleUnder M' P ∧
  ∀ C : Formula α, C.atoms ⊆ P →
  ((M.graftChainOmega a).root.1 ⊩ C ↔ M'.root.1 ⊩ C) := by
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ _ M _ _ _ a Rra hcov hcard;
    haveI : (M.graftChainOmega a).IsGL := graftChainOmega.isGL Rra;
    haveI : (M.graftChainOmega a).IsTree := graftChainOmega.isTree Rra hcov;
    by_cases hex : ∃ w, (M.graftChainOmega a).Redundant P w;
    . obtain ⟨w, hred⟩ := hex;
      obtain ⟨m, -, rfl⟩ := graftChainOmega.exists_of_redundant hred;
      have hm : m ≠ M.root.1 := fun h => hred.ne_root (congrArg Sum.inl h);
      have hma : ¬ a.IsInConeOf m :=
        graftChainOmega.not_isInConeOf_of_redundant Rra hcov hm hred;
      haveI : Fintype (M.removeCone ⟨m, hm⟩).World := Fintype.ofFinite _;
      haveI : (M.removeCone ⟨m, hm⟩).IsTree := removeCone.isTree;
      have hcov' : ∀ x : (M.removeCone ⟨m, hm⟩).World,
          x.IsProperPredecessorOf ⟨a, hma⟩ → x = (M.removeCone ⟨m, hm⟩).root.1 := by
        rintro ⟨x, hx⟩ ⟨hne, hR⟩;
        exact Subtype.ext (hcov x ⟨fun h => hne (Subtype.ext h), hR⟩);
      obtain ⟨κ', hNe', M', hGL', hTree', hSimple', hEq'⟩ :=
        ih (Fintype.card (M.removeCone ⟨m, hm⟩).World)
          (by rw [← hcard]; exact removeCone.card_lt ⟨m, hm⟩)
          (M.removeCone ⟨m, hm⟩) ⟨a, hma⟩ Rra hcov' rfl;
      refine ⟨κ', hNe', M', hGL', hTree', hSimple', fun C hC => ?_⟩;
      exact (removeCone.forces_iff (a := ⟨Sum.inl m, graftChainOmega.inl_ne_root hm⟩) hred hC _).symm.trans
        ((graftChainOmega.removeCone_root_forces_iff hm hma).trans (hEq' C hC));
    . exact ⟨graftChainOmega.World M, inferInstance, M.graftChainOmega a,
        ‹(M.graftChainOmega a).IsGL›, ‹(M.graftChainOmega a).IsTree›,
        fun w hw => hex ⟨w, hw⟩, fun C _ => Iff.rfl⟩;

/--
  **Lemma 8 in [Bek90] §4**: a `graftChainOmega`-shaped ω-model over a finite tree `M`
  at a point `a` covering the root admits a `P`-simplification.
-/
theorem exists_simplificationUnder_omega {κ : Type u} [Nonempty κ] {M : RootedModel κ α}
  [M.IsFiniteGL] {a : M.World} [hTree : M.IsTree] (Rra : M.root.1 ≺ a)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1)
  (P : Finset α) :
  ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsGL),
  M'.IsTree ∧ IsSimpleUnder M' P ∧
  ∀ C : Formula α, C.atoms ⊆ P →
  ((M.graftChainOmega a).root.1 ⊩ C ↔ M'.root.1 ⊩ C) := by
  haveI : Fintype M.World := Fintype.ofFinite _;
  exact exists_simplificationUnder_omega_aux (Fintype.card M.World) M a Rra hcov rfl;

end OmegaSimplification

end RootedModel

end
