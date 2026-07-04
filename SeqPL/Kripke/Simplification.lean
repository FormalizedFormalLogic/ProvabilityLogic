module

public import SeqPL.Kripke.Preservation
public import SeqPL.Kripke.PointGenerate
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
def IsTree (M : RootedModel κ α) : Prop :=
  ∀ x y z : M.World, x ≺ z → y ≺ z → x = y ∨ x ≺ y ∨ y ≺ x

variable {M : RootedModel κ α} {P : Finset α}

open Model (BisimulationUnder World.forces_iff_of_pbisimilar)
open Model.World (IsSuccessorOf)

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
lemma not_isSuccessorOf_root_of_ne {a : M.World} (ha : a ≠ M.root.1) :
    ¬ M.root.1.IsSuccessorOf a := by
  rintro (h | h);
  . exact ha h.symm;
  . exact Std.Irrefl.irrefl M.root.1 (IsTrans.trans _ _ _ (M.root.2 a ha) h);

/-- The carrier of `removeCone`, indexed (redundantly, for the sake of instance search)
by the proof `ha` that `a` is not the root. -/
abbrev removeCone.World (M : RootedModel κ α) (a : M.World) (_ha : a ≠ M.root.1) : Type _ :=
  {x : M.World // ¬ x.IsSuccessorOf a}

omit [DecidableEq α] in
instance removeCone.instNonempty (a : M.World) (ha : a ≠ M.root.1) :
    Nonempty (removeCone.World M a ha) :=
  ⟨⟨M.root.1, not_isSuccessorOf_root_of_ne ha⟩⟩

/-- Removal of the cone above `a` (Bek90 §4, item 3): the sub-model on the points that
are not successors of `a`. -/
def removeCone (M : RootedModel κ α) [M.IsGL] (a : M.World) (ha : a ≠ M.root.1) :
    RootedModel (removeCone.World M a ha) α where
  Rel' x y := M.Rel x.1 y.1
  Val' x q := M.Val x.1 q
  root := ⟨⟨M.root.1, not_isSuccessorOf_root_of_ne ha⟩, by
    rintro ⟨x, hx⟩ hne;
    show M.Rel M.root.1 x;
    exact M.root.2 x (by rintro rfl; exact hne rfl)⟩

namespace removeCone

instance instTrans (a : M.World) (ha : a ≠ M.root.1) : IsTrans _ (M.removeCone a ha).Rel :=
  ⟨fun x y z => IsTrans.trans x.1 y.1 z.1⟩
instance instIrrefl (a : M.World) (ha : a ≠ M.root.1) : Std.Irrefl (M.removeCone a ha).Rel :=
  ⟨fun x => Std.Irrefl.irrefl x.1⟩

omit [DecidableEq α] in
lemma isTree {a : M.World} {ha : a ≠ M.root.1} (hTree : M.IsTree) :
    (M.removeCone a ha).IsTree := by
  rintro x y z hxz hyz;
  rcases hTree x.1 y.1 z.1 hxz hyz with h | h | h;
  . exact Or.inl (Subtype.ext h);
  . exact Or.inr (Or.inl h);
  . exact Or.inr (Or.inr h);

section Finite

set_option linter.overlappingInstances false

variable [M.IsFiniteGL]

instance instFinite (a : M.World) (ha : a ≠ M.root.1) : Finite (M.removeCone a ha).World :=
  Subtype.finite

instance instIsFiniteGL (a : M.World) (ha : a ≠ M.root.1) : (M.removeCone a ha).IsFiniteGL where

omit [DecidableEq α] [M.IsFiniteGL] in
lemma card_lt (a : M.World) (ha : a ≠ M.root.1) [Fintype M.World]
    [Fintype (M.removeCone a ha).World] :
    Fintype.card (M.removeCone a ha).World < Fintype.card M.World :=
  Fintype.card_subtype_lt (p := fun x : M.World => ¬ x.IsSuccessorOf a) (x := a)
    (not_not_intro (Or.inl rfl))

end Finite

/--
  **Forcing preservation under removal of a redundant cone** (core of the proof of
  Lemma 6 in [Bek90] §4): if `M` is a tree and `a` is `P`-redundant, then for every
  point `x` outside `a`'s cone and every formula `C` depending on `P`, forcing of `C`
  at `x` in `M.removeCone a ha` agrees with forcing of `C` at `x` in `M`.
-/
theorem forces_iff {a : M.World} {ha : a ≠ M.root.1} (hTree : M.IsTree) (hred : Redundant M P a) :
  ∀ {C : Formula α}, C.atoms ⊆ P →
  ∀ x : (M.removeCone a ha).World,
  Model.World.Forces (M := (M.removeCone a ha).toModel) x C ↔ x.1 ⊩ C := by
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
      by_cases hzS : z.IsSuccessorOf a;
      . -- `z` was removed: transport the box-witness through the redundancy of `a`.
        have hxa : x ≺ a := by
          rcases hzS with rfl | haz;
          . exact hxz;
          . rcases hTree x a z hxz haz with (rfl | hxa | hax);
            . exact absurd (Or.inl rfl) hx;
            . exact hxa;
            . exact absurd (Or.inr hax) hx;
        obtain ⟨y, Bi, hxy, hyna, hnay, hyne, hBiya⟩ := hred.exists_alt x hxa;
        have hynS : ¬ y.IsSuccessorOf a := by rintro (rfl | h); exacts [hyne rfl, hnay h];
        have hyB : y ⊩ B := (ihB hC ⟨y, hynS⟩).mp (h ⟨y, hynS⟩ hxy);
        have haB : a ⊩ B := (World.forces_iff_of_pbisimilar Bi hBiya hC).mp hyB;
        rcases hzS with rfl | haz;
        . exact haB;
        . obtain ⟨z', hBiz'z, hyz'⟩ := Bi.back hBiya haz;
          have hxz' : x ≺ z' := IsTrans.trans _ _ _ hxy hyz';
          have hz'nS : ¬ z'.IsSuccessorOf a := by
            rintro (rfl | haz');
            . exact hyna hyz';
            . rcases hTree y a z' hyz' haz' with (hya | hya | hya);
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
    ∀ (n : ℕ) {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsFiniteGL],
      M.IsTree → Fintype.card M.World = n →
      ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : Fintype M'.World)
        (_ : M'.IsFiniteGL), M'.IsTree ∧ IsSimpleUnder M' P ∧
        ∀ C : Formula α, C.atoms ⊆ P → (M.root.1 ⊩ C ↔ M'.root.1 ⊩ C) := by
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ _ M _ _ hTree hcard;
    by_cases hex : ∃ a, Redundant M P a;
    . obtain ⟨a, hred⟩ := hex;
      have ha : a ≠ M.root.1 := hred.ne_root;
      haveI hfin : Fintype (M.removeCone a ha).World := Fintype.ofFinite _;
      obtain ⟨κ', hNe', M', hFin', hGL', hTree', hSimple', hEq'⟩ :=
        ih (Fintype.card (M.removeCone a ha).World) (by rw [← hcard]; exact removeCone.card_lt a ha)
          (M.removeCone a ha) (removeCone.isTree hTree) rfl;
      exact ⟨κ', hNe', M', hFin', hGL', hTree', hSimple', fun C hC =>
        (removeCone.forces_iff hTree hred hC (M.removeCone a ha).root.1).symm.trans (hEq' C hC)⟩;
    . exact ⟨κ, ‹Nonempty κ›, M, ‹Fintype M.World›, ‹M.IsFiniteGL›, hTree,
        fun a hA => hex ⟨a, hA⟩, fun C _ => Iff.rfl⟩;

end Simplification


section OmegaSimplification

omit [DecidableEq α] in
/--
  Auxiliary step for `graftChainOmega.isTree`: any `M`-predecessor `x₀` of a point
  `z₀` comparable with `a` (i.e. `z₀ = a` or `a ≺ z₀`) is itself comparable with the
  root or with `a`. Uses `hcov` (`a` covers the root, no intermediate points) to rule
  out the case where `x₀` is a *proper* intermediate ancestor of `a` distinct from the
  root.
-/
private lemma graftChainOmega.isTree_aux {M : RootedModel κ α} [M.IsFiniteGL] {a : M.World}
    (hTree : M.IsTree) (Rra : M.root.1 ≺ a) (hcov : ∀ x : M.World, M.root.1 ≺ x → ¬ x ≺ a)
    {x₀ z₀ : M.World} (hx : x₀ ≺ z₀) (hz : z₀ = a ∨ M.Rel a z₀) :
    x₀ = M.root.1 ∨ x₀ = a ∨ M.Rel a x₀ := by
  rcases hz with hz | haz;
  . rw [hz] at hx;
    rcases hTree x₀ M.root.1 a hx Rra with h | h | h;
    . exact Or.inl h;
    . exact absurd h not_rel_root;
    . exact absurd hx (hcov x₀ h);
  . rcases hTree x₀ a z₀ hx haz with h | h | h;
    . exact Or.inr (Or.inl h);
    . rcases hTree x₀ M.root.1 a h Rra with h' | h' | h';
      . exact Or.inl h';
      . exact absurd h' not_rel_root;
      . exact absurd h (hcov x₀ h');
    . exact Or.inr (Or.inr h);

omit [DecidableEq α] in
/--
  **`M.graftChainOmega a` is a tree** (`RootedModel.IsTree`), provided `M` is a tree
  and `a` *covers* the root directly (no point strictly between `M.root.1` and `a`).
  This "covers the root" hypothesis is exactly condition 6/7 of [Bek90]'s ω-model
  definition (the expanded point must cover the minimum); without it the tree property
  genuinely fails (a counterexample: an intermediate ancestor `x₀` of `a`, `x₀ ≠ root`,
  is then incomparable with `chainPoint 0` in `M.graftChainOmega a`).
-/
lemma graftChainOmega.isTree {M : RootedModel κ α} [M.IsFiniteGL] {a : M.World}
    (hTree : M.IsTree) (Rra : M.root.1 ≺ a) (hcov : ∀ x : M.World, M.root.1 ≺ x → ¬ x ≺ a) :
    (M.graftChainOmega a).IsTree := by
  rintro (x₀ | i) (y₀ | j) (z₀ | k) hxz hyz;
  . rcases hTree x₀ y₀ z₀ hxz hyz with h | h | h;
    . exact Or.inl (by rw [h]);
    . exact Or.inr (Or.inl h);
    . exact Or.inr (Or.inr h);
  . exact Or.inl (by rw [show x₀ = M.root.1 from hxz, show y₀ = M.root.1 from hyz]);
  . rcases graftChainOmega.isTree_aux hTree Rra hcov hxz hyz with h | h | h;
    . exact Or.inr (Or.inl h);
    . exact Or.inr (Or.inr (Or.inl h));
    . exact Or.inr (Or.inr (Or.inr h));
  . exact Or.inr (Or.inl hxz);
  . rcases graftChainOmega.isTree_aux hTree Rra hcov hyz hxz with h | h | h;
    . exact Or.inr (Or.inr h);
    . exact Or.inr (Or.inl (Or.inl h));
    . exact Or.inr (Or.inl (Or.inr h));
  . exact Or.inr (Or.inr hyz);
  . rcases lt_trichotomy i j with h | h | h;
    . exact Or.inr (Or.inr h);
    . exact Or.inl (by rw [h]);
    . exact Or.inr (Or.inl h);
  . rcases lt_trichotomy i j with h | h | h;
    . exact Or.inr (Or.inr h);
    . exact Or.inl (by rw [h]);
    . exact Or.inr (Or.inl h);

omit [DecidableEq α] in
/--
  **Chain points of an ω-model are never `P`-redundant** (Lemma 8 in [Bek90] §4: "if
  `b ≺ x ≺ r`, then, by condition 6 of the definition of ω-model, `x` is the unique
  point covering some point `y`; hence there are no cones above `𝒳_x` other than
  `𝒳_x` itself").

  The precise mechanism (matching the paper's "unique covering point" argument,
  rather than any rank/depth invariant): `chainPoint (i + 1)` is the *unique* point
  covering `chainPoint i` -- i.e. its immediate `≺`-predecessor -- and in fact *every*
  one of `chainPoint (i + 1)`'s successors other than `chainPoint i` itself already
  lies inside `chainPoint i`'s own cone (either a lower chain point `chainPoint j`,
  `j < i`, or a point of `M`'s cone above `a`, both of which `chainPoint i` directly
  relates to by construction). So testing `Redundant` at the specific predecessor
  `chainPoint (i + 1)` of `chainPoint i`, *every* candidate witness is automatically
  comparable to `chainPoint i`, hence excluded by the mutual-incomparability clause.
-/
lemma graftChainOmega.not_redundant_chainPoint {M : RootedModel κ α} [M.IsFiniteGL]
    (a : M.World) (P : Finset α) (i : ℕ) :
    ¬ (M.graftChainOmega a).Redundant P (Sum.inr i : (M.graftChainOmega a).World) := by
  rintro ⟨-, hred⟩;
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
/--
  **The grafted point `a` itself is never `P`-redundant either**, by the same
  "unique covering point" mechanism as `not_redundant_chainPoint`: `chainPoint 0` is
  the unique point covering `embed a`, and every other successor of `chainPoint 0`
  (a proper descendant of `a` within `M`) is already comparable to `a`.
-/
lemma graftChainOmega.not_redundant_embed_a {M : RootedModel κ α} [M.IsFiniteGL]
    (a : M.World) (P : Finset α) :
    ¬ (M.graftChainOmega a).Redundant P (Sum.inl a : (M.graftChainOmega a).World) := by
  rintro ⟨-, hred⟩;
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
/-- `a` is never a successor of a `P`-redundant (embedded) point of `M.graftChainOmega
a` -- combines `graftChainOmega.isTree`'s "covers the root" hypothesis (ruling out `m`
being a proper ancestor of `a` other than the root) with `m ≠ a`. -/
lemma graftChainOmega.not_isSuccessorOf_of_redundant {M : RootedModel κ α} [M.IsFiniteGL]
    {a : M.World} (_Rra : M.root.1 ≺ a) (hcov : ∀ x : M.World, M.root.1 ≺ x → ¬ x ≺ a)
    {P : Finset α} {m : M.World} (hm : m ≠ M.root.1)
    (hred : (M.graftChainOmega a).Redundant P (Sum.inl m)) :
    ¬ a.IsSuccessorOf m := by
  rintro (rfl | ham);
  . exact not_redundant_embed_a a P hred;
  . exact hcov m (M.root.2 m hm) ham;

/--
  **Lemma 8 in [Bek90] §4**, specialized to `graftChainOmega`-shaped ω-models (the
  paper's actual scope: an "ω-model" is precisely a finite `GL`-model expanded to
  length `ω` at a point *covering the minimum*, see [Bek90] p.261 item 6/7 and the
  corollary to Lemma 5). For a finite tree `M` and a point `a` covering `M`'s root,
  the ω-model `M.graftChainOmega a` admits a `P`-simplification.

  **Not proved in this session.** By `graftChainOmega.exists_of_redundant`, only
  embedded points can ever be redundant, and `M` is finite, so the natural strategy is
  the same strong induction on `Fintype.card M.World` as `exists_simplificationUnder`,
  removing one redundant embedded point's cone at a time. The missing piece is a
  lemma identifying `(M.graftChainOmega a).removeCone (Sum.inl m) _` (for a redundant
  embedded `m`, which survives with `a` intact by `not_isSuccessorOf_of_redundant`)
  with `(M.removeCone m _).graftChainOmega a'` for the corresponding image `a'` of
  `a` -- i.e. that "removing an embedded cone" commutes with "grafting the ω-chain".
  This is plausible (removing `cone(m)` never touches the chain, since chain points
  only relate into `cone(a)` and `m` is not an ancestor of `a`) but constructing the
  explicit order-isomorphism (and re-deriving `graftChainOmega.isTree`/`IsFiniteGL`
  for the smaller base model at each step) was not completed this session; see
  `.direct/exists-lemma56.md`.
-/
theorem exists_simplificationUnder_omega {M : RootedModel κ α} [M.IsFiniteGL] {a : M.World}
    (hTree : M.IsTree) (Rra : M.root.1 ≺ a) (hcov : ∀ x : M.World, M.root.1 ≺ x → ¬ x ≺ a)
    (P : Finset α) :
    ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsGL),
      M'.IsTree ∧ IsSimpleUnder M' P ∧
      ∀ C : Formula α, C.atoms ⊆ P →
        ((M.graftChainOmega a).root.1 ⊩ C ↔ M'.root.1 ⊩ C) := by
  sorry

end OmegaSimplification

end RootedModel

end
