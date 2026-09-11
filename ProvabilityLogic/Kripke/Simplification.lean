module

public import ProvabilityLogic.Kripke.Cone
public import ProvabilityLogic.Kripke.GraftOmega

/-!
# `P`-simplification of GL-models

This file formalizes removal of a redundant cone and the `P`-simplification lemmas, for
finite GL-models and for `graftOmega`-shaped ω-models. Tree-ness, which `Model.IsFiniteGL`
does not encode but the cone-removal argument needs, is a standing explicit hypothesis
`RootedModel.IsTree`; `P`-isomorphism of cones is formalized as `Model.BisimulationUnder`.

## References

- [Bek90, §4, item 3, Lemma 6, Lemma 8]
-/

@[expose]
public section

universe u

variable [Nonempty κ] {α : Type u}

namespace RootedModel

/-- `M` has the tree property if the `≺`-ancestors of any point are linearly ordered.
This is the standing assumption on "GL-models" in the classification literature. -/
class IsTree (M : RootedModel κ α) : Prop where
  tree : ∀ x y z : M.World, x ≺ z → y ≺ z → x = y ∨ x ≺ y ∨ y ≺ x

/-- A *finite GL tree*: a finite GL-model whose frame is a tree. This is the model class
of the classical "GL-models", i.e. finite irreflexive transitive trees. -/
class IsFiniteGLTree (M : RootedModel κ α) : Prop extends Model.IsFiniteGL M.toModel, IsTree M

instance {M : RootedModel κ α} [M.IsFiniteGL] [M.IsTree] : M.IsFiniteGLTree where

variable {M : RootedModel κ α} {P : Finset α}

open Model (BisimulationUnder World.forces_iff_of_pbisimilar)
open Model.World (IsInConeOf IsProperPredecessorOf)

/--
  A non-root point `a` is `P`-**redundant** if every ancestor `x ≺ a` has an alternative
  successor `y`, incomparable with `a`, whose cone is `P`-bisimilar to the cone above `a`.

  - [Bek90, §4, item 3]
-/
def Redundant (M : RootedModel κ α) (P : Finset α) (a : M.NonRoot) : Prop :=
  ∀ x : M.World, x ≺ a.1 →
    ∃ (y : M.World) (Bi : BisimulationUnder P M.toModel M.toModel),
      x ≺ y ∧ ¬ y ≺ a.1 ∧ ¬ a.1 ≺ y ∧ y ≠ a.1 ∧ Bi y a.1

def IsSimpleUnder (M : RootedModel κ α) (P : Finset α) : Prop :=
  ∀ a : M.NonRoot, ¬ Redundant M P a

/-- - [Bek90, Lemma 1, §5] -/
lemma Redundant.insert_of_root_forces_box [DecidableEq α] {M : RootedModel κ α}
  [IsTrans _ M.Rel] [Std.Irrefl M.Rel] {P : Finset α} {p : α} {w : M.NonRoot}
  (hred : Redundant M P w) (hbox : M.root.1 ⊩[_] (□(#p))) :
  Redundant M (insert p P) w := by
  intro x Rxw;
  obtain ⟨y, Bi, hxy, hynw, hnwy, hyne, hBiyw⟩ := hred x Rxw;
  let Bi' : BisimulationUnder (insert p P) M.toModel M.toModel :=
    { toRel := fun u v => Bi u v ∧ u ≠ M.root.1 ∧ v ≠ M.root.1
      atomic := by
        rintro u v q hq ⟨hBi, hu, hv⟩;
        rcases Finset.mem_insert.mp hq with rfl | hqP;
        . have h₁ : M.Val u q := hbox u (M.root.2 u hu);
          have h₂ : M.Val v q := hbox v (M.root.2 v hv);
          tauto;
        . exact Bi.atomic hqP hBi;
      forth := by
        rintro u u₁ v ⟨hBi, hu, hv⟩ Ruu₁;
        obtain ⟨v₁, hBi₁, Rvv₁⟩ := Bi.forth hBi Ruu₁;
        exact ⟨v₁, ⟨hBi₁, fun h => not_rel_root (h ▸ Ruu₁), fun h => not_rel_root (h ▸ Rvv₁)⟩, Rvv₁⟩;
      back := by
        rintro u v v₁ ⟨hBi, hu, hv⟩ Rvv₁;
        obtain ⟨u₁, hBi₁, Ruu₁⟩ := Bi.back hBi Rvv₁;
        exact ⟨u₁, ⟨hBi₁, fun h => not_rel_root (h ▸ Ruu₁), fun h => not_rel_root (h ▸ Rvv₁)⟩, Ruu₁⟩ };
  exact ⟨y, Bi', hxy, hynw, hnwy, hyne,
    hBiyw, fun h => not_rel_root (h ▸ hxy), w.2⟩;

/-- - [Bek90, Lemma 1, §5] -/
lemma IsSimpleUnder.of_insert_of_root_forces_box [DecidableEq α] {M : RootedModel κ α}
  [IsTrans _ M.Rel] [Std.Irrefl M.Rel] {P : Finset α} {p : α}
  (h : M.IsSimpleUnder (insert p P)) (hbox : M.root.1 ⊩[_] (□(#p))) :
  M.IsSimpleUnder P :=
  fun w hred => h w (hred.insert_of_root_forces_box hbox)

section RemoveCone

variable [M.IsGL]

lemma not_isInConeOf_root_of_ne {a : M.World} (ha : a ≠ M.root.1) :
  ¬ M.root.1.IsInConeOf a := by
  rintro (h | h);
  . exact ha h.symm;
  . exact Std.Irrefl.irrefl M.root.1 (IsTrans.trans _ _ _ (M.root.2 a ha) h);

abbrev removeCone.World (M : RootedModel κ α) (a : M.NonRoot) : Type _ :=
  {x : M.World // ¬ x.IsInConeOf a.1}

instance removeCone.instNonempty (a : M.NonRoot) : Nonempty (removeCone.World M a) :=
  ⟨⟨M.root.1, not_isInConeOf_root_of_ne a.2⟩⟩

/--
Removal of the cone above `a`: the sub-model on the points that are not successors of `a`.

- [Bek90, §4, item 3]
-/
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

lemma isTree {a : M.NonRoot} [hTree : M.IsTree] :
  (M.removeCone a).IsTree := by
  constructor;
  intro x y z hxz hyz;
  rcases hTree.tree x.1 y.1 z.1 hxz hyz with h | h | h;
  . left; exact Subtype.ext h;
  . right; left; exact h;
  . right; right; exact h;

section Finite

lemma card_lt (a : M.NonRoot) [Fintype M.World] [Fintype (M.removeCone a).World] :
  Fintype.card (M.removeCone a).World < Fintype.card M.World :=
  Fintype.card_subtype_lt (p := fun x : M.World => ¬ x.IsInConeOf a.1) (x := a.1)
    (not_not_intro (Or.inl rfl))

variable [M.IsFiniteGL]

-- `M.IsGL` and `M.IsFiniteGL` both supply `IsTrans M.World Model.Rel` here; the overlap
-- is deliberate, the explicit `[M.IsGL]` recording that `removeCone` is GL-only.
set_option linter.overlappingInstances false in
instance (a : M.NonRoot) : Finite (M.removeCone a).World :=
  Subtype.finite

set_option linter.overlappingInstances false in
instance (a : M.NonRoot) : (M.removeCone a).IsFiniteGL where

end Finite

/--
  **Forcing preservation under removal of a redundant cone**: if `M` is a tree and `a` is
  `P`-redundant, a formula depending on `P` is forced at a point outside `a`'s cone in
  `M.removeCone a` exactly when it is forced there in `M`.

  - [Bek90, Lemma 6, §4]
-/
theorem forces_iff [DecidableEq α] {a : M.NonRoot} [hTree : M.IsTree] (hred : Redundant M P a) :
  ∀ {C : Formula α}, C.atoms ⊆ P →
  ∀ x : (M.removeCone a).World,
  x ⊩[(M.removeCone a).toModel] C ↔ x.1 ⊩[M.toModel] C := by
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
      . have hxa : x ≺ a.1 := by
          rcases hzS with rfl | haz;
          . exact hxz;
          . rcases hTree.tree x a.1 z hxz haz with (rfl | hxa | hax);
            . exact absurd (Or.inl rfl) hx;
            . exact hxa;
            . exact absurd (Or.inr hax) hx;
        obtain ⟨y, Bi, hxy, hyna, hnay, hyne, hBiya⟩ := hred x hxa;
        have hynS : ¬ y.IsInConeOf a.1 := by rintro (rfl | h); exacts [hyne rfl, hnay h];
        have hyB : y ⊩[M.toModel] B := (ihB hC ⟨y, hynS⟩).mp (h ⟨y, hynS⟩ hxy);
        have haB : a.1 ⊩[M.toModel] B := (World.forces_iff_of_pbisimilar Bi hBiya hC).mp hyB;
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
          have hz'B : z' ⊩[M.toModel] B := (ihB hC ⟨z', hz'nS⟩).mp (h ⟨z', hz'nS⟩ hxz');
          exact (World.forces_iff_of_pbisimilar Bi hBiz'z hC).mp hz'B;
      . exact (ihB hC ⟨z, hzS⟩).mp (h ⟨z, hzS⟩ hxz);
    . intro h ⟨z, hz⟩ hxz;
      exact (ihB hC ⟨z, hz⟩).mpr (h z hxz);

end removeCone

end RemoveCone


section Simplification

open Classical in
/--
**Simplification-under-`P` of a finite GL-model**: every finite GL tree admits a
`P`-simplification with the same forcing, at the root, of every formula depending on `P`.

- [Bek90, Lemma 6, §4]
-/
theorem exists_simplificationUnder :
  ∀ (n : ℕ) {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsFiniteGLTree],
    Fintype.card M.World = n →
  ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : Fintype M'.World)
    (_ : M'.IsFiniteGL), M'.IsTree ∧ IsSimpleUnder M' P ∧
  ∀ C : Formula α, C.atoms ⊆ P → (M.root.1 ⊩[M.toModel] C ↔ M'.root.1 ⊩[M'.toModel] C) := by
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ _ M _ _ hcard;
    by_cases hex : ∃ a : M.NonRoot, Redundant M P a;
    . obtain ⟨a, hred⟩ := hex;
      have hfin : Fintype (M.removeCone a).World := Fintype.ofFinite _;
      have : (M.removeCone a).IsTree := removeCone.isTree;
      obtain ⟨κ', hNe', M', hFin', hGL', hTree', hSimple', hEq'⟩ :=
        ih (Fintype.card (M.removeCone a).World) (by rw [← hcard]; exact removeCone.card_lt a)
          (M.removeCone a) rfl;
      exact ⟨κ', hNe', M', hFin', hGL', hTree', hSimple', fun C hC =>
        (removeCone.forces_iff hred hC (M.removeCone a).root.1).symm.trans (hEq' C hC)⟩;
    . exact ⟨κ, ‹Nonempty κ›, M, ‹Fintype M.World›, inferInstance, inferInstance,
        fun a hA => hex ⟨a, hA⟩, fun C _ => Iff.rfl⟩;

end Simplification


section OmegaSimplification

/--
  `M.graftOmega a` is a tree provided `M` is a tree and `a` *covers* the root directly.
  The covering hypothesis is necessary for tree-ness.

  - [Bek90, condition 6/7]
-/
lemma graftOmega.isTree {M : RootedModel κ α} [hTree : M.IsFiniteGLTree] {a : M.NonRoot}
  (_Rra : M.root.1 ≺ a.1)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a.1 → x = M.root.1) :
  (M.graftOmega a).IsTree := by
  have hcov' : ∀ x : M.World, M.root.1 ≺ x → ¬ x ≺ a.1 := by
    intro x Rrx Rxa;
    exact not_rel_root (hcov x ⟨fun h => Std.Irrefl.irrefl a.1 (h ▸ Rxa), Rxa⟩ ▸ Rrx);
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

lemma graftOmega.inl_ne_root {M : RootedModel κ α} {a : M.NonRoot} {m : M.World} (hm : m ≠ M.root.1) :
  (Sum.inl m : (M.graftOmega a).World) ≠ (M.graftOmega a).root.1 :=
  fun h => hm (Sum.inl.inj h)

/-- - [Bek90, Lemma 8, §4] -/
lemma graftOmega.not_redundant_chainPoint {M : RootedModel κ α} [M.IsFiniteGL]
  (a : M.NonRoot) (P : Finset α) (i : ℕ) :
  ¬ (M.graftOmega a).Redundant P ⟨Sum.inr i, inr_ne_root⟩ := by
  intro hred;
  have hwa : (M.graftOmega a).Rel (Sum.inr (i + 1)) (Sum.inr i) := by
    show i < i + 1;
    omega;
  obtain ⟨u, Bi, hxu, hune, hnau, hyne, hBiua⟩ := hred (Sum.inr (i + 1)) hwa;
  apply hnau;
  rcases u with z | j;
  . show z = a.1 ∨ M.Rel a.1 z;
    exact hxu;
  . have hj : j < i + 1 := hxu;
    have hji : j ≠ i := fun h => hyne (by rw [h]);
    show j < i;
    omega;

/-- - [Bek90, Lemma 8, §4] -/
lemma graftOmega.not_redundant_embed_a {M : RootedModel κ α} [M.IsFiniteGL]
  (a : M.NonRoot) (P : Finset α) :
  ¬ (M.graftOmega a).Redundant P ⟨Sum.inl a.1, inl_ne_root a.2⟩ := by
  intro hred;
  have hwa : (M.graftOmega a).Rel (Sum.inr 0) (Sum.inl a.1) := by
    show a.1 = a.1 ∨ M.Rel a.1 a.1;
    left; rfl;
  obtain ⟨u, Bi, hxu, hune, hnau, hyne, hBiua⟩ := hred (Sum.inr 0) hwa;
  apply hnau;
  rcases u with z | j;
  . have hz : z = a.1 ∨ M.Rel a.1 z := hxu;
    rcases hz with rfl | hMaz;
    . exact absurd rfl hyne;
    . exact hMaz;
  . exact absurd hxu (by omega);

lemma graftOmega.exists_of_redundant {M : RootedModel κ α} [M.IsFiniteGL] {a : M.NonRoot}
  {P : Finset α} {a' : (M.graftOmega a).NonRoot} (hred : (M.graftOmega a).Redundant P a') :
  ∃ (m : M.World) (hm : m ≠ M.root.1), m ≠ a.1 ∧ a' = ⟨Sum.inl m, inl_ne_root hm⟩ := by
  obtain ⟨a1, hane'⟩ := a';
  rcases a1 with m | i;
  . exact ⟨m, fun h => hane' (congrArg Sum.inl h),
      fun h => not_redundant_embed_a a P (h ▸ hred), rfl⟩;
  . exact absurd hred (not_redundant_chainPoint a P i);

lemma graftOmega.not_isInConeOf_of_redundant {M : RootedModel κ α} [M.IsFiniteGL]
  {a : M.NonRoot} (_Rra : M.root.1 ≺ a.1)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a.1 → x = M.root.1)
  {P : Finset α} {m : M.World} (hm : m ≠ M.root.1)
  (hred : (M.graftOmega a).Redundant P ⟨Sum.inl m, inl_ne_root hm⟩) :
  ¬ a.1.IsInConeOf m := by
  rintro (rfl | ham);
  . exact not_redundant_embed_a a P hred;
  . exact hm (hcov m ⟨fun h => Std.Irrefl.irrefl a.1 (h ▸ ham), ham⟩);

lemma graftOmega.inl_isInConeOf_inl_iff {M : RootedModel κ α} {a : M.NonRoot} {m x : M.World} :
  IsInConeOf (M := (M.graftOmega a).toModel) (Sum.inl x) (Sum.inl m) ↔
  x.IsInConeOf m := by
  constructor;
  . rintro (h | h);
    . left; exact Sum.inl.inj h;
    . right; exact h;
  . rintro (rfl | h);
    . left; rfl;
    . right; exact h;

lemma graftOmega.not_inr_isInConeOf_inl {M : RootedModel κ α} {a : M.NonRoot} {m : M.World}
  (hm : m ≠ M.root.1) (i : ℕ) :
  ¬ IsInConeOf (M := (M.graftOmega a).toModel) (Sum.inr i) (Sum.inl m) := by
  rintro (h | h);
  . simp at h;
  . exact hm h;

/-- **Removing an embedded cone commutes with grafting the ω-chain**: the evident
identification of `(M.graftOmega a).removeCone (Sum.inl m)` with
`(M.removeCone m).graftOmega a` is a pseudo-epimorphism. -/
def graftOmega.removeConePseudoEpimorphism {M : RootedModel κ α} [M.IsGL]
  {a : M.NonRoot} {m : M.World} [(M.graftOmega a).IsGL]
  (hm : m ≠ M.root.1) (hma : ¬ a.1.IsInConeOf m) :
  ((M.graftOmega a).removeCone ⟨Sum.inl m, inl_ne_root hm⟩).toModel →ₚ
  ((M.removeCone ⟨m, hm⟩).graftOmega
    ⟨⟨a.1, hma⟩, fun h => a.2 (congrArg Subtype.val h)⟩).toModel where
  toFun := fun
    | ⟨.inl x, hx⟩ => .inl ⟨x, fun h => hx (inl_isInConeOf_inl_iff.mpr h)⟩
    | ⟨.inr i, _⟩ => .inr i
  forth := by
    rintro ⟨(x | i), hx⟩ ⟨(y | j), hy⟩ Rxy;
    . exact Rxy;
    . exact Subtype.ext Rxy;
    . rcases Rxy with rfl | h;
      . left; exact Subtype.ext rfl;
      . right; exact h;
    . exact Rxy;
  back := by
    rintro ⟨(x | i), hx⟩ (⟨y, hy⟩ | j) h;
    . exact ⟨⟨.inl y, fun hs => hy (inl_isInConeOf_inl_iff.mp hs)⟩, rfl, h⟩;
    . exact ⟨⟨.inr j, not_inr_isInConeOf_inl hm j⟩, rfl, congrArg Subtype.val h⟩;
    . exact ⟨⟨.inl y, fun hs => hy (inl_isInConeOf_inl_iff.mp hs)⟩, rfl, by
        rcases h with h | h;
        . left; exact congrArg Subtype.val h;
        . right; exact h⟩;
    . exact ⟨⟨.inr j, not_inr_isInConeOf_inl hm j⟩, rfl, h⟩;
  atomic := by
    rintro ⟨(x | i), hx⟩ b;
    . exact Iff.rfl;
    . exact Iff.rfl;

lemma graftOmega.removeCone_root_forces_iff {M : RootedModel κ α} [M.IsGL]
  {a : M.NonRoot} {m : M.World} [(M.graftOmega a).IsGL]
  (hm : m ≠ M.root.1) (hma : ¬ a.1.IsInConeOf m) {C : Formula α} :
  ((M.graftOmega a).removeCone ⟨Sum.inl m, inl_ne_root hm⟩).root.1
    ⊩[((M.graftOmega a).removeCone ⟨Sum.inl m, inl_ne_root hm⟩).toModel] C ↔
  ((M.removeCone ⟨m, hm⟩).graftOmega
    ⟨⟨a.1, hma⟩, fun h => a.2 (congrArg Subtype.val h)⟩).root.1
    ⊩[((M.removeCone ⟨m, hm⟩).graftOmega
      ⟨⟨a.1, hma⟩, fun h => a.2 (congrArg Subtype.val h)⟩).toModel] C :=
  (removeConePseudoEpimorphism hm hma).modal_equivalence _ (A := C)

open Classical in
/--
Auxiliary form of `exists_simplificationUnder_omega'` carrying the induction on the
cardinality of the underlying finite tree.

- [Bek90, Lemma 8, §4]
-/
theorem exists_simplificationUnder_omega_aux [DecidableEq α] :
  ∀ (n : ℕ) {κ : Type u} [Nonempty κ] (M : RootedModel κ α) [Fintype M.World] [M.IsFiniteGLTree]
    (a : M.World) (Rra : M.root.1 ≺ a),
  (∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1) →
  Fintype.card M.World = n →
  ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsFiniteGL)
    (_ : M'.IsTree) (a' : M'.NonRoot),
  M'.root.1 ≺ a'.1 ∧
  (∀ x : M'.World, x.IsProperPredecessorOf a'.1 → x = M'.root.1) ∧
  ((∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a) →
    ∀ x : M'.World, M'.root.1 ≺ x → x.IsInConeOf a'.1) ∧
  IsSimpleUnder (M'.graftOmega a') P ∧
  ∀ C : Formula α, C.atoms ⊆ P →
  ((M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1
    ⊩[(M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).toModel] C ↔
    (M'.graftOmega a').root.1 ⊩[(M'.graftOmega a').toModel] C) := by
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro κ _ M _ _ a Rra hcov hcard;
    have hane : a ≠ M.root.1 := fun h => Std.Irrefl.irrefl _ (h ▸ Rra);
    have : (M.graftOmega ⟨a, hane⟩).IsGL := graftOmega.isGL Rra;
    have : (M.graftOmega ⟨a, hane⟩).IsTree := graftOmega.isTree Rra hcov;
    by_cases hex : ∃ w : (M.graftOmega ⟨a, hane⟩).NonRoot, (M.graftOmega ⟨a, hane⟩).Redundant P w;
    . obtain ⟨w, hred⟩ := hex;
      obtain ⟨m, hm, -, rfl⟩ := graftOmega.exists_of_redundant hred;
      have hma : ¬ a.IsInConeOf m :=
        graftOmega.not_isInConeOf_of_redundant Rra hcov hm hred;
      have : Fintype (M.removeCone ⟨m, hm⟩).World := Fintype.ofFinite _;
      have : (M.removeCone ⟨m, hm⟩).IsTree := removeCone.isTree;
      have hcov' : ∀ x : (M.removeCone ⟨m, hm⟩).World,
          x.IsProperPredecessorOf ⟨a, hma⟩ → x = (M.removeCone ⟨m, hm⟩).root.1 := by
        rintro ⟨x, hx⟩ ⟨hne, hR⟩;
        exact Subtype.ext (hcov x ⟨fun h => hne (Subtype.ext h), hR⟩);
      have hlat' : (∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a) →
          ∀ x : (M.removeCone ⟨m, hm⟩).World,
            (M.removeCone ⟨m, hm⟩).root.1 ≺ x →
            IsInConeOf (M := (M.removeCone ⟨m, hm⟩).toModel) x ⟨a, hma⟩ := by
        rintro h ⟨x, hx⟩ Rrx;
        rcases h x Rrx with rfl | hax;
        . left; exact Subtype.ext rfl;
        . right; exact hax;
      obtain ⟨κ', hNe', M', hGL', hTree', a', Rra', hcov'', hlat'', hSimple', hEq'⟩ :=
        ih (Fintype.card (M.removeCone ⟨m, hm⟩).World)
          (by rw [← hcard]; exact removeCone.card_lt ⟨m, hm⟩)
          (M.removeCone ⟨m, hm⟩) ⟨a, hma⟩ Rra hcov' rfl;
      refine ⟨κ', hNe', M', hGL', hTree', a', Rra', hcov'',
        fun h => hlat'' (hlat' h), hSimple', ?_⟩;
      intro C hC;
      exact (removeCone.forces_iff (a := ⟨Sum.inl m, graftOmega.inl_ne_root hm⟩) hred hC _).symm.trans
        ((graftOmega.removeCone_root_forces_iff hm hma).trans (hEq' C hC));
    . exact ⟨κ, ‹Nonempty κ›, M, inferInstance, inferInstance, ⟨a, hane⟩, Rra, hcov,
        fun h => h, fun w hw => hex ⟨w, hw⟩, fun C _ => Iff.rfl⟩;

/--
  **Shape-exposing form**: the `P`-simplification of a `graftOmega`-shaped ω-model is
  again of the shape `M'.graftOmega a'` for a finite tree `M'` and a point `a'` covering
  its root, and lateral-cone-freeness ("being a D-model") is preserved.

  - [Bek90, Lemma 8, §4]
-/
theorem exists_simplificationUnder_omega' [DecidableEq α] {κ : Type u} [Nonempty κ] {M : RootedModel κ α}
  [hTree : M.IsFiniteGLTree] {a : M.World} (Rra : M.root.1 ≺ a)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1)
  (P : Finset α) :
  ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsFiniteGL)
    (_ : M'.IsTree) (a' : M'.NonRoot),
  M'.root.1 ≺ a'.1 ∧
  (∀ x : M'.World, x.IsProperPredecessorOf a'.1 → x = M'.root.1) ∧
  ((∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a) →
    ∀ x : M'.World, M'.root.1 ≺ x → x.IsInConeOf a'.1) ∧
  IsSimpleUnder (M'.graftOmega a') P ∧
  ∀ C : Formula α, C.atoms ⊆ P →
  ((M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1
    ⊩[(M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).toModel] C ↔
    (M'.graftOmega a').root.1 ⊩[(M'.graftOmega a').toModel] C) := by
  have : Fintype M.World := Fintype.ofFinite _;
  exact exists_simplificationUnder_omega_aux (Fintype.card M.World) M a Rra hcov rfl;

/--
  A `graftOmega`-shaped ω-model over a finite tree `M` at a point `a` covering the
  root admits a `P`-simplification.

  - [Bek90, Lemma 8, §4]
-/
theorem exists_simplificationUnder_omega [DecidableEq α] {κ : Type u} [Nonempty κ] {M : RootedModel κ α}
  [hTree : M.IsFiniteGLTree] {a : M.World} (Rra : M.root.1 ≺ a)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1)
  (P : Finset α) :
  ∃ (κ' : Type u) (_ : Nonempty κ') (M' : RootedModel κ' α) (_ : M'.IsGL),
  M'.IsTree ∧ IsSimpleUnder M' P ∧
  ∀ C : Formula α, C.atoms ⊆ P →
  ((M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1
    ⊩[(M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).toModel] C ↔ M'.root.1 ⊩[M'.toModel] C) := by
  obtain ⟨κ', hNe', M', hGL', hTree', a', Rra', hcov', -, hSimple', hEq'⟩ :=
    exists_simplificationUnder_omega' Rra hcov P;
  have := hNe'; have := hGL'; have := hTree';
  exact ⟨graftOmega.World M', inferInstance, M'.graftOmega a',
    graftOmega.isGL Rra', graftOmega.isTree Rra' hcov', hSimple', hEq'⟩;

end OmegaSimplification

end RootedModel

end
