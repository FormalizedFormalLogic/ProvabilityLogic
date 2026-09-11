module

public import ProvabilityLogic.Formula.Modalized
public import ProvabilityLogic.Kripke.DefiningFormula
public import ProvabilityLogic.Kripke.Tail

/-!
# Almost defining formulas for D-models

An *almost defining formula* is the D-model analogue of a defining formula: it pins a
`P`-simple D-model down up to a bisimulation-under-`P` whose atomic clause is waived at
the root. This file defines `RootedModel.StabilizedBisimulationUnder` and
`RootedModel.AlmostDefines`, builds the almost defining formula `Φ₀` of every D-model
over a finite GL tree with no lateral cones, and transfers the forcing of a modalized
formula from such a D-model's root to the chain of the tail model over a cone.

## References

- [Bek90, Lemma 1, Lemma 4, Lemma 9, Remark 1, Remark 2]
-/

@[expose]
public section

universe u

variable {α : Type u}

namespace RootedModel

variable [Nonempty κ]

/--
  A **stabilized bisimulation-under-`P`** between rooted models `M₁` and `M₂`: a
  bisimulation-under-`P` relating the roots, reflecting root-ness, whose atomic clause
  is waived at `M₂`'s root. Two D-models are related by one exactly when they agree on
  `P` everywhere except possibly at their minimum points.

  - [Bek90, Lemma 1]
-/
structure StabilizedBisimulationUnder
  (P : Finset α)
  {κ₁ κ₂ : Type*} [Nonempty κ₁] [Nonempty κ₂]
  (M₁ : RootedModel κ₁ α) (M₂ : RootedModel κ₂ α) where
  toRel : M₁.World → M₂.World → Prop
  root_rel : toRel M₁.root.1 M₂.root.1
  root_reflect {x₁ x₂} : toRel x₁ x₂ → (x₂ = M₂.root.1 ↔ x₁ = M₁.root.1)
  atomic {x₁ x₂ q} : q ∈ P → toRel x₁ x₂ → x₂ ≠ M₂.root.1 → (M₁.Val x₁ q ↔ M₂.Val x₂ q)
  forth {x₁ y₁ x₂} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ x₂ y₂} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁, toRel y₁ y₂ ∧ x₁ ≺ y₁

variable
  {κ κ₁ κ₂ : Type*}
  [Nonempty κ] [Nonempty κ₁] [Nonempty κ₂]
  {M₁ : RootedModel κ₁ α} {M₂ : RootedModel κ₂ α}
  {P : Finset α}

instance : CoeFun (StabilizedBisimulationUnder P M₁ M₂) (fun _ => M₁.World → M₂.World → Prop) :=
  ⟨StabilizedBisimulationUnder.toRel⟩

/--
  `A` **almost defines** the D-model `M` under `P`: the D-model analogue of
  `RootedModel.IsDefiningFormula`.

  - [Bek90, Remark 1, Remark 2]
-/
structure AlmostDefines [DecidableEq α]
  (P : Finset α) (M : RootedModel κ α) (A : Formula α) : Prop where
  atoms_subset : A.atoms ⊆ P
  modalized : A.Modalized
  root_forces : M.root.1 ⊩[_] A
  almost_unique : ∀ {κ' : Type u} [Nonempty κ'] (N : RootedModel κ' α), [N.IsFiniteGLTree] →
    ∀ c : N.World, (Rrc : N.root.1 ≺ c) →
    (∀ x : N.World, x.IsProperPredecessorOf c → x = N.root.1) →
    (N.graftOmega ⟨c, fun h => Std.Irrefl.irrefl _ (h ▸ Rrc)⟩).IsSimpleUnder P →
    (N.graftOmega ⟨c, fun h => Std.Irrefl.irrefl _ (h ▸ Rrc)⟩).root.1 ⊩[_] A →
    Nonempty (StabilizedBisimulationUnder P M
      (N.graftOmega ⟨c, fun h => Std.Irrefl.irrefl _ (h ▸ Rrc)⟩))

namespace graftOmega

open Model Model.World
open Model.World (IsInConeOf IsProperPredecessorOf)

variable {M : RootedModel κ α} {a : M.NonRoot}

-- Kept `local` rather than global: a general `Finite → Fintype` instance would create
-- diamonds, while a file-local one is found canonically everywhere it is needed here.
noncomputable local instance instFintypeConeOfIsFiniteGL {M' : RootedModel κ α}
  [M'.IsFiniteGL] {a' : M'.World} : Fintype (M'.toModel↾a') := Fintype.ofFinite _

lemma inl_forces_charFormulaUnder [DecidableEq α] [M.IsFiniteGL] [Fintype M.World]
  {x : M.World} (hx : x ≠ M.root.1) :
  (.inl x) ⊩[(M.graftOmega a).toModel] (x.charFormulaUnder P) := by
  suffices h : ∀ n (x : M.World), x.rank = n → x ≠ M.root.1 →
      (.inl x) ⊩[(M.graftOmega a).toModel] (x.charFormulaUnder P) from
    h x.rank x rfl hx;
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro x rfl hx;
    apply forces_charFormulaUnder_iff.mpr;
    and_intros;
    . exact fun q _ => Iff.rfl;
    . intro y Rxy;
      exact ⟨.inl y, Rxy, ih y.rank (rank_lt_of_rel Rxy) y rfl (fun h => not_rel_root (h ▸ Rxy))⟩;
    . rintro (y | i) Rxv;
      . have Rxy : x ≺ y := Rxv;
        exact ⟨y, Rxy, ih y.rank (rank_lt_of_rel Rxy) y rfl (fun h => not_rel_root (h ▸ Rxy))⟩;
      . exact absurd Rxv hx;

section Depth

variable [M.IsFiniteGL] [Fintype M.World]

lemma inl_forces_boxItr_bot_iff {x : M.World} (hx : x ≠ M.root.1) {k : ℕ} :
  (.inl x) ⊩[(M.graftOmega a).toModel] (□^[k]⊥) ↔ x.rank < k := by
  constructor;
  . intro h;
    by_contra hk;
    obtain ⟨y, hy⟩ := iff_le_rank.mp (Nat.le_of_not_lt hk);
    exact forces_boxItr.mp h (.inl y) (relItr_inl hy);
  . intro h;
    exact inl_forces_boxItr_bot hx (iff_rank_lt_forces_boxItr_bot.mp h);

lemma relItr_from_inr_le (Rra : M.root.1 ≺ a.1) {i n : ℕ} {w : (M.graftOmega a).World}
  (h : Model.RelItr (M := (M.graftOmega a).toModel) n (.inr i) w) :
  n ≤ i + 1 + a.1.rank := by
  induction n generalizing i w with
  | zero => omega;
  | succ n ih =>
    obtain ⟨v, Riv, hv⟩ := h;
    match v with
    | .inr j =>
      have hji : j < i := Riv;
      have := ih hv;
      omega;
    | .inl y =>
      have hya : y = a.1 ∨ a.1 ≺ y := Riv;
      have hy : y ≠ M.root.1 := by
        rcases hya with rfl | hay;
        . exact graft.ne_root_of_rel Rra;
        . exact fun h => not_rel_root (h ▸ hay);
      obtain ⟨z, rfl, hyz, -⟩ := relItr_from_inl hy hv;
      have hn : n ≤ y.rank := iff_le_rank.mpr ⟨z, hyz⟩;
      have hy_le : y.rank ≤ a.1.rank := by
        rcases hya with rfl | hay;
        . rfl;
        . exact le_of_lt (rank_lt_of_rel hay);
      omega;

lemma inr_forces_boxItr_bot_iff (Rra : M.root.1 ≺ a.1) {i k : ℕ} :
  (.inr i) ⊩[(M.graftOmega a).toModel] (□^[k]⊥) ↔ i + 1 + a.1.rank < k := by
  constructor;
  . intro h;
    by_contra hk;
    obtain ⟨t, ht⟩ := exists_rank_terminal a.1;
    have hfull : Model.RelItr (M := (M.graftOmega a).toModel) (k + (i + 1 + a.1.rank - k))
        (.inr i) (.inl t) := by
      rw [show k + (i + 1 + a.1.rank - k) = i + 1 + a.1.rank by omega];
      exact Model.relItr_comp
        (Model.relItr_comp inr_relItr_inr_zero (Model.relItr_one.mpr (Or.inl rfl)))
        (relItr_inl ht);
    obtain ⟨z, hz, -⟩ := Model.relItr_decomp hfull;
    exact forces_boxItr.mp h z hz;
  . intro h;
    apply forces_boxItr.mpr;
    intro w hw;
    exact absurd (relItr_from_inr_le Rra hw) (by omega);

omit [Fintype M.World] in
lemma root_rel_inl_of_isInConeOf (Rra : M.root.1 ≺ a.1) {x : M.World} (hx : x.IsInConeOf a.1) :
  (M.graftOmega a).root.1 ≺ (Sum.inl x : (M.graftOmega a).World) := by
  rcases hx with rfl | hax;
  . exact Rra;
  . show M.Rel M.root.1 x;
    exact IsTrans.trans _ _ _ Rra hax;

lemma exists_exact_depth (Rra : M.root.1 ≺ a.1) (m : ℕ) :
  ∃ w : (M.graftOmega a).World,
  (M.graftOmega a).root.1 ≺ w ∧
  (∀ j : ℕ, m ≤ j + a.1.rank → (Sum.inr j : (M.graftOmega a).World) ≺ w) ∧
  w ⊮[_] (□^[m]⊥) ∧
  w ⊩[_] (□^[m + 1]⊥) := by
  have hane : a.1 ≠ M.root.1 := graft.ne_root_of_rel Rra;
  rcases Nat.lt_trichotomy m a.1.rank with hm | hm | hm;
  . obtain ⟨y, Ray, hy⟩ := of_lt_rank hm;
    have hyne : y ≠ M.root.1 := fun h => not_rel_root (h ▸ Ray);
    use .inl y, root_rel_inl_of_isInConeOf Rra (Or.inr Ray), fun j _ => Or.inr Ray;
    and_intros <;>
      simp only [Model.World.NotForces, inl_forces_boxItr_bot_iff hyne] <;>
      omega;
  . subst hm;
    use .inl a.1, Rra, fun j _ => Or.inl rfl;
    and_intros <;>
      simp only [Model.World.NotForces, inl_forces_boxItr_bot_iff hane] <;>
      omega;
  . use .inr (m - a.1.rank - 1);
    and_intros;
    . show M.root.1 = M.root.1;
      rfl;
    . intro j hj;
      show m - a.1.rank - 1 < j;
      omega;
    . simp only [Model.World.NotForces, inr_forces_boxItr_bot_iff Rra];
      omega;
    . rw [inr_forces_boxItr_bot_iff Rra];
      omega;

lemma exists_exact_depth_of_ne_root (Rra : M.root.1 ≺ a.1)
  {v : (M.graftOmega a).World} (hv : v ≠ (M.graftOmega a).root.1) :
  ∃ m : ℕ,
  v ⊮[_] (□^[m]⊥) ∧
  v ⊩[_] (□^[m + 1]⊥) := by
  rcases v with x | j;
  . have hx : x ≠ M.root.1 := fun h => hv (congrArg Sum.inl h);
    use x.rank;
    and_intros <;>
      simp only [Model.World.NotForces, inl_forces_boxItr_bot_iff hx] <;> omega;
  . use j + 1 + a.1.rank;
    and_intros <;>
      simp only [Model.World.NotForces, inr_forces_boxItr_bot_iff Rra] <;> omega;

lemma exists_rel_exact_depth (Rra : M.root.1 ≺ a.1) {v : (M.graftOmega a).World} {m : ℕ}
  (hv : v ⊮[_] (□^[m + 1]⊥)) :
  ∃ w, v ≺ w ∧
  w ⊮[_] (□^[m]⊥) ∧
  w ⊩[_] (□^[m + 1]⊥) := by
  obtain ⟨w, hroot, hchain, hw₁, hw₂⟩ := exists_exact_depth Rra m;
  rcases v with x | j;
  . by_cases hx : x = M.root.1;
    . subst hx;
      exact ⟨w, hroot, hw₁, hw₂⟩;
    . replace hv : m < x.rank := by
        have := (inl_forces_boxItr_bot_iff hx (k := m + 1)).not.mp hv;
        omega;
      obtain ⟨y, Rxy, hy⟩ := of_lt_rank hv;
      have hyne : y ≠ M.root.1 := fun h => not_rel_root (h ▸ Rxy);
      use .inl y, Rxy;
      and_intros <;>
        simp only [Model.World.NotForces, inl_forces_boxItr_bot_iff hyne] <;> omega;
  . have h : m ≤ j + a.1.rank := by
      have := (inr_forces_boxItr_bot_iff Rra (i := j) (k := m + 1)).not.mp hv;
      omega;
    exact ⟨w, hchain j h, hw₁, hw₂⟩;

end Depth

section OtherModel

variable {κ' : Type*} [Nonempty κ'] {N : RootedModel κ' α} {c : N.NonRoot} [DecidableEq α]
  [M.IsFiniteGL] [Fintype M.World]

/-- The formula `Φ₀` of the D-model case, with `N = a.rank`.

- [Bek90, Remark 1] -/
noncomputable abbrev phi0 (M : RootedModel κ α) [M.IsFiniteGL] [Fintype M.World] (a : M.World)
  (P : Finset α) : Formula α :=
  □(∼(□^[a.rank + 1]⊥) 🡒 ((◇(a.charFormulaUnder P)) ⋏ a.valuationConj P))
    ⋏ □((□^[a.rank + 1]⊥) 🡒 ⋁(Finset.univ.image fun y : M.toModel↾a => y.1.charFormulaUnder P))

/-- - [Bek90, Lemma 9.1] -/
lemma forces_dia_and_valuationConj_of_not_forces_boxItr
  (hAroot : (N.graftOmega c).root.1 ⊩[(N.graftOmega c).toModel] phi0 M a.1 P)
  {w : (N.graftOmega c).World} (Rrw : (N.graftOmega c).root.1 ≺ w)
  (hw : w ⊮[(N.graftOmega c).toModel] (□^[a.1.rank + 1]⊥)) :
  w ⊩[(N.graftOmega c).toModel] (◇(a.1.charFormulaUnder P) ⋏ a.1.valuationConj P) :=
  (forces_and.mp hAroot).1 w Rrw (forces_neg.mpr hw)

/-- - [Bek90, Lemma 9.1] -/
lemma forces_fdisj_charFormulaUnder_of_forces_boxItr
  (hAroot : (N.graftOmega c).root.1 ⊩[(N.graftOmega c).toModel] phi0 M a.1 P)
  {w : (N.graftOmega c).World} (Rrw : (N.graftOmega c).root.1 ≺ w)
  (hw : w ⊩[(N.graftOmega c).toModel] (□^[a.1.rank + 1]⊥)) :
  w ⊩[(N.graftOmega c).toModel]
    (⋁(Finset.univ.image fun y : M.toModel↾a.1 => y.1.charFormulaUnder P)) :=
  (forces_and.mp hAroot).2 w Rrw hw

/-- - [Bek90, Lemma 9] -/
lemma val_eq_of_forces_phi0 (hAroot : (N.graftOmega c).root.1 ⊩[(N.graftOmega c).toModel] phi0 M a.1 P) {q : α}
  (hq : q ∈ P) : M.Val a.1 q ↔ N.Val c.1 q := by
  have Rrw : (N.graftOmega c).root.1 ≺ (Sum.inr a.1.rank : (N.graftOmega c).World) := by
    show (N.root.1 = N.root.1);
    rfl;
  have hpath : Model.RelItr (M := (N.graftOmega c).toModel) (a.1.rank + 1)
      (Sum.inr a.1.rank) (Sum.inl c.1) :=
    Model.relItr_comp (graftOmega.inr_relItr_inr_zero (M := N) (a := c) (n := a.1.rank))
      (Model.relItr_one.mpr (Or.inl rfl));
  have hw : (Sum.inr a.1.rank : (N.graftOmega c).World) ⊮[(N.graftOmega c).toModel]
      (□^[a.1.rank + 1]⊥) :=
    fun h => forces_boxItr.mp h (Sum.inl c.1) hpath;
  have h := forces_dia_and_valuationConj_of_not_forces_boxItr hAroot Rrw hw;
  exact forces_valuationConj.mp (forces_and.mp h).2 q hq;

/-- - [Bek90, Lemma 9.1] -/
lemma exists_forces_charFormulaUnder_of_not_forces_boxItr [N.IsFiniteGL] [Fintype N.World]
  (Rrc : N.root.1 ≺ c.1)
  (hAroot : (N.graftOmega c).root.1 ⊩[(N.graftOmega c).toModel] phi0 M a.1 P)
  {v : (N.graftOmega c).World} (Rrv : (N.graftOmega c).root.1 ≺ v)
  (hv : v ⊮[(N.graftOmega c).toModel] (□^[a.1.rank + 1]⊥))
  {x : M.World} (hx : x.IsInConeOf a.1) :
  ∃ w, v ≺ w ∧ w ⊩[(N.graftOmega c).toModel] (x.charFormulaUnder P) := by
  have hGL : (N.graftOmega c).IsGL := isGL Rrc;
  have := hGL.toIsTrans;
  obtain ⟨w₀, Rvw₀, hw₀⟩ := forces_dia.mp
    (forces_and.mp (forces_dia_and_valuationConj_of_not_forces_boxItr hAroot Rrv hv)).1;
  rcases hx with rfl | hax;
  . exact ⟨w₀, Rvw₀, hw₀⟩;
  . obtain ⟨w, Rw₀w, hw⟩ := (forces_charFormulaUnder_iff.mp hw₀).2.1 x hax;
    exact ⟨w, IsTrans.trans _ _ _ Rvw₀ Rw₀w, hw⟩;

lemma root_exists_forces_charFormulaUnder [N.IsFiniteGL] [Fintype N.World]
  (Rrc : N.root.1 ≺ c.1)
  (hAroot : (N.graftOmega c).root.1 ⊩[(N.graftOmega c).toModel] phi0 M a.1 P)
  {x : M.World} (hx : x.IsInConeOf a.1) :
  ∃ w, (N.graftOmega c).root.1 ≺ w ∧
  w ⊩[(N.graftOmega c).toModel] (x.charFormulaUnder P) := by
  have hGL : (N.graftOmega c).IsGL := isGL Rrc;
  have := hGL.toIsTrans;
  have Rrv : (N.graftOmega c).root.1 ≺ (Sum.inr a.1.rank : (N.graftOmega c).World) := by
    show N.root.1 = N.root.1;
    rfl;
  have hv : (Sum.inr a.1.rank : (N.graftOmega c).World) ⊮[(N.graftOmega c).toModel]
      (□^[a.1.rank + 1]⊥) :=
    (inr_forces_boxItr_bot_iff Rrc).not.mpr (by omega);
  obtain ⟨w, Rvw, hw⟩ := exists_forces_charFormulaUnder_of_not_forces_boxItr Rrc hAroot Rrv hv hx;
  exact ⟨w, IsTrans.trans _ _ _ Rrv Rvw, hw⟩;

end OtherModel

/--
  Every D-model `M.graftOmega a` over a finite GL tree `M` with no lateral cones
  (`hlat`) admits an almost defining formula. The general case with lateral cones is
  not needed here: the D-model countermodel of `LogicD` has none, and the shape is
  preserved by `P`-simplification.

  - [Bek90, Lemma 9, Lemma 1]
-/
theorem exists_almostDefiningFormula [DecidableEq α] [M.IsFiniteGLTree] [Fintype M.World]
  (Rra : M.root.1 ≺ a.1)
  (hlat : ∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a.1) :
  ∃ A : Formula α, AlmostDefines P (M.graftOmega a) A := by
  classical
  have hane : a.1 ≠ M.root.1 := graft.ne_root_of_rel Rra;
  have hbot : ∀ n : ℕ, ((□^[n]⊥ : Formula α)).atoms = ∅ := by
    intro n; induction n <;> simp_all [Formula.boxItr, Formula.atoms];
  use phi0 M a.1 P;
  constructor;
  case atoms_subset =>
    have hΓ :
        (⋁(Finset.univ.image fun y : M.toModel↾a.1 => y.1.charFormulaUnder P)).atoms ⊆ P := by
      apply subset_trans (FormulaFinset.atoms_disj_subset _);
      intro q hq;
      simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at hq;
      obtain ⟨A, ⟨y, -, rfl⟩, hqA⟩ := hq;
      exact atoms_charFormulaUnder hqA;
    intro q hq;
    simp only [Formula.atoms, hbot,
      Finset.empty_union, Finset.union_empty, Finset.mem_union] at hq;
    rcases hq with (hq | hq) | hq;
    . exact atoms_charFormulaUnder hq;
    . exact atoms_valuationConj hq;
    . exact hΓ hq;
  case modalized =>
    intro q;
    exact ⟨⟨trivial, trivial, trivial⟩, trivial⟩;
  case root_forces =>
    apply forces_and.mpr;
    and_intros;
    . rintro (x | i) Rrw hw;
      . exfalso;
        have Rrx : M.root.1 ≺ x := Rrw;
        apply forces_neg.mp hw;
        apply inl_forces_boxItr_bot (fun h => not_rel_root (h ▸ Rrx));
        apply iff_rank_lt_forces_boxItr_bot.mp;
        rcases hlat x Rrw with rfl | hax;
        . omega;
        . have := rank_lt_of_rel hax; omega;
      . apply forces_and.mpr;
        and_intros;
        . apply forces_dia.mpr;
          exact ⟨.inl a.1, Or.inl rfl, inl_forces_charFormulaUnder hane⟩;
        . apply forces_valuationConj.mpr;
          intro q _;
          exact Iff.rfl;
    . rintro (x | i) Rrw hw;
      . have Rrx : M.root.1 ≺ x := Rrw;
        apply forces_fdisj.mpr;
        use x.charFormulaUnder P;
        and_intros;
        . exact Finset.mem_image.mpr ⟨⟨x, hlat x Rrx⟩, Finset.mem_univ _, rfl⟩;
        . exact inl_forces_charFormulaUnder (fun h => not_rel_root (h ▸ Rrx));
      . exfalso;
        obtain ⟨t, ht⟩ := exists_rank_terminal a.1;
        exact forces_boxItr.mp hw (.inl t) ⟨.inl a.1, Or.inl rfl, relItr_inl ht⟩;
  case almost_unique =>
    intro κ' _ N _ c Rrc _ _ hAroot;
    have : Fintype N.World := Fintype.ofFinite _;
    have hcne : c ≠ N.root.1 := fun h => not_rel_root (h ▸ Rrc);
    set c' : N.NonRoot := ⟨c, hcne⟩ with hc'_def;
    have hGL : (N.graftOmega c').IsGL := isGL Rrc;
    have := hGL.toIsTrans;
    have : Std.Irrefl (N.graftOmega c').Rel :=
      @ConverseWellFounded.irrefl _ _ hGL.toIsConverseWellFounded;
    exact ⟨{
      toRel := fun u v =>
        (u = (M.graftOmega a).root.1 ∧ v = (N.graftOmega c').root.1) ∨
        (u ≠ (M.graftOmega a).root.1 ∧ v ≠ (N.graftOmega c').root.1 ∧
          match u with
          | .inl x => v ⊩[(N.graftOmega c').toModel] (x.charFormulaUnder P)
          | .inr i =>
            v ⊮[(N.graftOmega c').toModel] (□^[i + 1 + a.1.rank]⊥) ∧
            v ⊩[(N.graftOmega c').toModel] (□^[i + 1 + a.1.rank + 1]⊥))
      root_rel := Or.inl ⟨rfl, rfl⟩
      root_reflect := by
        rintro u v (⟨rfl, rfl⟩ | ⟨hu, hv, -⟩);
        . exact iff_of_true rfl rfl;
        . exact iff_of_false hv hu;
      atomic := by
        rintro u v q hq (⟨rfl, rfl⟩ | ⟨hu, hv, hC⟩) hvne;
        . exact absurd rfl hvne;
        . rcases u with x | i;
          . exact (forces_charFormulaUnder_iff.mp hC).1 q hq;
          . have hdeep : v ⊮[(N.graftOmega c').toModel] (□^[a.1.rank + 1]⊥) :=
              fun h => hC.1 (forces_boxItr_bot_mono (by omega) h);
            have h := forces_dia_and_valuationConj_of_not_forces_boxItr hAroot
              ((N.graftOmega c').root.2 v hv) hdeep;
            exact forces_valuationConj.mp (forces_and.mp h).2 q hq;
      forth := by
        rintro u u' v (⟨rfl, rfl⟩ | ⟨hu, hv, hC⟩) Ruu';
        . rcases u' with x | i;
          . have Rrx : M.root.1 ≺ x := Ruu';
            obtain ⟨w, Rrw, hw⟩ := root_exists_forces_charFormulaUnder Rrc hAroot (hlat x Rrx);
            exact ⟨w, Or.inr ⟨inl_ne_root (fun h => not_rel_root (h ▸ Rrx)),
              fun h => not_rel_root (h ▸ Rrw), hw⟩, Rrw⟩;
          . obtain ⟨w, Rrw, -, hw₁, hw₂⟩ := exists_exact_depth (a := c') Rrc (i + 1 + a.1.rank);
            exact ⟨w, Or.inr ⟨inr_ne_root, fun h => not_rel_root (h ▸ Rrw), hw₁, hw₂⟩, Rrw⟩;
        . rcases u with x | i;
          . rcases u' with y | j;
            . have Rxy : x ≺ y := Ruu';
              obtain ⟨w, Rvw, hw⟩ := (forces_charFormulaUnder_iff.mp hC).2.1 y Rxy;
              exact ⟨w, Or.inr ⟨inl_ne_root (fun h => not_rel_root (h ▸ Rxy)),
                fun h => not_rel_root (h ▸ Rvw), hw⟩, Rvw⟩;
            . exact absurd (show x = M.root.1 from Ruu') (fun h => hu (congrArg Sum.inl h));
          . rcases u' with y | j;
            . have hy : y.IsInConeOf a.1 := Ruu';
              have hyne : y ≠ M.root.1 := by
                rcases hy with rfl | hay;
                . exact hane;
                . exact fun h => not_rel_root (h ▸ hay);
              have hdeep : v ⊮[(N.graftOmega c').toModel] (□^[a.1.rank + 1]⊥) :=
                fun h => hC.1 (forces_boxItr_bot_mono (by omega) h);
              obtain ⟨w, Rvw, hw⟩ := exists_forces_charFormulaUnder_of_not_forces_boxItr
                Rrc hAroot ((N.graftOmega c').root.2 v hv) hdeep hy;
              exact ⟨w, Or.inr ⟨inl_ne_root hyne, fun h => not_rel_root (h ▸ Rvw), hw⟩, Rvw⟩;
            . have hji : j < i := Ruu';
              obtain ⟨w, Rvw, hw₁, hw₂⟩ := exists_rel_exact_depth Rrc (m := j + 1 + a.1.rank)
                (fun h => hC.1 (forces_boxItr_bot_mono (by omega) h));
              exact ⟨w, Or.inr ⟨inr_ne_root, fun h => not_rel_root (h ▸ Rvw), hw₁, hw₂⟩, Rvw⟩;
      back := by
        rintro u v v' (⟨rfl, rfl⟩ | ⟨hu, hv, hC⟩) Rvv';
        . by_cases hsh : v' ⊩[(N.graftOmega c').toModel] (□^[a.1.rank + 1]⊥);
          . obtain ⟨B, hB, hv'B⟩ :=
              forces_fdisj.mp (forces_fdisj_charFormulaUnder_of_forces_boxItr hAroot Rvv' hsh);
            obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hB;
            have htne : t.1 ≠ M.root.1 := by
              intro h;
              have h2 := t.2;
              rw [h] at h2;
              exact not_isInConeOf_root_of_ne hane h2;
            exact ⟨.inl t.1, Or.inr ⟨inl_ne_root htne, fun h => not_rel_root (h ▸ Rvv'), hv'B⟩,
              root_rel_inl_of_isInConeOf Rra t.2⟩;
          . obtain ⟨m, hm₁, hm₂⟩ :=
              exists_exact_depth_of_ne_root (a := c') (v := v') Rrc (fun h => not_rel_root (h ▸ Rvv'));
            have hge : a.1.rank + 1 ≤ m := by
              by_contra hlt;
              exact hsh (forces_boxItr_bot_mono (by omega) hm₂);
            exact ⟨.inr (m - a.1.rank - 1),
              Or.inr ⟨inr_ne_root, fun h => not_rel_root (h ▸ Rvv'),
                by rw [show m - a.1.rank - 1 + 1 + a.1.rank = m by omega]; exact hm₁,
                by rw [show m - a.1.rank - 1 + 1 + a.1.rank + 1 = m + 1 by omega]; exact hm₂⟩,
              show M.root.1 = M.root.1 from rfl⟩;
        . have hv'ne : v' ≠ (N.graftOmega c').root.1 := fun h => not_rel_root (h ▸ Rvv');
          rcases u with x | i;
          . obtain ⟨y, Rxy, hy⟩ := (forces_charFormulaUnder_iff.mp hC).2.2 v' Rvv';
            exact ⟨.inl y, Or.inr ⟨inl_ne_root (fun h => not_rel_root (h ▸ Rxy)), hv'ne, hy⟩, Rxy⟩;
          . by_cases hsh : v' ⊩[(N.graftOmega c').toModel] (□^[a.1.rank + 1]⊥);
            . obtain ⟨B, hB, hv'B⟩ := forces_fdisj.mp
                (forces_fdisj_charFormulaUnder_of_forces_boxItr hAroot
                  ((N.graftOmega c').root.2 v' hv'ne) hsh);
              obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hB;
              have htne : t.1 ≠ M.root.1 := by
                intro h;
                have h2 := t.2;
                rw [h] at h2;
                exact not_isInConeOf_root_of_ne hane h2;
              exact ⟨.inl t.1, Or.inr ⟨inl_ne_root htne, hv'ne, hv'B⟩,
                show t.1 = a.1 ∨ a.1 ≺ t.1 from t.2⟩;
            . obtain ⟨m, hm₁, hm₂⟩ := exists_exact_depth_of_ne_root (a := c') Rrc hv'ne;
              have hge : a.1.rank + 1 ≤ m := by
                by_contra hlt;
                exact hsh (forces_boxItr_bot_mono (by omega) hm₂);
              have hlt : m < i + 1 + a.1.rank := by
                by_contra hle;
                have hstep : v' ⊩[(N.graftOmega c').toModel]
                    (□^[i + 1 + a.1.rank]⊥) := by
                  apply forces_boxItr.mpr;
                  intro z hz;
                  exact forces_boxItr.mp hC.2 z ⟨v', Rvv', hz⟩;
                exact hm₁ (forces_boxItr_bot_mono (by omega) hstep);
              exact ⟨.inr (m - a.1.rank - 1),
                Or.inr ⟨inr_ne_root, hv'ne,
                  by rw [show m - a.1.rank - 1 + 1 + a.1.rank = m by omega]; exact hm₁,
                  by rw [show m - a.1.rank - 1 + 1 + a.1.rank + 1 = m + 1 by omega]; exact hm₂⟩,
                show m - a.1.rank - 1 < i by omega⟩;
    }⟩;

section ConeTail

/-- The tail model over the cone of `a` in `M`: the stabilization of the D-model
`M.graftOmega a`. -/
abbrev coneTail (M : RootedModel κ α) (a : M.World) :
  RootedModel (Model.toTail.World (Model.toRootedModel M.toModel a).toModel) α :=
  (Model.toRootedModel M.toModel a).toModel.toTail (Model.toRootedModel M.toModel a).root.1

variable [M.IsFiniteGL] [Fintype M.World]

/-- The chain-and-cone part of the D-model `M.graftOmega a` is bisimilar to the tail
model over the cone of `a`. -/
def coneTailBisimulation (M : RootedModel κ α) [M.IsFiniteGL] (a : M.World)
  (Rra : M.root.1 ≺ a) :
  (M.graftOmega ⟨a, fun h => not_rel_root (h ▸ Rra)⟩).toModel ⇄ (coneTail M a).toModel where
  toRel u v :=
    match u, v with
    | .inl x, .inl y => x = y.1
    | .inr i, .inr j => j = (i : ℕ∞)
    | .inl _, .inr _ => False
    | .inr _, .inl _ => False
  atomic := by rintro (x | i) (y | j) q h <;> grind;
  forth := by
    rintro (x | i) (u | i') (y | j) h Rxu;
    . subst h;
      exact ⟨.inl ⟨u, isInConeOf_of_isInConeOf y.2 Rxu⟩, rfl, Rxu⟩;
    . exact h.elim;
    . subst h;
      exfalso;
      have hroot : (M.root.1).IsInConeOf a := by
        have hy : y.1 = M.root.1 := Rxu;
        exact hy ▸ y.2;
      exact not_isInConeOf_root_of_ne (fun h => not_rel_root (h ▸ Rra)) hroot;
    . exact h.elim;
    . exact h.elim;
    . exact ⟨.inl ⟨u, Rxu⟩, rfl, trivial⟩;
    . exact h.elim;
    . subst h;
      exact ⟨.inr (i' : ℕ∞), rfl, show (i' : ℕ∞) < (i : ℕ∞) by exact_mod_cast Rxu⟩;
  back := by
    rintro (x | i) (y | j) (v | j') h Rv;
    . subst h;
      exact ⟨.inl v.1, rfl, Rv⟩;
    . exact Rv.elim;
    . exact h.elim;
    . exact h.elim;
    . exact h.elim;
    . exact h.elim;
    . subst h;
      exact ⟨.inl v.1, rfl, v.2⟩;
    . subst h;
      have hj' : j' ≠ (⊤ : ℕ∞) := ne_top_of_lt (show j' < (i : ℕ∞) from Rv);
      obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hj';
      have hmi : (m : ℕ∞) < (i : ℕ∞) := Rv;
      exact ⟨.inr m, rfl, by exact_mod_cast hmi⟩;

omit [Fintype M.World] in
lemma coneTail_chainPoint_modal_equivalent (Rra : M.root.1 ≺ a.1) (i : ℕ) :
  ModalEquivalent (M₁ := (M.graftOmega a).toModel) (M₂ := (coneTail M a.1).toModel)
    (Sum.inr i) (Sum.inr (i : ℕ∞)) :=
  modal_equivalent_of_bisimilar (coneTailBisimulation M a.1 Rra)
    (show (coneTailBisimulation M a.1 Rra).toRel (Sum.inr i) (Sum.inr (i : ℕ∞)) from rfl)

omit [Fintype M.World] in
lemma coneTail_embed_modal_equivalent (Rra : M.root.1 ≺ a.1) (y : M.toModel↾a.1) :
  ModalEquivalent (M₁ := (M.graftOmega a).toModel) (M₂ := (coneTail M a.1).toModel)
    (Sum.inl y.1) (Sum.inl y) :=
  modal_equivalent_of_bisimilar (coneTailBisimulation M a.1 Rra)
    (show (coneTailBisimulation M a.1 Rra).toRel (Sum.inl y.1) (Sum.inl y) from rfl)

omit [Fintype M.World] in
/--
  **Stabilization transfer for modalized formulas**: for a D-model `M.graftOmega a`
  with no lateral cones, a modalized formula is forced at the root exactly when it is
  eventually forced along the chain of the tail model over the cone of `a`.

  - [Bek90, Lemma 4]
-/
theorem eventually_coneTail_chainPoint_forces_iff_of_modalized
  (Rra : M.root.1 ≺ a) (hlat : ∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a)
  {C : Formula α} (hC : C.Modalized) :
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
  (Sum.inr (n : ℕ∞) ⊩[(coneTail M a).toModel] C ↔
    (M.graftOmega a).root.1 ⊩[(M.graftOmega a).toModel] C) := by
  induction C with
  | atom q => exact (hC q rfl).elim;
  | bot => exact ⟨0, fun n _ => Iff.rfl⟩;
  | imp A B ihA ihB =>
    obtain ⟨k₁, h₁⟩ := ihA (fun q => (hC q).1);
    obtain ⟨k₂, h₂⟩ := ihB (fun q => (hC q).2);
    use max k₁ k₂;
    intro n hn;
    have hA := h₁ n (le_trans (le_max_left _ _) hn);
    have hB := h₂ n (le_trans (le_max_right _ _) hn);
    constructor;
    . intro h ha; exact hB.mp (h (hA.mpr ha));
    . intro h ha; exact hB.mpr (h (hA.mp ha));
  | box A ihA =>
    by_cases h : (M.graftOmega a).root.1 ⊩[(M.graftOmega a).toModel] (□A);
    . use 0;
      intro n _;
      refine iff_of_true ?_ h;
      rintro (y | j) Rny;
      . apply (coneTail_embed_modal_equivalent Rra y).mp;
        exact h (Sum.inl y.1) (root_rel_inl_of_isInConeOf Rra y.2);
      . have hj : j ≠ (⊤ : ℕ∞) :=
          ne_top_of_lt (show j < (n : ℕ∞) from Rny);
        obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hj;
        apply (coneTail_chainPoint_modal_equivalent Rra m).mp;
        exact h (Sum.inr m) rfl;
    . obtain ⟨w, Rrw, hwA⟩ := by
        have := forces_box.not.mp h;
        push Not at this;
        exact this;
      rcases w with x | i;
      . have hx : x.IsInConeOf a := hlat x Rrw;
        use 0;
        intro n _;
        refine iff_of_false ?_ h;
        intro hbox;
        apply hwA;
        apply (coneTail_embed_modal_equivalent Rra ⟨x, hx⟩).mpr;
        exact hbox (Sum.inl ⟨x, hx⟩) trivial;
      . use i + 1;
        intro n hn;
        refine iff_of_false ?_ h;
        intro hbox;
        apply hwA;
        apply (coneTail_chainPoint_modal_equivalent Rra i).mpr;
        apply hbox (Sum.inr (i : ℕ∞));
        show (i : ℕ∞) < (n : ℕ∞);
        exact_mod_cast hn;

end ConeTail

end graftOmega

end RootedModel

end
