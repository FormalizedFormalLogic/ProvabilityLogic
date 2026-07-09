module

public import SeqPL.Kripke.DefiningFormula
public import SeqPL.Kripke.Tail
public import SeqPL.Logic.D.NotCIP

/-!
# Almost defining formulas for D-models (Bek90 §4, Lemma 9)

This file states **Lemma 9 of [Bek90] §4** for the D-model case, together with the
supporting notions:

* `RootedModel.StabilizedBisimulationUnder`: a bisimulation-under-`P` whose atomic
  clause is waived at the root of the second model. This formalizes [Bek90]'s
  "the *stabilizations* are `p̄`-isomorphic": two D-models agree everywhere except
  possibly in the valuation of their minimum points;
* `RootedModel.AlmostDefines`: the *almost defining formula* property for D-models
  (Remarks 1-2 of [Bek90] §4, p.265), the D-model analogue of
  `RootedModel.IsDefiningFormula`;
* `RootedModel.graftOmega.phi0` and the lemmas around it
  (`forces_dia_and_valuationConj_of_not_forces_boxItr`,
  `forces_fdisj_charFormulaUnder_of_forces_boxItr`, `val_eq_of_forces_phi0`): the
  D-model form of `Φ₀` (Remark 1) together with the direct consequences of it being
  forced at the root of *another* `P`-simple D-model-shaped ω-model -- the D-model
  specialization of Lemma 9.1 (p.264), which in this case needs no auxiliary
  "largest shallow-enough predecessor" construction since there are no lateral cones
  to separate `a` from;
* `RootedModel.graftOmega.exists_almostDefiningFormula` (**Lemma 9 + Remarks 1-2
  of [Bek90] §4**): every `P`-simple D-model has an *almost defining* formula `Φ₀`.
  The uniqueness clause (`AlmostDefines.almost_unique`, Remark 2) is proved by an
  explicit semantic bisimulation instead of the paper's `P`-isomorphism: embedded
  points are related through their characteristic formulas, chain points through
  their *exact depth* (`exists_exact_depth` and the surrounding lemmas: forcing
  `□^[m+1]⊥` while refuting `□^[m]⊥`). Since a bisimulation -- unlike an isomorphism
  -- may relate chain points of the two ω-models of matching depth regardless of
  where the respective base trees end, neither Lemma 9.2 (the branch-point depth
  bound) nor the `P`-simplicity of the other model is needed, mirroring how Lemma 7
  (`RootedModel.exists_isDefiningFormula`) sheds its simpleness hypothesis under the
  bisimulation formulation;
* the "stabilization" transfer needed on the `LogicS` side (Lemma 4 of [Bek90] §4 in
  the form needed here): a modalized formula forced at the root of a D-model
  `M.graftOmega a` is eventually forced along the chain of the *tail model* over
  the cone of `a` (`RootedModel.graftOmega.eventually_coneTail_chainPoint_forces_iff_of_modalized`).
-/

@[expose]
public section

universe u

variable {α : Type u}

namespace RootedModel

variable [Nonempty κ]

/--
  A **stabilized bisimulation-under-`P`** between rooted models `M₁` and `M₂`: a
  bisimulation-under-`P` relating the roots, reflecting root-ness, whose atomic
  clause is waived at `M₂`'s root. This formalizes the notion that "the
  stabilizations of the D-models are `p̄`-isomorphic": the *stabilization*
  of a D-model replaces the (free) valuation of its minimum point by the stable
  tail valuation, so two D-models with `p̄`-isomorphic stabilizations agree on `p̄`
  everywhere except possibly at their minimum points (= roots).

  - [Bek90, Lemma 1 (§5, proof)]
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
  `A` **almost defines** the D-model `M` under `P`: `A` depends only on `P`, is
  modalized, is true at `M`'s root, and any other `P`-simple D-model-shaped
  ω-model forcing `A` admits a stabilized-bisimulation-under-`P` back from `M`.
  The analogue of `RootedModel.IsDefiningFormula` for D-models.

  - [Bek90, Remarks 1-2 (p.265)]
-/
structure AlmostDefines [DecidableEq α]
  (P : Finset α) (M : RootedModel κ α) (A : Formula α) : Prop where
  atoms_subset : A.atoms ⊆ P
  modalized : A.Modalized
  root_forces : M.root.1 ⊩ A
  almost_unique : ∀ {κ' : Type u} [Nonempty κ'] (N : RootedModel κ' α), [N.IsFiniteGLTree] →
    ∀ c : N.World, N.root.1 ≺ c →
    (∀ x : N.World, x.IsProperPredecessorOf c → x = N.root.1) →
    (N.graftOmega c).IsSimpleUnder P →
    (N.graftOmega c).root.1 ⊩ A →
    Nonempty (StabilizedBisimulationUnder P M (N.graftOmega c))

namespace graftOmega

open Model Model.World
open Model.World (IsInConeOf IsProperPredecessorOf Forces)

variable {M : RootedModel κ α} {a : M.World}

/--
  A classically-chosen `Fintype` instance for any finite GL-model's worlds, derived
  from the `Finite M.World` instance that `Model.IsFiniteGL` already provides. Kept
  `local` (not a global instance) to avoid the diamond issues a general
  `Finite → Fintype` instance would cause; within this file it lets declarations that
  need `Fintype M.World` (e.g. for `Model.World.charFormulaUnder`'s `Finset.univ`)
  take just `[M.IsFiniteGL]`, with the same canonical instance found everywhere it's
  needed (so no mismatch between separately-derived `Fintype` instances arises).
-/
noncomputable local instance instFintypeWorldOfIsFiniteGL {M' : RootedModel κ α}
  [M'.IsFiniteGL] : Fintype M'.World := Fintype.ofFinite _

/-- Likewise for the `Fintype` instance of a cone, derived from `Finite (Cone M a)`
(itself automatic from `Finite M.World`, see `Model.instFiniteCone` in
`SeqPL/Kripke/Cone.lean`). -/
noncomputable local instance instFintypeConeOfIsFiniteGL {M' : RootedModel κ α}
  [M'.IsFiniteGL] {a' : M'.World} : Fintype (M'.toModel↾a') := Fintype.ofFinite _

/-- A non-root world of `M` forces its own characteristic formula as an `inl` world
of the ω-grafted model. -/
lemma inl_forces_charFormulaUnder [DecidableEq α] [M.IsFiniteGL]
  {x : M.World} (hx : x ≠ M.root.1) :
  Forces (M := (M.graftOmega a).toModel) (.inl x) (x.charFormulaUnder P) := by
  suffices h : ∀ n (x : M.World), x.rank = n → x ≠ M.root.1 →
      Forces (M := (M.graftOmega a).toModel) (.inl x) (x.charFormulaUnder P) from
    h x.rank x rfl hx;
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro x rfl hx;
    apply forces_charFormulaUnder_iff.mpr;
    refine ⟨fun q _ => Iff.rfl, ?_, ?_⟩;
    . intro y Rxy;
      exact ⟨.inl y, Rxy, ih y.rank (rank_lt_of_rel Rxy) y rfl (fun h => not_rel_root (h ▸ Rxy))⟩;
    . rintro (y | i) Rxv;
      . have Rxy : x ≺ y := Rxv;
        exact ⟨y, Rxy, ih y.rank (rank_lt_of_rel Rxy) y rfl (fun h => not_rel_root (h ▸ Rxy))⟩;
      . exact absurd Rxv hx;

section Depth

variable [M.IsFiniteGL]

/-- Depth characterization of embedded non-root points of the ω-grafted model:
`Sum.inl x` forces `□^[k]⊥` iff `x.rank < k`. -/
lemma inl_forces_boxItr_bot_iff {x : M.World} (hx : x ≠ M.root.1) {k : ℕ} :
  Forces (M := (M.graftOmega a).toModel) (.inl x) (□^[k]⊥) ↔ x.rank < k := by
  constructor;
  . intro h;
    by_contra hk;
    obtain ⟨y, hy⟩ := iff_le_rank.mp (Nat.le_of_not_lt hk);
    exact forces_boxItr.mp h (.inl y) (relItr_inl hy);
  . intro h;
    exact inl_forces_boxItr_bot hx (iff_rank_lt_forces_boxItr_bot.mp h);

/-- The length of a chain starting from a chain point of the ω-grafted model is
bounded by `i + 1 + a.rank`. The ω-analogue of `graft.relItr_from_inr_le`. -/
lemma relItr_from_inr_le (Rra : M.root.1 ≺ a) {i n : ℕ} {w : (M.graftOmega a).World}
  (h : Model.RelItr (M := (M.graftOmega a).toModel) n (.inr i) w) :
  n ≤ i + 1 + a.rank := by
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
      have hya : y = a ∨ a ≺ y := Riv;
      have hy : y ≠ M.root.1 := by
        rcases hya with rfl | hay;
        . exact graft.ne_root_of_rel Rra;
        . exact fun h => not_rel_root (h ▸ hay);
      obtain ⟨z, rfl, hyz, -⟩ := relItr_from_inl hy hv;
      have hn : n ≤ y.rank := iff_le_rank.mpr ⟨z, hyz⟩;
      have hy_le : y.rank ≤ a.rank := by
        rcases hya with rfl | hay;
        . rfl;
        . exact le_of_lt (rank_lt_of_rel hay);
      omega;

/-- Depth characterization of chain points of the ω-grafted model: `chainPoint i`
forces `□^[k]⊥` iff `i + 1 + a.rank < k`. -/
lemma inr_forces_boxItr_bot_iff (Rra : M.root.1 ≺ a) {i k : ℕ} :
  Forces (M := (M.graftOmega a).toModel) (.inr i) (□^[k]⊥) ↔ i + 1 + a.rank < k := by
  constructor;
  . intro h;
    by_contra hk;
    -- the full chain `chainPoint i ≺ ⋯ ≺ chainPoint 0 ≺ a ≺ ⋯ ≺ (rank-terminal)` has
    -- length `i + 1 + a.rank ≥ k`, so `chainPoint i` refutes `□^[k]⊥`
    obtain ⟨t, ht⟩ := exists_rank_terminal a;
    have hfull : Model.RelItr (M := (M.graftOmega a).toModel) (k + (i + 1 + a.rank - k))
        (.inr i) (.inl t) := by
      rw [show k + (i + 1 + a.rank - k) = i + 1 + a.rank by omega];
      exact Model.relItr_comp
        (Model.relItr_comp inr_relItr_inr_zero (Model.relItr_one.mpr (Or.inl rfl)))
        (relItr_inl ht);
    obtain ⟨z, hz, -⟩ := Model.relItr_decomp hfull;
    exact forces_boxItr.mp h z hz;
  . intro h;
    apply forces_boxItr.mpr;
    intro w hw;
    exact absurd (relItr_from_inr_le Rra hw) (by omega);

/-- Every cone point of `a` lies above the root of the D-model. -/
lemma root_rel_inl_of_isInConeOf (Rra : M.root.1 ≺ a) {x : M.World} (hx : x.IsInConeOf a) :
  (M.graftOmega a).root.1 ≺ (Sum.inl x : (M.graftOmega a).World) := by
  rcases hx with rfl | hax;
  . exact Rra;
  . show M.Rel M.root.1 x;
    exact IsTrans.trans _ _ _ Rra hax;

/--
  The chain-and-cone part of the ω-grafted model realizes every exact depth `m`:
  some point refuting `□^[m]⊥` but forcing `□^[m+1]⊥` lies above the root and above
  every chain point `chainPoint j` with `m ≤ j + a.rank`.
-/
lemma exists_exact_depth (Rra : M.root.1 ≺ a) (m : ℕ) :
  ∃ w : (M.graftOmega a).World,
  (M.graftOmega a).root.1 ≺ w ∧
  (∀ j : ℕ, m ≤ j + a.rank → (Sum.inr j : (M.graftOmega a).World) ≺ w) ∧
  ¬ Forces (M := (M.graftOmega a).toModel) w (□^[m]⊥) ∧
  Forces (M := (M.graftOmega a).toModel) w (□^[m + 1]⊥) := by
  have hane : a ≠ M.root.1 := graft.ne_root_of_rel Rra;
  -- for `m ≤ a.rank` the witness lies in the cone of `a`, otherwise it is
  -- `chainPoint (m - a.rank - 1)`
  rcases Nat.lt_trichotomy m a.rank with hm | hm | hm;
  . obtain ⟨y, Ray, hy⟩ := of_lt_rank hm;
    have hyne : y ≠ M.root.1 := fun h => not_rel_root (h ▸ Ray);
    refine ⟨.inl y, root_rel_inl_of_isInConeOf Rra (Or.inr Ray), fun j _ => Or.inr Ray, ?_, ?_⟩ <;>
      rw [inl_forces_boxItr_bot_iff hyne] <;>
      omega;
  . subst hm;
    refine ⟨.inl a, Rra, fun j _ => Or.inl rfl, ?_, ?_⟩ <;>
      rw [inl_forces_boxItr_bot_iff hane] <;>
      omega;
  . refine ⟨.inr (m - a.rank - 1), ?_, fun j hj => ?_, ?_, ?_⟩;
    . show M.root.1 = M.root.1;
      rfl;
    . show m - a.rank - 1 < j;
      omega;
    . rw [inr_forces_boxItr_bot_iff Rra];
      omega;
    . rw [inr_forces_boxItr_bot_iff Rra];
      omega;

/-- Every non-root point of the ω-grafted model has an exact depth: it refutes
`□^[m]⊥` but forces `□^[m+1]⊥` for some `m`. -/
lemma exists_exact_depth_of_ne_root (Rra : M.root.1 ≺ a)
  {v : (M.graftOmega a).World} (hv : v ≠ (M.graftOmega a).root.1) :
  ∃ m : ℕ,
  ¬ Forces (M := (M.graftOmega a).toModel) v (□^[m]⊥) ∧
  Forces (M := (M.graftOmega a).toModel) v (□^[m + 1]⊥) := by
  -- `m` is `x.rank` if embedded, `i + 1 + a.rank` if the chain point `chainPoint i`
  rcases v with x | j;
  . have hx : x ≠ M.root.1 := fun h => hv (congrArg Sum.inl h);
    refine ⟨x.rank, ?_, ?_⟩ <;> rw [inl_forces_boxItr_bot_iff hx] <;> omega;
  . refine ⟨j + 1 + a.rank, ?_, ?_⟩ <;> rw [inr_forces_boxItr_bot_iff Rra] <;> omega;

/--
  **Exact-depth successor** in the ω-grafted model: any point refuting `□^[m+1]⊥` has
  a successor of exact depth `m`. The ω-grafted model thus shares with finite
  GL-models the exact-depth-successor property `Model.of_lt_rank` despite its root
  having infinite depth: below any sufficiently deep point, the grafted chain
  together with the cone of `a` realizes every exact depth.
-/
lemma exists_rel_exact_depth (Rra : M.root.1 ≺ a) {v : (M.graftOmega a).World} {m : ℕ}
  (hv : ¬ Forces (M := (M.graftOmega a).toModel) v (□^[m + 1]⊥)) :
  ∃ w, v ≺ w ∧
  ¬ Forces (M := (M.graftOmega a).toModel) w (□^[m]⊥) ∧
  Forces (M := (M.graftOmega a).toModel) w (□^[m + 1]⊥) := by
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
      refine ⟨.inl y, Rxy, ?_, ?_⟩ <;> rw [inl_forces_boxItr_bot_iff hyne] <;> omega;
  . refine ⟨w, hchain j ?_, hw₁, hw₂⟩;
    have := (inr_forces_boxItr_bot_iff Rra (i := j) (k := m + 1)).not.mp hv;
    omega;

end Depth

section OtherModel

variable {κ' : Type*} [Nonempty κ'] {N : RootedModel κ' α} {c : N.World} [DecidableEq α]
  [M.IsFiniteGL]

/-- The `Φ₀` formula of Remark 1 (p.265), abbreviated for the "almost defining"
uniqueness lemmas below: `□(∼□^[N+1]⊥ 🡒 (◇φ_a ⋏ p̄^{(a)})) ⋏ □(□^[N+1]⊥ 🡒 ⋁_{x⪰a}φ_x)`
with `N = a.rank`. -/
noncomputable abbrev phi0 (M : RootedModel κ α) [M.IsFiniteGL] (a : M.World)
  (P : Finset α) : Formula α :=
  □(∼(□^[a.rank + 1]⊥) 🡒 ((◇(a.charFormulaUnder P)) ⋏ a.valuationConj P))
    ⋏ □((□^[a.rank + 1]⊥) 🡒 ⋁(Finset.univ.image fun y : M.toModel↾a => y.1.charFormulaUnder P))

/--
  D-model case, first half: if `Φ₀` (built from `a`, `P`) is forced at the root of
  another `P`-simple D-model-shaped ω-model `N.graftOmega c`, every point
  reachable from its root that refutes `□^[a.rank+1]⊥` (i.e. is "deep") forces
  `◇φ_a ⋏ p̄^{(a)}`. Unlike the general Lemma 9.1 (p.264), no auxiliary "largest
  shallow-enough predecessor" construction is needed here: in the D-model
  special case `Φ₀`'s first conjunct already speaks directly about `a` (there
  are no lateral cones `r_1,…,r_n` to separate `a` from).

  - [Bek90, Lemma 9.1 (§4, D-model case, first half)]
-/
lemma forces_dia_and_valuationConj_of_not_forces_boxItr
  (hAroot : (N.graftOmega c).root.1 ⊩ phi0 M a P)
  {w : (N.graftOmega c).World} (Rrw : (N.graftOmega c).root.1 ≺ w)
  (hw : ¬ Forces (M := (N.graftOmega c).toModel) w (□^[a.rank + 1]⊥)) :
  Forces (M := (N.graftOmega c).toModel) w (◇(a.charFormulaUnder P) ⋏ a.valuationConj P) :=
  (forces_and.mp hAroot).1 w Rrw (forces_neg.mpr hw)

/--
  D-model case, second half: if `Φ₀` is forced at the root of `N.graftOmega c`,
  every point reachable from its root that forces `□^[a.rank+1]⊥` (i.e. is
  "shallow") forces `⋁_{x⪰a}φ_x`, hence (via `Model.charBisimulationUnder`) is
  `P`-bisimilar to some point of `a`'s cone in `M`.

  - [Bek90, Lemma 9.1 (§4, D-model case, second half)]
-/
lemma forces_fdisj_charFormulaUnder_of_forces_boxItr
  (hAroot : (N.graftOmega c).root.1 ⊩ phi0 M a P)
  {w : (N.graftOmega c).World} (Rrw : (N.graftOmega c).root.1 ≺ w)
  (hw : Forces (M := (N.graftOmega c).toModel) w (□^[a.rank + 1]⊥)) :
  Forces (M := (N.graftOmega c).toModel) w
    (⋁(Finset.univ.image fun y : M.toModel↾a => y.1.charFormulaUnder P)) :=
  (forces_and.mp hAroot).2 w Rrw hw

/--
  Key structural fact for Remark 2 (p.265): if `Φ₀` is forced at the root of
  `N.graftOmega c`, the tail element `c` agrees with `a` on the valuation of
  every atom in `P`. This is `p̄^{(r₀)}` being forced "deep in the chain" of the
  proof.

  - [Bek90, Lemma 9 (p.263, proof)]
-/
lemma val_eq_of_forces_phi0 (hAroot : (N.graftOmega c).root.1 ⊩ phi0 M a P) {q : α}
  (hq : q ∈ P) : M.Val a q ↔ N.Val c q := by
  have Rrw : (N.graftOmega c).root.1 ≺ (Sum.inr a.rank : (N.graftOmega c).World) := by
    show (N.root.1 = N.root.1);
    rfl;
  -- the point of the grafted chain exactly `a.rank` steps below the root reaches `c`
  -- in `a.rank + 1` more steps, so it refutes `□^[a.rank+1]⊥`
  have hpath : Model.RelItr (M := (N.graftOmega c).toModel) (a.rank + 1)
      (Sum.inr a.rank) (Sum.inl c) :=
    Model.relItr_comp (graftOmega.inr_relItr_inr_zero (M := N) (a := c) (n := a.rank))
      (Model.relItr_one.mpr (Or.inl rfl));
  have hw : ¬ Forces (M := (N.graftOmega c).toModel) (Sum.inr a.rank) (□^[a.rank + 1]⊥) :=
    fun h => forces_boxItr.mp h (Sum.inl c) hpath;
  -- hence, by the first conjunct of `Φ₀`, this point carries `a`'s valuation; but every
  -- chain point of `N.graftOmega c` carries exactly `c`'s valuation by construction,
  -- pinning `N.Val c` to agree with `M.Val a` on `P`
  have h := forces_dia_and_valuationConj_of_not_forces_boxItr hAroot Rrw hw;
  exact forces_valuationConj.mp (forces_and.mp h).2 q hq;

/--
  D-model case, cone-localized form: if `Φ₀` is forced at the root of
  `N.graftOmega c`, every point above the root that refutes `□^[a.rank+1]⊥` has,
  for each `x` in the cone of `a`, a successor forcing `φ_x` (through `◇φ_a`
  and the forth clauses of `φ_a`).

  - [Bek90, Lemma 9.1 (§4, D-model case, cone-localized form)]
-/
lemma exists_forces_charFormulaUnder_of_not_forces_boxItr [N.IsFiniteGL]
  (Rrc : N.root.1 ≺ c)
  (hAroot : (N.graftOmega c).root.1 ⊩ phi0 M a P)
  {v : (N.graftOmega c).World} (Rrv : (N.graftOmega c).root.1 ≺ v)
  (hv : ¬ Forces (M := (N.graftOmega c).toModel) v (□^[a.rank + 1]⊥))
  {x : M.World} (hx : x.IsInConeOf a) :
  ∃ w, v ≺ w ∧ Forces (M := (N.graftOmega c).toModel) w (x.charFormulaUnder P) := by
  haveI hGL : (N.graftOmega c).IsGL := isGL Rrc;
  haveI := hGL.toIsTrans;
  obtain ⟨w₀, Rvw₀, hw₀⟩ := forces_dia.mp
    (forces_and.mp (forces_dia_and_valuationConj_of_not_forces_boxItr hAroot Rrv hv)).1;
  rcases hx with rfl | hax;
  . exact ⟨w₀, Rvw₀, hw₀⟩;
  . obtain ⟨w, Rw₀w, hw⟩ := (forces_charFormulaUnder_iff.mp hw₀).2.1 x hax;
    exact ⟨w, IsTrans.trans _ _ _ Rvw₀ Rw₀w, hw⟩;

/-- Root form of `exists_forces_charFormulaUnder_of_not_forces_boxItr`: the root of
`N.graftOmega c` forcing `Φ₀` sees a point forcing `φ_x` for every `x` in the
cone of `a` (through the grafted chain, which is unboundedly deep). -/
lemma root_exists_forces_charFormulaUnder [N.IsFiniteGL]
  (Rrc : N.root.1 ≺ c)
  (hAroot : (N.graftOmega c).root.1 ⊩ phi0 M a P)
  {x : M.World} (hx : x.IsInConeOf a) :
  ∃ w, (N.graftOmega c).root.1 ≺ w ∧
  Forces (M := (N.graftOmega c).toModel) w (x.charFormulaUnder P) := by
  haveI hGL : (N.graftOmega c).IsGL := isGL Rrc;
  haveI := hGL.toIsTrans;
  have Rrv : (N.graftOmega c).root.1 ≺ (Sum.inr a.rank : (N.graftOmega c).World) := by
    show N.root.1 = N.root.1;
    rfl;
  have hv : ¬ Forces (M := (N.graftOmega c).toModel) (Sum.inr a.rank) (□^[a.rank + 1]⊥) :=
    (inr_forces_boxItr_bot_iff Rrc).not.mpr (by omega);
  obtain ⟨w, Rvw, hw⟩ := exists_forces_charFormulaUnder_of_not_forces_boxItr Rrc hAroot Rrv hv hx;
  exact ⟨w, IsTrans.trans _ _ _ Rrv Rvw, hw⟩;

end OtherModel

/--
  D-model case: every `P`-simple D-model -- an ω-model `M.graftOmega a` over a
  finite GL tree `M` where `a` covers the root and there are no lateral cones
  (`hlat`) -- admits an *almost defining* formula `Φ₀` (`AlmostDefines`).

  This is stated only for the D-model special case (`n = 0` in the paper's
  notation): by Remark 1 (p.265) the formula then takes the simpler form
  `Φ₀ = □(∼□^[N+1]⊥ 🡒 (◇φ_{r₀} ⋏ p̄^{(r₀)})) ⋏ □(□^[N+1]⊥ 🡒 ⋁_{x ⪰ r₀} φ_x)`,
  where `N` is the depth of the tail element `r₀ = a`, the `φ_x` are the defining
  formulas of the cones (here realized as `Model.World.charFormulaUnder`, cf. Lemma 7,
  `RootedModel.exists_isDefiningFormula`), and `p̄^{(r₀)}` pins down the valuation of
  `r₀` (`Model.World.valuationConj`); Remark 2 (p.265) provides the almost-defining
  property (the `almost_unique` field). The general case with lateral cones
  (`n > 0`) is not needed for the proof of Lemma 1 -- the D-model countermodel
  produced by Lemma 3 has no lateral cones, and this shape is preserved by the
  `P`-simplification (`exists_simplificationUnder_omega'`) -- and is left as
  future work.

  - [Bek90, Lemma 9 (§4, D-model case), Lemma 1 (§5)]
-/
theorem exists_almostDefiningFormula [DecidableEq α] [M.IsFiniteGLTree]
  (Rra : M.root.1 ≺ a)
  (hcov : ∀ x : M.World, x.IsProperPredecessorOf a → x = M.root.1)
  (hlat : ∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a)
  (hsimple : (M.graftOmega a).IsSimpleUnder P) :
  ∃ A : Formula α, AlmostDefines P (M.graftOmega a) A := by
  classical
  have hane : a ≠ M.root.1 := graft.ne_root_of_rel Rra;
  have hbot : ∀ n : ℕ, ((□^[n]⊥ : Formula α)).atoms = ∅ := by
    intro n; induction n <;> simp_all [Formula.boxItr, Formula.atoms];
  -- `Φ₀` of Remark 1 (p.265): with `N := a.rank` the depth of the tail element,
  -- `Φ₀ = □(∼□^[N+1]⊥ 🡒 (◇φ_a ⋏ p̄^{(a)})) ⋏ □(□^[N+1]⊥ 🡒 ⋁_{x ⪰ a} φ_x)`.
  use phi0 M a P;
  constructor;
  case atoms_subset =>
    have hΓ : (⋁(Finset.univ.image fun y : M.toModel↾a => y.1.charFormulaUnder P)).atoms ⊆ P := by
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
    constructor;
    . -- first conjunct: only the grafted chain points refute `□^[N+1]⊥`, and they
      -- see the cone of `a` and carry its stable valuation
      rintro (x | i) Rrw hw;
      . exfalso;
        have Rrx : M.root.1 ≺ x := Rrw;
        apply forces_neg.mp hw;
        apply inl_forces_boxItr_bot (fun h => not_rel_root (h ▸ Rrx));
        apply iff_rank_lt_forces_boxItr_bot.mp;
        rcases hlat x Rrw with rfl | hax;
        . omega;
        . have := rank_lt_of_rel hax; omega;
      . apply forces_and.mpr;
        constructor;
        . apply forces_dia.mpr;
          exact ⟨.inl a, Or.inl rfl, inl_forces_charFormulaUnder hane⟩;
        . apply forces_valuationConj.mpr;
          intro q _;
          exact Iff.rfl;
    . -- second conjunct: the worlds forcing `□^[N+1]⊥` are exactly the cone points
      -- of `a`, each of which forces its own characteristic formula
      rintro (x | i) Rrw hw;
      . have Rrx : M.root.1 ≺ x := Rrw;
        apply forces_fdisj.mpr;
        refine ⟨x.charFormulaUnder P, ?_, ?_⟩;
        . exact Finset.mem_image.mpr ⟨⟨x, hlat x Rrx⟩, Finset.mem_univ _, rfl⟩;
        . exact inl_forces_charFormulaUnder (fun h => not_rel_root (h ▸ Rrx));
      . exfalso;
        obtain ⟨t, ht⟩ := exists_rank_terminal a;
        exact forces_boxItr.mp hw (.inl t) ⟨.inl a, Or.inl rfl, relItr_inl ht⟩;
  case almost_unique =>
    intro κ' _ N _ c Rrc _ _ hAroot;
    haveI hGL : (N.graftOmega c).IsGL := isGL Rrc;
    haveI := hGL.toIsTrans;
    haveI : Std.Irrefl (N.graftOmega c).Rel :=
      @ConverseWellFounded.irrefl _ _ hGL.toIsConverseWellFounded;
    -- **Remark 2 (p.265)**. The required stabilized bisimulation is defined
    -- semantically: the two roots are related; an embedded point `x` of the D-model
    -- is related to the points of `N.graftOmega c` forcing its characteristic
    -- formula `φ_x`; the chain point `chainPoint i` (of exact depth `i + 1 + a.rank`)
    -- is related to the points of exact depth `i + 1 + a.rank`. Unlike the paper's
    -- `P`-isomorphism, a bisimulation may relate chain points of the two ω-models of
    -- matching depth regardless of where the respective base trees end, so no
    -- Lemma 9.2-style branch-point analysis (nor `P`-simplicity of the other model)
    -- is needed: `Φ₀` provides the forth/back transfers directly through Lemma 9.1
    -- (its first conjunct for the deep points, its second conjunct for the shallow
    -- ones) and the exact-depth lemmas above.
    refine ⟨{
      toRel := fun u v =>
        (u = (M.graftOmega a).root.1 ∧ v = (N.graftOmega c).root.1) ∨
        (u ≠ (M.graftOmega a).root.1 ∧ v ≠ (N.graftOmega c).root.1 ∧
          match u with
          | .inl x => Forces (M := (N.graftOmega c).toModel) v (x.charFormulaUnder P)
          | .inr i =>
            ¬ Forces (M := (N.graftOmega c).toModel) v (□^[i + 1 + a.rank]⊥) ∧
            Forces (M := (N.graftOmega c).toModel) v (□^[i + 1 + a.rank + 1]⊥))
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
          . -- a chain point carries `a`'s valuation; `v` is deep, so it forces
            -- `p̄^{(a)}` by the first conjunct of `Φ₀`
            have hdeep : ¬ Forces (M := (N.graftOmega c).toModel) v (□^[a.rank + 1]⊥) :=
              fun h => hC.1 (forces_boxItr_bot_mono (by omega) h);
            have h := forces_dia_and_valuationConj_of_not_forces_boxItr hAroot
              ((N.graftOmega c).root.2 v hv) hdeep;
            exact forces_valuationConj.mp (forces_and.mp h).2 q hq;
      forth := by
        rintro u u' v (⟨rfl, rfl⟩ | ⟨hu, hv, hC⟩) Ruu';
        . rcases u' with x | i;
          . -- an embedded point above the root lies in the cone of `a` (`hlat`) and
            -- its characteristic formula is forced somewhere above the other root
            have Rrx : M.root.1 ≺ x := Ruu';
            obtain ⟨w, Rrw, hw⟩ := root_exists_forces_charFormulaUnder Rrc hAroot (hlat x Rrx);
            exact ⟨w, Or.inr ⟨inl_ne_root (fun h => not_rel_root (h ▸ Rrx)),
              fun h => not_rel_root (h ▸ Rrw), hw⟩, Rrw⟩;
          . obtain ⟨w, Rrw, -, hw₁, hw₂⟩ := exists_exact_depth Rrc (i + 1 + a.rank);
            exact ⟨w, Or.inr ⟨inr_ne_root, fun h => not_rel_root (h ▸ Rrw), hw₁, hw₂⟩, Rrw⟩;
        . rcases u with x | i;
          . rcases u' with y | j;
            . have Rxy : x ≺ y := Ruu';
              obtain ⟨w, Rvw, hw⟩ := (forces_charFormulaUnder_iff.mp hC).2.1 y Rxy;
              exact ⟨w, Or.inr ⟨inl_ne_root (fun h => not_rel_root (h ▸ Rxy)),
                fun h => not_rel_root (h ▸ Rvw), hw⟩, Rvw⟩;
            . exact absurd (show x = M.root.1 from Ruu') (fun h => hu (congrArg Sum.inl h));
          . rcases u' with y | j;
            . -- `chainPoint i ≺ y` puts `y` in the cone of `a`; `v` is deep, so
              -- Lemma 9.1 provides a successor forcing `φ_y`
              have hy : y.IsInConeOf a := Ruu';
              have hyne : y ≠ M.root.1 := by
                rcases hy with rfl | hay;
                . exact hane;
                . exact fun h => not_rel_root (h ▸ hay);
              have hdeep : ¬ Forces (M := (N.graftOmega c).toModel) v (□^[a.rank + 1]⊥) :=
                fun h => hC.1 (forces_boxItr_bot_mono (by omega) h);
              obtain ⟨w, Rvw, hw⟩ := exists_forces_charFormulaUnder_of_not_forces_boxItr
                Rrc hAroot ((N.graftOmega c).root.2 v hv) hdeep hy;
              exact ⟨w, Or.inr ⟨inl_ne_root hyne, fun h => not_rel_root (h ▸ Rvw), hw⟩, Rvw⟩;
            . have hji : j < i := Ruu';
              obtain ⟨w, Rvw, hw₁, hw₂⟩ := exists_rel_exact_depth Rrc (m := j + 1 + a.rank)
                (fun h => hC.1 (forces_boxItr_bot_mono (by omega) h));
              exact ⟨w, Or.inr ⟨inr_ne_root, fun h => not_rel_root (h ▸ Rvw), hw₁, hw₂⟩, Rvw⟩;
      back := by
        rintro u v v' (⟨rfl, rfl⟩ | ⟨hu, hv, hC⟩) Rvv';
        . by_cases hsh : Forces (M := (N.graftOmega c).toModel) v' (□^[a.rank + 1]⊥);
          . -- a shallow point forces some `φ_t`, `t` in the cone of `a`, by the
            -- second conjunct of `Φ₀`
            obtain ⟨B, hB, hv'B⟩ :=
              forces_fdisj.mp (forces_fdisj_charFormulaUnder_of_forces_boxItr hAroot Rvv' hsh);
            obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hB;
            have htne : t.1 ≠ M.root.1 := fun h => not_isInConeOf_root_of_ne hane (h ▸ t.2);
            exact ⟨.inl t.1, Or.inr ⟨inl_ne_root htne, graft.ne_root_of_rel Rvv', hv'B⟩,
              root_rel_inl_of_isInConeOf Rra t.2⟩;
          . -- a deep point has an exact depth `≥ a.rank + 1`: it matches a chain point
            obtain ⟨m, hm₁, hm₂⟩ :=
              exists_exact_depth_of_ne_root Rrc (graft.ne_root_of_rel Rvv');
            have hge : a.rank + 1 ≤ m := by
              by_contra hlt;
              exact hsh (forces_boxItr_bot_mono (by omega) hm₂);
            refine ⟨.inr (m - a.rank - 1),
              Or.inr ⟨inr_ne_root, graft.ne_root_of_rel Rvv', ?_, ?_⟩, ?_⟩;
            . rw [show m - a.rank - 1 + 1 + a.rank = m by omega];
              exact hm₁;
            . rw [show m - a.rank - 1 + 1 + a.rank + 1 = m + 1 by omega];
              exact hm₂;
            . show M.root.1 = M.root.1;
              rfl;
        . have hv'ne : v' ≠ (N.graftOmega c).root.1 := fun h => not_rel_root (h ▸ Rvv');
          rcases u with x | i;
          . obtain ⟨y, Rxy, hy⟩ := (forces_charFormulaUnder_iff.mp hC).2.2 v' Rvv';
            exact ⟨.inl y, Or.inr ⟨inl_ne_root (fun h => not_rel_root (h ▸ Rxy)), hv'ne, hy⟩, Rxy⟩;
          . by_cases hsh : Forces (M := (N.graftOmega c).toModel) v' (□^[a.rank + 1]⊥);
            . obtain ⟨B, hB, hv'B⟩ := forces_fdisj.mp
                (forces_fdisj_charFormulaUnder_of_forces_boxItr hAroot
                  ((N.graftOmega c).root.2 v' hv'ne) hsh);
              obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hB;
              have htne : t.1 ≠ M.root.1 := fun h => not_isInConeOf_root_of_ne hane (h ▸ t.2);
              exact ⟨.inl t.1, Or.inr ⟨inl_ne_root htne, hv'ne, hv'B⟩,
                show t.1 = a ∨ a ≺ t.1 from t.2⟩;
            . -- a deep successor of the chain point `chainPoint i` has an exact depth
              -- `m` with `a.rank + 1 ≤ m < i + 1 + a.rank`: it matches `chainPoint j`
              -- with `j = m - a.rank - 1 < i`
              obtain ⟨m, hm₁, hm₂⟩ := exists_exact_depth_of_ne_root Rrc hv'ne;
              have hge : a.rank + 1 ≤ m := by
                by_contra hlt;
                exact hsh (forces_boxItr_bot_mono (by omega) hm₂);
              have hlt : m < i + 1 + a.rank := by
                by_contra hle;
                have hstep : Forces (M := (N.graftOmega c).toModel) v'
                    (□^[i + 1 + a.rank]⊥) := by
                  apply forces_boxItr.mpr;
                  intro z hz;
                  exact forces_boxItr.mp hC.2 z ⟨v', Rvv', hz⟩;
                exact hm₁ (forces_boxItr_bot_mono (by omega) hstep);
              refine ⟨.inr (m - a.rank - 1), Or.inr ⟨inr_ne_root, hv'ne, ?_, ?_⟩, ?_⟩;
              . rw [show m - a.rank - 1 + 1 + a.rank = m by omega];
                exact hm₁;
              . rw [show m - a.rank - 1 + 1 + a.rank + 1 = m + 1 by omega];
                exact hm₂;
              . show m - a.rank - 1 < i;
                omega;
    }⟩;

section ConeTail

/--
The tail model over the cone of `a` in `M`: the stabilization of the D-model
`M.graftOmega a` (its chain points carry the stable valuation `M.Val a` and see
exactly the cone of `a`).

- [Bek90]
-/
abbrev coneTail (M : RootedModel κ α) (a : M.World) :
  RootedModel (Model.toTail.World (Model.toRootedModel M.toModel a).toModel) α :=
  (Model.toRootedModel M.toModel a).toModel.toTail (Model.toRootedModel M.toModel a).root.1

variable [M.IsFiniteGL]

/--
  The chain-and-cone part of the D-model `M.graftOmega a` is bisimilar to the
  tail model over the cone of `a`: chain point `i` corresponds to `chainPoint i`,
  cone points to themselves.
-/
def coneTailBisimulation (M : RootedModel κ α) [M.IsFiniteGL] (a : M.World)
  (Rra : M.root.1 ≺ a) :
  (M.graftOmega a).toModel ⇄ (coneTail M a).toModel where
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
      exact not_isInConeOf_root_of_ne (graft.ne_root_of_rel Rra) hroot;
    . exact h.elim;
    . exact h.elim;
    . exact ⟨.inl ⟨u, Rxu⟩, rfl, trivial⟩;
    . exact h.elim;
    . subst h;
      refine ⟨.inr (i' : ℕ∞), rfl, ?_⟩;
      show (i' : ℕ∞) < (i : ℕ∞);
      exact_mod_cast Rxu;
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
      refine ⟨.inr m, rfl, ?_⟩;
      show m < i;
      have hmi : (m : ℕ∞) < (i : ℕ∞) := Rv;
      exact_mod_cast hmi;

/-- The grafted chain point `i` of the D-model is modally equivalent to `chainPoint i`
of the tail model over the cone of `a`. -/
lemma coneTail_chainPoint_modal_equivalent (Rra : M.root.1 ≺ a) (i : ℕ) :
  ModalEquivalent (M₁ := (M.graftOmega a).toModel) (M₂ := (coneTail M a).toModel)
    (Sum.inr i) (Sum.inr (i : ℕ∞)) :=
  modal_equivalent_of_bisimilar (coneTailBisimulation M a Rra)
    (show (coneTailBisimulation M a Rra).toRel (Sum.inr i) (Sum.inr (i : ℕ∞)) from rfl)

/-- An embedded cone point of the D-model is modally equivalent to its copy in the
tail model over the cone of `a`. -/
lemma coneTail_embed_modal_equivalent (Rra : M.root.1 ≺ a) (y : M.toModel↾a) :
  ModalEquivalent (M₁ := (M.graftOmega a).toModel) (M₂ := (coneTail M a).toModel)
    (Sum.inl y.1) (Sum.inl y) :=
  modal_equivalent_of_bisimilar (coneTailBisimulation M a Rra)
    (show (coneTailBisimulation M a Rra).toRel (Sum.inl y.1) (Sum.inl y) from rfl)

/--
  **Stabilization transfer for modalized formulas**: for a D-model
  `M.graftOmega a` (no lateral cones, `hlat`), the forcing of a modalized
  formula at the root agrees, eventually along the chain, with its forcing at
  the chain points of the tail model over the cone of `a`. In particular a
  modalized formula true at the D-model's root is eventually true along the
  tail model's chain, which is exactly what the `LogicS` tail-model semantics
  consumes.

  - [Bek90, Lemma 4 (§4)]
-/
theorem eventually_coneTail_chainPoint_forces_iff_of_modalized
  (Rra : M.root.1 ≺ a) (hlat : ∀ x : M.World, M.root.1 ≺ x → x.IsInConeOf a)
  {C : Formula α} (hC : C.Modalized) :
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
  (Forces (M := (coneTail M a).toModel) (Sum.inr (n : ℕ∞)) C ↔
    (M.graftOmega a).root.1 ⊩ C) := by
  induction C with
  | atom q => exact (hC q rfl).elim;
  | bot => exact ⟨0, fun n _ => Iff.rfl⟩;
  | imp A B ihA ihB =>
    obtain ⟨k₁, h₁⟩ := ihA (fun q => (hC q).1);
    obtain ⟨k₂, h₂⟩ := ihB (fun q => (hC q).2);
    refine ⟨max k₁ k₂, fun n hn => ?_⟩;
    have hA := h₁ n (le_trans (le_max_left _ _) hn);
    have hB := h₂ n (le_trans (le_max_right _ _) hn);
    constructor;
    . intro h ha; exact hB.mp (h (hA.mpr ha));
    . intro h ha; exact hB.mpr (h (hA.mp ha));
  | box A ihA =>
    by_cases h : (M.graftOmega a).root.1 ⊩ (□A);
    . refine ⟨0, fun n _ => iff_of_true ?_ h⟩;
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
      . -- the refuting point is a cone point (no lateral cones), visible from every
        -- chain point of the tail model
        have hx : x.IsInConeOf a := hlat x Rrw;
        refine ⟨0, fun n _ => iff_of_false (fun hbox => ?_) h⟩;
        apply hwA;
        apply (coneTail_embed_modal_equivalent Rra ⟨x, hx⟩).mpr;
        exact hbox (Sum.inl ⟨x, hx⟩) trivial;
      . -- the refuting point is a grafted chain point, visible from every later
        -- chain point of the tail model
        refine ⟨i + 1, fun n hn => iff_of_false (fun hbox => ?_) h⟩;
        apply hwA;
        apply (coneTail_chainPoint_modal_equivalent Rra i).mpr;
        apply hbox (Sum.inr (i : ℕ∞));
        show (i : ℕ∞) < (n : ℕ∞);
        exact_mod_cast hn;

end ConeTail

end graftOmega

end RootedModel

end
