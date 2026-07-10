module

public import SeqPL.Kripke.Simplification

/-!
# Defining formulas for finite GL-models (Bek90 §4, Lemma 7)

This file defines defining formulas (matching [Bek90] §4) and proves Lemma 7: every
finite GL-model has a defining formula over any finite set of variables `P`.

[Bek90] cites prior work ([12], [Art86]) for Lemma 7 and states it for models
simple-under-`P`, with uniqueness up to `P`-isomorphism. SeqPL's `IsDefiningFormula`
instead phrases uniqueness via `Model.BisimulationUnder` (bisimilarity-under-`P` of the
roots), and under this formulation the lemma reduces to the classical characteristic
formula construction: for each world `x` (by well-founded recursion on `World.rank`)
take

`χ_x := p̄^(x) ⋏ ⋀_{x ≺ y} ◇χ_y ⋏ □(⋁_{x ≺ y} χ_y)`

where `p̄^(x)` (`World.valuationConj`) pins down `x`'s valuation on `P`. The relation
`fun x w => w ⊩ χ_x` is then a bisimulation-under-`P` against an *arbitrary* model
(`Model.charBisimulationUnder`), so no simpleness or tree-ness hypotheses are needed
anywhere.

The next target is Lemma 9 (the ω-model analogue, whose formula `Φ` is spelled out
explicitly on p.264 of [Bek90] using `TBB`/`□^[N+1]⊥`-style depth markers together
with the lateral cones' defining formulas).
-/

@[expose]
public section

universe u

variable {κ κ' : Type*} [Nonempty κ] [Nonempty κ'] {α : Type u} [DecidableEq α]

namespace Model

noncomputable section

open Classical

variable {M : Model κ α} {P : Finset α} {x y : M.World} {N : Model κ' α}

/--
  The conjunction of literals over `P` pinning down the valuation of `x` on `P`:
  `a` for each `a ∈ P` true at `x`, and `∼a` for each `a ∈ P` false at `x`.

  - [Bek90]
-/
def World.valuationConj (P : Finset α) (x : M.World) : Formula α :=
  ⋀(P.image fun a => if M.Val x a then #a else ∼#a)

/-- The atoms of `x.valuationConj P` are contained in `P`. -/
@[grind .]
lemma World.atoms_valuationConj : (x.valuationConj P).atoms ⊆ P := by
  intro b hb;
  have hb' := FormulaFinset.atoms_conj_subset _ hb;
  simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at hb';
  obtain ⟨A, ⟨a, ha, rfl⟩, hbA⟩ := hb';
  split at hbA <;> simp_all [Formula.atoms];

/-- A world `w` (of any model) forces `x.valuationConj P` iff it agrees with `x` on `P`. -/
@[grind =]
lemma World.forces_valuationConj {w : N.World} :
  w ⊩ x.valuationConj P ↔ ∀ a ∈ P, (M.Val x a ↔ N.Val w a) := by
  constructor;
  · intro h a ha;
    have := World.forces_fconj.mp h _ (Finset.mem_image_of_mem _ ha);
    split at this <;> grind [World.Forces];
  · intro h;
    apply World.forces_fconj.mpr;
    rintro A hA;
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA;
    split <;> grind [World.Forces];

section

variable [Fintype M.World]

/-- The type of all (proper) successors of `x`. -/
abbrev World.Successors (x : M.World) := { y : M.World // x ≺ y }

instance : Fintype (x.Successors) := Subtype.fintype _

/--
  The characteristic formula of `x` over `P`: it pins down the valuation of `x` on
  `P`, asserts that each successor's characteristic formula is possible, and
  asserts that every successor satisfies some successor's characteristic formula.

  - [Bek90]
-/
def World.charFormulaUnder [M.IsGL] (P : Finset α) (x : M.World) : Formula α :=
  x.valuationConj P
  ⋏ ⋀(Finset.univ.image fun y : x.Successors => ◇(y.1.charFormulaUnder P))
  ⋏ □(⋁(Finset.univ.image fun y : x.Successors => y.1.charFormulaUnder P))
termination_by x.rank
decreasing_by all_goals exact rank_lt_of_rel y.2

variable [M.IsGL]

lemma World.charFormulaUnder_def :
  x.charFormulaUnder P =
  x.valuationConj P
  ⋏ ⋀(Finset.univ.image fun y : x.Successors => ◇(y.1.charFormulaUnder P))
  ⋏ □(⋁(Finset.univ.image fun y : x.Successors => y.1.charFormulaUnder P)) := by
  rw [World.charFormulaUnder];

/-- The atoms of `x.charFormulaUnder P` are contained in `P`. -/
@[grind .]
lemma World.atoms_charFormulaUnder : (x.charFormulaUnder P).atoms ⊆ P := by
  suffices h : ∀ n (x : M.World), x.rank = n → (x.charFormulaUnder P).atoms ⊆ P from
    h x.rank x rfl;
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro x rfl;
    rw [World.charFormulaUnder_def];
    simp only [Formula.atoms_and, Finset.union_subset_iff];
    refine ⟨⟨World.atoms_valuationConj, ?_⟩, ?_⟩;
    · apply subset_trans (FormulaFinset.atoms_conj_subset _);
      intro a ha;
      simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at ha;
      obtain ⟨A, ⟨y, -, rfl⟩, haA⟩ := ha;
      rw [Formula.atoms_dia] at haA;
      exact ih y.1.rank (rank_lt_of_rel y.2) y.1 rfl haA;
    · rw [Formula.atoms_box];
      apply subset_trans (FormulaFinset.atoms_disj_subset _);
      intro a ha;
      simp only [FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at ha;
      obtain ⟨A, ⟨y, -, rfl⟩, haA⟩ := ha;
      exact ih y.1.rank (rank_lt_of_rel y.2) y.1 rfl haA;

/--
  A world `w` (of any model) forces `x.charFormulaUnder P` iff it agrees with `x` on
  `P` and the forth/back conditions of a bisimulation-under-`P` hold at `(x, w)` with
  respect to the characteristic-formula relation.
-/
lemma World.forces_charFormulaUnder_iff {w : N.World} :
  w ⊩ x.charFormulaUnder P ↔
  (∀ a ∈ P, (M.Val x a ↔ N.Val w a)) ∧
  (∀ y : M.World, x ≺ y → ∃ v : N.World, w ≺ v ∧ v ⊩ y.charFormulaUnder P) ∧
  (∀ v : N.World, w ≺ v → ∃ y : M.World, x ≺ y ∧ v ⊩ y.charFormulaUnder P) := by
  rw [World.charFormulaUnder_def, World.forces_and, World.forces_and];
  constructor;
  · rintro ⟨⟨h1, h2⟩, h3⟩;
    refine ⟨World.forces_valuationConj.mp h1, ?_, ?_⟩;
    · intro y Rxy;
      have := World.forces_fconj.mp h2 (◇(y.charFormulaUnder P)) $
        Finset.mem_image_of_mem _ (Finset.mem_univ (⟨y, Rxy⟩ : x.Successors));
      exact World.forces_dia.mp this;
    · intro v Rwv;
      obtain ⟨A, hA, hvA⟩ := World.forces_fdisj.mp (h3 v Rwv);
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hA;
      exact ⟨y.1, y.2, hvA⟩;
  · rintro ⟨h1, h2, h3⟩;
    refine ⟨⟨World.forces_valuationConj.mpr h1, ?_⟩, ?_⟩;
    · apply World.forces_fconj.mpr;
      rintro A hA;
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hA;
      obtain ⟨v, Rwv, hv⟩ := h2 y.1 y.2;
      exact World.forces_dia.mpr ⟨v, Rwv, hv⟩;
    · intro v Rwv;
      apply World.forces_fdisj.mpr;
      obtain ⟨y, Rxy, hv⟩ := h3 v Rwv;
      exact ⟨y.charFormulaUnder P,
        Finset.mem_image_of_mem _ (Finset.mem_univ (⟨y, Rxy⟩ : x.Successors)), hv⟩;

/-- Every world forces its own characteristic formula. -/
@[grind .]
lemma World.forces_charFormulaUnder_self : x ⊩ x.charFormulaUnder P := by
  suffices h : ∀ n (x : M.World), x.rank = n → x ⊩ x.charFormulaUnder P from
    h x.rank x rfl;
  intro n;
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro x rfl;
    apply World.forces_charFormulaUnder_iff.mpr;
    refine ⟨by grind, ?_, ?_⟩;
    · intro y Rxy;
      exact ⟨y, Rxy, ih y.rank (rank_lt_of_rel Rxy) y rfl⟩;
    · intro v Rxv;
      exact ⟨v, Rxv, ih v.rank (rank_lt_of_rel Rxv) v rfl⟩;

end

/--
  The characteristic-formula relation `fun x w => w ⊩ x.charFormulaUnder P` is a
  bisimulation-under-`P` between a finite GL-model `M` and an *arbitrary* model `N`:
  the atomic/forth/back conditions are exactly the three components of
  `World.forces_charFormulaUnder_iff`.
-/
def charBisimulationUnder (P : Finset α) (M : Model κ α) [Fintype M.World] [M.IsGL]
  (N : Model κ' α) : M ⇄[P] N where
  toRel x w := w ⊩ x.charFormulaUnder P
  atomic ha h := (World.forces_charFormulaUnder_iff.mp h).1 _ ha
  forth h Rxy := by
    obtain ⟨v, Rwv, hv⟩ := (World.forces_charFormulaUnder_iff.mp h).2.1 _ Rxy;
    exact ⟨v, hv, Rwv⟩;
  back h Rwv := by
    obtain ⟨y, Rxy, hy⟩ := (World.forces_charFormulaUnder_iff.mp h).2.2 _ Rwv;
    exact ⟨y, hy, Rxy⟩;

end

end Model

namespace RootedModel

open scoped Model

/--
  A formula `A` is a **defining formula** for a (finite) GL-model `M` simple-under-`P`
  (following [12]) if `A` depends only on `P`, is true at `M`'s root, and `M` is
  the *unique* model simple-under-`P` (up to bisimilarity-under-`P` of the roots,
  our surrogate for "`P`-isomorphism", see `Model.BisimulationUnder` in
  `SeqPL/Kripke/Preservation.lean`) in which `A` is true.

  - [Bek90]
-/
structure IsDefiningFormula (P : Finset α) (M : RootedModel κ α) (A : Formula α) : Prop where
  atoms_subset : A.atoms ⊆ P
  root_forces : M.root.1 ⊩ A
  unique_up_to_bisim : ∀ {κ' : Type u} [Nonempty κ'] (N : RootedModel κ' α) [N.IsFiniteGL],
    N.IsSimpleUnder P → N.root.1 ⊩ A →
    ∃ Bi : M.toModel ⇄[P] N.toModel, Bi M.root.1 N.root.1

/--
  If the set of variables `P` is finite, every finite GL-model has a defining
  formula, namely the characteristic formula of its root.

  Note that no simpleness (nor tree-ness) hypothesis on `M` is needed: the paper
  states the lemma for models simple-under-`P` because its uniqueness is up to
  `P`-isomorphism, whereas our `IsDefiningFormula` phrases uniqueness via
  `Model.BisimulationUnder`, for which `Model.charBisimulationUnder` works against
  arbitrary models.

  - [Bek90, Lemma 7]
-/
theorem exists_isDefiningFormula {M : RootedModel κ α} [M.IsFiniteGL] (P : Finset α) :
  ∃ A : Formula α, IsDefiningFormula P M A := by
  haveI : Fintype M.World := Fintype.ofFinite _;
  use M.root.1.charFormulaUnder P;
  constructor;
  . exact Model.World.atoms_charFormulaUnder;
  . exact Model.World.forces_charFormulaUnder_self;
  . rintro κ' _ N _ _ hNA;
    use Model.charBisimulationUnder P M.toModel N.toModel;
    exact hNA;

end RootedModel

end
