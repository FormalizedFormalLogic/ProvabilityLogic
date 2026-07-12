module

public import ProvabilityLogic.Kripke.PseudoTail
public import ProvabilityLogic.Kripke.Simplification
public import ProvabilityLogic.ToFoundation.Vorspiel.List.Chain
public import Mathlib.Data.Fintype.Option

/-!
# Tree realization of pseudo-tail models (Bek90 §4, Lemma 3)

ProvabilityLogic's semantics of `LogicD` (`LogicD.provability_TFAE`) produces countermodels of the
shape `M.toPseudoTail r o`, whereas the simplification machinery of [Bek90] §4
(Lemma 8, `ProvabilityLogic/Kripke/Simplification.lean`) operates on ω-models of the shape
`N.graftOmega a` over finite *trees* `N` with `a` *covering* the root. The two
frame constructions are not isomorphic (the root of a `toPseudoTail` model has a free
valuation `o` and no lateral cones, while `graftOmega` keeps the base root with
its valuation and all its cones), so a bridge is needed -- this is the content of
Lemma 3 of [Bek90] §4 in this codebase.

This file provides the bridge: the **D-model tree** `M.dModelTree r o` is the finite
GL tree consisting of

* a root (the paper's *minimum point* `b`, valuation `o`, seeing everything),
* a *tail point* `a★` (valuation `M.Val r`, seeing all chains), and
* the nonempty `M.Rel`-chains of `M` ordered by proper prefix (the "forest
  unravelling" of `M`, each chain valued by its last element),

and the evident last-element map is a pseudo-epimorphism from
`(M.dModelTree r o).graftOmega a★` onto `M.toPseudoTail r o` sending root to
root. Hence any `toPseudoTail`-shaped countermodel yields a `graftOmega`-shaped
countermodel over a finite tree, in which the tail point covers the root and there
are **no lateral cones** (every point above the root lies in the tail point's cone) --
i.e. a *D-model* in the sense of [Bek90], as required by the Lemma 9 machinery.
-/

@[expose]
public section

universe u

variable [Nonempty κ] {α : Type u}

namespace Model

variable (M : Model κ α)

/-- Worlds of the chain forest of `M`: nonempty `M.Rel`-chains, to be ordered by
proper prefix (the "forest unravelling" of the rootless model `M`, cf.
`RootedModel.unravelling`). -/
abbrev chainForest.World : Type _ := { c : List M.World // c ≠ [] ∧ c.IsChain M.Rel }

namespace chainForest

variable {M} (x : chainForest.World M)

/-- The last world of a chain: the "current" point the chain represents. -/
def World.last : M.World := x.1.getLast x.2.1

instance instFinite [M.IsFiniteGL] : Finite (chainForest.World M) := by
  haveI := Classical.decEq M.World;
  haveI : Finite { l : List M.World // l.IsChain M.Rel } := List.chains_finite;
  apply Finite.of_injective
    (fun x => (⟨x.1, x.2.2⟩ : { l : List M.World // l.IsChain M.Rel }));
  intro x y h;
  exact Subtype.ext (by simpa using congrArg Subtype.val h);

end chainForest

/-- Worlds of the D-model tree: `none` is the root (the paper's minimum point `b`),
`some none` is the tail point `a★`, and `some (some c)` are the chains of the forest. -/
abbrev dModelTree.World : Type _ := Option (Option (chainForest.World M))

instance : Nonempty (dModelTree.World M) := ⟨none⟩

/--
  The **D-model tree** over `M` with tail valuation at `r` and root valuation `o`:
  a root `b` (valuation `o`) below a tail point `a★` (valuation `M.Val r`) below the
  chain forest of `M` (each chain valued by its last element, ordered by proper
  prefix). Grafting the ω-chain at `a★` realizes `M.toPseudoTail r o` over a finite
  tree; see `dModelTree.graftOmega_root_forces_iff`.
-/
def dModelTree (r : M.World) (o : α → Prop) : RootedModel (dModelTree.World M) α where
  Rel' x y :=
    match x, y with
    | some (some c), some (some c') => c.1 <+: c'.1 ∧ c.1.length < c'.1.length
    | some none, some (some _) => True
    | none, none => False
    | none, _ => True
    | _, _ => False
  Val' x q :=
    match x with
    | some (some c) => M.Val (chainForest.World.last c) q
    | some none => M.Val r q
    | none => o q
  root := ⟨none, by
    rintro (_ | _ | c) hx;
    . exact absurd rfl hx;
    . trivial;
    . trivial;⟩

namespace dModelTree

variable {M} {r : M.World} {o : α → Prop}

/-- The tail point `a★` of the D-model tree. -/
abbrev tailPoint : (M.dModelTree r o).NonRoot := ⟨some none, by simp [dModelTree]⟩

/-- The embedding of a chain into the D-model tree. -/
abbrev embed (c : chainForest.World M) : (M.dModelTree r o).World := some (some c)

@[simp] lemma root_eq : (M.dModelTree r o).root.1 = none := rfl

instance : IsTrans _ (M.dModelTree r o).Rel := ⟨by
  rintro (_ | _ | x) (_ | _ | y) (_ | _ | z) h h' <;>
    first
    | exact h.elim
    | exact h'.elim
    | trivial
    | exact ⟨h.1.trans h'.1, Nat.lt_trans h.2 h'.2⟩;⟩

instance : Std.Irrefl (M.dModelTree r o).Rel := ⟨by
  rintro (_ | _ | c) h;
  . exact h;
  . exact h;
  . exact absurd h.2 (lt_irrefl _);⟩

instance instFinite [M.IsFiniteGL] : Finite (M.dModelTree r o).World := by
  haveI : Finite (chainForest.World M) := chainForest.instFinite;
  infer_instance;

instance [M.IsFiniteGL] : (M.dModelTree r o).IsFiniteGL where
  finite := instFinite

open Model.World (IsInConeOf IsProperPredecessorOf)

/-- The D-model tree is a tree: the ancestors of any point are linearly ordered. -/
instance : (M.dModelTree r o).IsTree := by
  constructor;
  rintro (_ | _ | x) (_ | _ | y) (_ | _ | z) hxz hyz <;>
    first
    | exact hxz.elim
    | exact hyz.elim
    | exact Or.inl rfl
    | exact Or.inr (Or.inl trivial)
    | exact Or.inr (Or.inr trivial)
    | (rcases List.prefix_or_prefix_of_prefix hxz.1 hyz.1 with h | h;
       . rcases lt_or_eq_of_le h.length_le with hl | hl;
         . exact Or.inr (Or.inl ⟨h, hl⟩);
         . exact Or.inl (congrArg (some ∘ some) (Subtype.ext (h.eq_of_length hl)));
       . rcases lt_or_eq_of_le h.length_le with hl | hl;
         . exact Or.inr (Or.inr ⟨h, hl⟩);
         . exact Or.inl (congrArg (some ∘ some) (Subtype.ext (h.eq_of_length hl).symm)));

/-- The tail point lies above the root. -/
lemma root_rel_tailPoint : (M.dModelTree r o).root.1 ≺ (tailPoint : (M.dModelTree r o).NonRoot).1 :=
  trivial

/-- The tail point covers the root: its only proper predecessor is the root. -/
lemma tailPoint_covers_root :
  ∀ x : (M.dModelTree r o).World,
  IsProperPredecessorOf (M := (M.dModelTree r o).toModel) x tailPoint.1 →
  x = (M.dModelTree r o).root.1 := by
  rintro (_ | _ | c) ⟨hne, hR⟩;
  . rfl;
  . exact absurd rfl hne;
  . exact hR.elim;

/--
The D-model tree has no lateral cones: every point above the root lies in the
tail point's cone. This is the "D-model" condition (`n = 0`).

- [Bek90, Lemma 9]
-/
lemma isInConeOf_tailPoint_of_root_rel :
  ∀ x : (M.dModelTree r o).World, (M.dModelTree r o).root.1 ≺ x →
  IsInConeOf (M := (M.dModelTree r o).toModel) x tailPoint.1 := by
  rintro (_ | _ | c) hR;
  . exact hR.elim;
  . exact Or.inl rfl;
  . exact Or.inr trivial;

section PseudoEpimorphism

open RootedModel

/-- The singleton chain at a world of `M`. -/
abbrev singletonChain (x : M.World) : chainForest.World M := ⟨[x], by simp, by simp⟩

@[simp]
lemma last_singletonChain {x : M.World} :
  chainForest.World.last (singletonChain x) = x := rfl

variable [M.IsFiniteGL]

/--
  The last-element map is a pseudo-epimorphism from the ω-model grafted on the
  D-model tree onto the pseudo-tail model: the root `b` goes to the pseudo-tail root
  ω, the tail point `a★` to `chainPoint 0`, the grafted chain shifts by one, and
  chains project to their last element.
-/
def graftOmegaPseudoEpimorphism (M : Model κ α) [M.IsFiniteGL] (r : M.World)
  (o : α → Prop) :
  ((M.dModelTree r o).graftOmega tailPoint).toModel →ₚ
  (M.toPseudoTail r o).toModel where
  toFun := fun
    | .inl (some (some c)) => .inl (chainForest.World.last c)
    | .inl (some none) => .inr 0
    | .inl none => .inr ⊤
    | .inr n => .inr ((n : ℕ) + 1 : ℕ)
  forth := by
    haveI := Classical.decEq M.World;
    rintro ((_ | _ | c) | i) ((_ | _ | c') | j) Rxy;
    -- from the root `b` (↦ ω)
    . exact Rxy.elim;
    . show (0 : ℕ∞) < (⊤ : ℕ∞);
      simp;
    . trivial;
    . show (((j : ℕ) + 1 : ℕ) : ℕ∞) < (⊤ : ℕ∞);
      exact WithTop.coe_lt_top _;
    -- from the tail point `a★` (↦ chainPoint 0)
    . exact Rxy.elim;
    . exact Rxy.elim;
    . trivial;
    . exact absurd (show (some (none : Option (chainForest.World M))) = none from Rxy)
        (by simp);
    -- from an embedded chain (↦ its last element)
    . exact Rxy.elim;
    . exact Rxy.elim;
    . exact List.rel_getLast_getLast_of_prefix c'.2.2 Rxy.1 Rxy.2 c.2.1 c'.2.1;
    . exact absurd (show (some (some c) : Option (Option (chainForest.World M))) = none from Rxy)
        (by simp);
    -- from a grafted chain point (↦ chainPoint (i + 1))
    . rcases Rxy with h | h;
      . exact absurd (show (none : Option (Option (chainForest.World M))) = some none from h)
          (by simp);
      . exact h.elim;
    . show (0 : ℕ∞) < (((i : ℕ) + 1 : ℕ) : ℕ∞);
      exact_mod_cast Nat.succ_pos i;
    . trivial;
    . show (((j : ℕ) + 1 : ℕ) : ℕ∞) < (((i : ℕ) + 1 : ℕ) : ℕ∞);
      exact_mod_cast Nat.succ_lt_succ Rxy;
  back := by
    rintro ((_ | _ | c) | i) (x | j) h;
    -- from the root `b` (ω) to an embedded world
    . exact ⟨.inl (embed (singletonChain x)), rfl, trivial⟩;
    -- from the root `b` (ω) down the chain
    . have hj : j ≠ (⊤ : ℕ∞) := ne_top_of_lt (show j < (⊤ : ℕ∞) from h);
      obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hj;
      match m with
      | 0 => exact ⟨.inl tailPoint.1, rfl, trivial⟩;
      | m + 1 => exact ⟨.inr m, rfl, rfl⟩;
    -- from the tail point `a★` (chainPoint 0) to an embedded world
    . exact ⟨.inl (embed (singletonChain x)), rfl, trivial⟩;
    -- chainPoint 0 sees no chain point
    . exact absurd (show j < (0 : ℕ∞) from h) (by simp);
    -- from an embedded chain to an embedded world: extend the chain
    . have hR : M.Rel (chainForest.World.last c) x := h;
      have hchain : (c.1.concat x).IsChain M.Rel :=
        (List.isChain_concat_of_not_nil c.2.1).mpr ⟨c.2.2, hR⟩;
      refine ⟨.inl (embed ⟨c.1.concat x, by simp, hchain⟩), ?_, ?_, ?_⟩;
      . simp [chainForest.World.last];
      . simp;
      . simp;
    -- embedded worlds see no chain points
    . exact h.elim;
    -- from a grafted chain point to an embedded world
    . exact ⟨.inl (embed (singletonChain x)), rfl, Or.inr trivial⟩;
    -- from a grafted chain point down the chain
    . have hj : j ≠ (⊤ : ℕ∞) := ne_top_of_lt (show j < (((i : ℕ) + 1 : ℕ) : ℕ∞) from h);
      obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hj;
      match m with
      | 0 => exact ⟨.inl tailPoint.1, rfl, Or.inl rfl⟩;
      | m + 1 =>
        refine ⟨.inr m, rfl, ?_⟩;
        show m < i;
        have hlt : (((m : ℕ) + 1 : ℕ) : ℕ∞) < (((i : ℕ) + 1 : ℕ) : ℕ∞) := h;
        have : (m + 1 : ℕ) < (i + 1 : ℕ) := by exact_mod_cast hlt;
        omega;
  atomic := by
    rintro ((_ | _ | c) | i) q;
    . show o q ↔ if (⊤ : ℕ∞) = (⊤ : ℕ∞) then o q else M.Val r q;
      rw [if_pos rfl];
    . show M.Val r q ↔ if (0 : ℕ∞) = (⊤ : ℕ∞) then o q else M.Val r q;
      rw [if_neg (by simp)];
    . exact Iff.rfl;
    . show M.Val r q ↔ if (((i : ℕ) + 1 : ℕ) : ℕ∞) = (⊤ : ℕ∞) then o q else M.Val r q;
      rw [if_neg (by exact_mod_cast WithTop.coe_ne_top)];

/--
Root forcing transfers between the ω-model grafted on the D-model tree and the
pseudo-tail model (model-theoretic core).

- [Bek90, Lemma 3]
-/
lemma graftOmega_root_forces_iff {C : Formula α} :
  ((M.dModelTree r o).graftOmega tailPoint).root.1 ⊩ C ↔
  (M.toPseudoTail r o).root.1 ⊩ C :=
  (graftOmegaPseudoEpimorphism M r o).modal_equivalence
    ((M.dModelTree r o).graftOmega tailPoint).root.1 (A := C)

end PseudoEpimorphism

end dModelTree

end Model

end
