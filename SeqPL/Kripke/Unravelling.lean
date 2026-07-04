module

public import SeqPL.Kripke.Preservation
public import SeqPL.Kripke.Simplification
public import SeqPL.Vorspiel.List

/-!
# Tree unravelling of GL-models

This file ports Foundation's `Frame.mkTransTreeUnravelling` to SeqPL's model
setting. Given a rooted model `M`, its *tree unravelling* `M.unravelling`
is the rooted model whose worlds are the `M.Rel`-chains starting at `M`'s root,
ordered by proper prefix. Since GL-models are transitive, the (transitively
closed) accessibility relation is exactly *proper prefix extension*, which is
automatically transitive, irreflexive and a tree (`RootedModel.IsTree`): the
ancestors of a chain are precisely its prefixes, which are linearly ordered.

The last-element map `x ↦ x.1.getLast` is a p-morphism onto `M`, so the root of
the unravelling is modally equivalent to `M`'s root. When `M` is a finite
GL-model, so is its unravelling; hence validity over the (smaller) class of
finite GL *tree* models already entails GL-provability -- the new item of
`LogicGL.provability_TFAE`.
-/

@[expose]
public section

universe u

variable [Nonempty κ] {α : Type u}

namespace RootedModel

variable (M : RootedModel κ α)

/-- Worlds of the tree unravelling: `M.Rel`-chains starting from the root. -/
abbrev unravelling.World : Type _ :=
  { c : List M.World // [M.root.1] <+: c ∧ c.IsChain M.Rel }

namespace unravelling

variable {M} (x : unravelling.World M)

lemma root_prefix : [M.root.1] <+: x.1 := x.2.1

lemma isChain : x.1.IsChain M.Rel := x.2.2

@[simp]
lemma ne_nil : x.1 ≠ [] := by
  intro h;
  simpa [h] using x.2.1;

/-- The last world of a chain: the "current" point the chain represents. -/
def World.last : M.World := x.1.getLast (ne_nil x)

instance instNonempty : Nonempty (unravelling.World M) :=
  ⟨⟨[M.root.1], List.prefix_refl _, by simp⟩⟩

end unravelling

open unravelling in
/-- The tree unravelling of a rooted model `M`: worlds are `M.Rel`-chains from
the root, accessibility is proper prefix extension, and the valuation is that of
the last world of the chain. -/
def unravelling : RootedModel (unravelling.World M) α where
  Rel' x y := x.1 <+: y.1 ∧ x.1.length < y.1.length
  Val' x q := M.Val (unravelling.World.last x) q
  root := ⟨⟨[M.root.1], List.prefix_refl _, by simp⟩, by
    rintro ⟨x, hx₁, hx₂⟩ hx;
    refine ⟨hx₁, ?_⟩;
    obtain ⟨t, rfl⟩ := hx₁;
    cases t with
    | nil => simp at hx;
    | cons a t => simp;⟩

namespace unravelling

variable {M} {x y : (M.unravelling).World}

@[simp]
lemma rel_iff : x ≺ y ↔ x.1 <+: y.1 ∧ x.1.length < y.1.length := Iff.rfl

@[simp]
lemma val_iff {q : α} : (M.unravelling).Val x q ↔ M.Val (World.last x) q := Iff.rfl

@[simp]
lemma root_val : (M.unravelling).root.1.1 = [M.root.1] := rfl

@[simp]
lemma root_last : World.last (M.unravelling).root.1 = M.root.1 := by
  simp [World.last];

instance instIsTrans : IsTrans _ (M.unravelling).Rel := by
  constructor;
  rintro x y z ⟨h₁, h₂⟩ ⟨h₃, h₄⟩;
  exact ⟨h₁.trans h₃, by omega⟩;

instance instIrrefl : Std.Irrefl (M.unravelling).Rel := by
  constructor;
  rintro x ⟨-, h⟩;
  omega;

instance instIsTree : (M.unravelling).IsTree := by
  constructor;
  rintro x y z ⟨hxz, -⟩ ⟨hyz, -⟩;
  rcases List.prefix_or_prefix_of_prefix hxz hyz with h | h;
  . rcases lt_or_eq_of_le h.length_le with hl | hl;
    . right; left; exact ⟨h, hl⟩;
    . left; exact Subtype.ext $ h.eq_of_length hl;
  . rcases lt_or_eq_of_le h.length_le with hl | hl;
    . right; right; exact ⟨h, hl⟩;
    . left; exact Subtype.ext $ (h.eq_of_length hl).symm;

instance instFinite [M.IsFiniteGL] : Finite (M.unravelling).World := by
  haveI := Classical.decEq M.World;
  haveI : Finite { l : List M.World // l.IsChain M.Rel } := List.chains_finite;
  apply Finite.of_injective
    (fun x => (⟨x.1, x.2.2⟩ : { l : List M.World // l.IsChain M.Rel }));
  intro x y h;
  apply Subtype.ext;
  simpa using congrArg Subtype.val h;

instance instIsFiniteGL [M.IsFiniteGL] : (M.unravelling).IsFiniteGL where
  finite := instFinite

/-- The last-element map is a p-morphism from the tree unravelling onto `M`. -/
def pMorphism [M.IsGL] : (M.unravelling).toModel →ₚ M.toModel where
  toFun := World.last
  forth := by
    rintro x y ⟨hp, hl⟩;
    apply List.rel_getLast_of_isChain_trans (isChain y) (ne_nil y);
    . exact hp.subset $ List.getLast_mem (ne_nil x);
    . obtain ⟨t, ht⟩ := hp;
      have htne : t ≠ [] := by
        rintro rfl;
        simp only [List.append_nil] at ht;
        rw [ht] at hl;
        omega;
      have hd : x.1.Disjoint t :=
        List.disjoint_of_nodup_append $ ht ▸ (isChain y).nodup_of_irrefl_trans;
      have he : y.1.getLast (ne_nil y) = t.getLast htne := by
        rw [show y.1.getLast (ne_nil y) = (x.1 ++ t).getLast (ht ▸ ne_nil y) by simp [ht]];
        exact List.getLast_append_of_ne_nil _ htne;
      rw [he];
      intro e;
      exact hd (e ▸ List.getLast_mem (ne_nil x)) (List.getLast_mem htne);
  back := by
    rintro x v hv;
    refine ⟨⟨x.1.concat v, ?_, ?_⟩, ?_, ?_, ?_⟩;
    . exact x.2.1.trans (by simp);
    . exact (List.isChain_concat_of_not_nil (ne_nil x)).mpr ⟨isChain x, hv⟩;
    . simp [World.last];
    . simp;
    . simp;
  atomic := Iff.rfl

/-- The root of the tree unravelling is modally equivalent to `M`'s root. -/
lemma modal_equivalence_root [M.IsGL] :
    (M.unravelling).root.1 ↭ M.root.1 := by
  have h : (M.unravelling).root.1 ↭ (pMorphism (M := M)).toFun (M.unravelling).root.1 :=
    (pMorphism (M := M)).modal_equivalence _;
  rwa [show (pMorphism (M := M)).toFun (M.unravelling).root.1 = M.root.1 from root_last]
    at h;

end unravelling

end RootedModel

end
