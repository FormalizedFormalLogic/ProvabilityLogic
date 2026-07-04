module

public import SeqPL.Kripke.Simplification

/-!
# Defining formulas for GL-models simple-under-`P` (Bek90 §4, Lemmas 7 and 9)

**Status: scaffolding only.** This file records the *definition* of a defining
formula (matching [Bek90] §4) and the *statement* of Lemma 7 (existence, for finite
GL-models simple-under-`P`). It does **not** attempt a proof: Lemma 7 itself is not
proved inline in [Bek90] -- the paper cites prior work ([12], and via that lineage
Artemov 1986 / Boolos 1980's theory of "simple" GL-models) for it. Constructing the
formula requires genuinely new SeqPL infrastructure (combining, for each point `x` of
a finite model simple-under-`P`, a formula pinning down `x`'s exact valuation together with a
box-quantified statement enumerating *exactly* its successors' defining formulas, by
structural induction on the model's rank) that does not yet exist anywhere in this
project. This is flagged in the classification literature as the heaviest part of the
[Bek90] §4-5 development; see `.direct/exists-lemma56.md` for the session notes on
scope and a suggested plan.

Once Lemma 7 is available, Lemma 9 (the ω-model analogue, whose formula `Φ` is spelled
out explicitly on p.264 of [Bek90] using `TBB`/`□^[N+1]⊥`-style depth markers together
with the lateral cones' defining formulas) is comparatively more mechanical, and is the
next target after this.
-/

@[expose]
public section

universe u

variable [Nonempty κ] {α : Type u} [DecidableEq α]

namespace RootedModel

/--
  A formula `A` is a **defining formula** for a (finite) GL-model `M` simple-under-`P`
  (Bek90 §4, following [12]) if `A` depends only on `P`, is true at `M`'s root, and
  `M` is the *unique* model simple-under-`P` (up to bisimilarity-under-`P` of the
  roots, our surrogate for "`P`-isomorphism", see `Model.BisimulationUnder` in
  `SeqPL/Kripke/Preservation.lean`) in which `A` is true.
-/
structure IsDefiningFormula (P : Finset α) (M : RootedModel κ α) (A : Formula α) : Prop where
  atoms_subset : A.atoms ⊆ P
  root_forces : M.root.1 ⊩ A
  unique_up_to_bisim : ∀ {κ' : Type u} [Nonempty κ'] (N : RootedModel κ' α) [N.IsFiniteGL],
    N.IsSimpleUnder P → N.root.1 ⊩ A →
    ∃ Bi : Model.BisimulationUnder P M.toModel N.toModel, Bi M.root.1 N.root.1

/--
  **Lemma 7 in [Bek90] §4**: if the set of variables `P` is finite, every finite
  GL-model simple-under-`P` has a defining formula.

  **Not proved in this session** -- see the module docstring for why (this is
  genuinely new territory for SeqPL, not a routine adaptation of existing lemmas).
-/
theorem exists_isDefiningFormula {M : RootedModel κ α} [M.IsFiniteGL] (P : Finset α)
    (hM : M.IsSimpleUnder P) : ∃ A : Formula α, IsDefiningFormula P M A := by
  sorry

end RootedModel

end
