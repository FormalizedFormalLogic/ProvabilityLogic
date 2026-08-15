module

public import ProvabilityLogic.Logic.SumQuasiNormal
public import ProvabilityLogic.Hilbert.Grz.Basic

/-!
# Soundness and Kripke completeness of `LogicGrz`

This file bundles the equivalences between: membership in `LogicGrz` (Grz-provability),
Hilbert-style provability, cut-free and cut-full Gentzen-style provability, validity over
finite Grz-models, and validity at the root of finite rooted Grz-models.

Unlike `LogicGL`, Grz has no labelled Gentzen calculus or tree-model unravelling in this
repository, so the `provability_TFAE` equivalence list is shorter.
-/

@[expose]
public section

variable {α : Type u}

abbrev LogicGrz {α} : Logic α := { A | ⊢ʰ[Grz] A }

namespace LogicGrz

theorem provability_TFAE [DecidableEq α] {A : Formula α} : [
  A ∈ LogicGrz,
  ⊢ʰ[Grz] A,
  ⊢ᵍ[Grz] (∅ ⟹ {A}),
  ⊢ᵍᶜ[Grz] (∅ ⟹ {A}),
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGrz] → M ⊧ A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGrz] → M.root.1 ⊩[_] A
].TFAE := by
  tfae_have 1 ↔ 2 := by grind;
  tfae_have 2 → 3 := ProvableGentzen.of_provableHilbert;
  tfae_have 3 → 2 := ProvableHilbert.of_provableGentzen_singleton;
  tfae_have 3 → 4 := GentzenWithCutProvable.of_without_cut;
  tfae_have 4 → 3 := ProvableGentzen.of_with_cut;
  tfae_have 2 → 5 := by
    intro h κ _ M _;
    exact Model.validateSequent_singleton_iff.mp
      (ProvableGentzen.Kripke.finite_soundness (ProvableGentzen.of_provableHilbert h) M);
  tfae_have 5 → 3 := by
    intro h;
    apply ProvableGentzen.Kripke.completeness;
    intro κ _ M _;
    exact Model.validateSequent_singleton_iff.mpr (h M);
  tfae_have 5 → 6 := fun h {κ} _ M _ => h M.toModel M.root.1;
  tfae_have 6 → 5 := by
    intro h κ _ M _ x;
    exact Model.toRootedModel.forces_same_at_root.mp $ h (M.toRootedModel x);
  tfae_finish;

theorem iff_provableHilbert [DecidableEq α] {A : Formula α} : A ∈ LogicGrz ↔ ⊢ʰ[Grz] A :=
  provability_TFAE.out 0 1

theorem iff_provableGentzen [DecidableEq α] {A : Formula α} : A ∈ LogicGrz ↔ ⊢ᵍ[Grz] (∅ ⟹ {A}) :=
  provability_TFAE.out 0 2

theorem iff_provableGentzenWithCut [DecidableEq α] {A : Formula α} : A ∈ LogicGrz ↔ ⊢ᵍᶜ[Grz] (∅ ⟹ {A}) :=
  provability_TFAE.out 0 3

theorem iff_forces [DecidableEq α] {A : Formula α} :
    A ∈ LogicGrz ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGrz] → M ⊧ A :=
  provability_TFAE.out 0 4

theorem iff_forces_root [DecidableEq α] {A : Formula α} :
    A ∈ LogicGrz ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGrz] → M.root.1 ⊩[_] A :=
  provability_TFAE.out 0 5

end LogicGrz

end
