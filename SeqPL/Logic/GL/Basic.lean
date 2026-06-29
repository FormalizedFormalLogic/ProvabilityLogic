module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Hilbert.Basic
public import SeqPL.Kripke.PointGenerate
public import Mathlib.Tactic.TFAE

@[expose]
public section

variable {α : Type u}

abbrev LogicGL {α} : Logic α := { A | ⊢ʰ A }

theorem LogicGL_TFAE [DecidableEq α] {A : Formula α} : [
  A ∈ LogicGL,
  ⊢ʰ A,
  ⊢ᵍ (∅ ⟹ {A}),
  ⊢ᵍᶜ (∅ ⟹ {A}),
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A
].TFAE
  := by
  tfae_have 1 ↔ 2 := by grind;
  tfae_have 2 → 3 := ProvableGentzen.of_provableHilbert;
  tfae_have 3 → 2 := by
    intro h;
    simpa using ProvableHilbert.mdp (ProvableHilbert.of_provableGentzen (S := ∅ ⟹ {A}) h) (by simp);
  tfae_have 3 → 4 := GentzenWithCutProvable.of_without_cut;
  tfae_have 4 → 3 := ProvableGentzen.of_with_cut;
  tfae_have 2 → 5 := by
    intro h κ _;
    apply ProvableHilbert.Kripke.finite_soundness h;
  tfae_have 5 → 2 := ProvableHilbert.Kripke.completeness;
  tfae_finish;

theorem LogicGL_semantical_TFAE [DecidableEq α] {A : Formula α} : [
  A ∈ LogicGL,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGL] → M.root.1 ⊩ A
].TFAE := by
  tfae_have 1 ↔ 2 := LogicGL_TFAE.out 0 4;
  tfae_have 2 → 3 := by
    intro h κ _ M _;
    apply h;
  tfae_have 3 → 2 := by
    intro h κ _ M _ x;
    exact Model.toRootedModel.forces_same_at_root.mp $ h (M.toRootedModel x);
  tfae_finish;

end
