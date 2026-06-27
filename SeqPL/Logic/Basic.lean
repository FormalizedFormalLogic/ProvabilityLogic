module

public import SeqPL.Hilbert.Basic
public import Mathlib.Tactic.TFAE

@[expose]
public section

variable {α : Type u}

abbrev Logic (α) := Set (Formula α)

abbrev LogicGL (α) : Logic α := { A | ⊢ʰ A }

theorem LogicGL_TFAE [DecidableEq α] {A : Formula α} : [
  A ∈ LogicGL α,
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

end
