module

public import SeqPL.Gentzen.Maehara

@[expose]
public section

universe u
variable {α : Type u} [DecidableEq α]

namespace LogicGL

variable {A B : Formula α}

lemma provable_imp_iff_provableGentzen_seqent : A 🡒 B ∈ LogicGL ↔ ⊢ᵍ ({A} ⟹ {B}) := by
  constructor;
  · intro h;
    exact ProvableGentzen.deduction_theorem.mpr $ LogicGL_TFAE.out 1 2 |>.mp h
  · intro h;
    apply LogicGL_TFAE.out 2 1 |>.mp;
    apply ProvableGentzen.deduction_theorem.mp;
    simpa using h;

noncomputable def interpolant (h : A 🡒 B ∈ LogicGL) : Formula α := ProvableGentzen.interpolant (PartitionOf.ss A B) (provable_imp_iff_provableGentzen_seqent.mp h)

variable {h : A 🡒 B ∈ LogicGL}

lemma interpolant_provable_ant : A 🡒 (interpolant h) ∈ LogicGL := by
  apply provable_imp_iff_provableGentzen_seqent.mpr;
  exact ProvableGentzen.interpolant_provable_ant (P := PartitionOf.ss A B);

lemma interpolant_provable_suc : (interpolant h) 🡒 B ∈ LogicGL := by
  apply provable_imp_iff_provableGentzen_seqent.mpr;
  exact ProvableGentzen.interpolant_provable_suc (P := PartitionOf.ss A B);

lemma interpolant_atoms : (interpolant h).atoms ⊆ A.atoms ∩ B.atoms := by
  have := ProvableGentzen.interpolant_atoms (h := LogicGL.provable_imp_iff_provableGentzen_seqent.mp h) (P := PartitionOf.ss A B);
  rwa [PartitionOf.ss_atoms] at this;

/--
  **Craig interpolation property** (Maehara's method via Gentzen calculus): `Logic GL` has the
  Craig interpolation property.
-/
theorem CIP (h : (A 🡒 B) ∈ LogicGL) :
    ∃ C : Formula α, (A 🡒 C) ∈ LogicGL ∧ (C 🡒 B) ∈ LogicGL ∧ C.atoms ⊆ A.atoms ∩ B.atoms :=
  ⟨interpolant h, interpolant_provable_ant, interpolant_provable_suc, interpolant_atoms⟩

end LogicGL

end
