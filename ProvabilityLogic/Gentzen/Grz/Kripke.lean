module

public import ProvabilityLogic.Gentzen.Grz.Basic
public import ProvabilityLogic.Gentzen.GL.Kripke
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finite.Prod

/-!
Kripke completeness of the cut-free `LogicGrz.ProofGentzen`. The Lindenbaum-style saturation
follows the `LogicS` development (`ProvabilityLogic.Gentzen.S.Kripke`), whose `boxL`-closure
construction is the model for the `boxT`-closure needed here, rather than the plain `LogicGL`
one, since `LogicGrz` also unboxes formulas from the antecedent.
-/

@[expose]
public section

variable {κ : Type u} [Nonempty κ]
         {α : Type v} [DecidableEq α]
         {M : Model κ α}
         {A B : Formula α} {Γ Γ' Δ Δ' : FormulaFinset α}

namespace LogicGrz

open LogicGL
open scoped FormulaFinset

/--
The subformula closure needed to run the Lindenbaum construction for `LogicGrz.ProofGentzen`:
besides the ordinary subformulas of `S`, it contains the Grz companions `ψ 🡒 □ψ` and their boxed
form `□(ψ 🡒 □ψ)` for every `□ψ` occurring in `S`. The `boxGrz` rule's premise introduces
`□(ψ 🡒 □ψ)`, which is not a subformula of the conclusion, so a saturated sequent built on top of
`S` may range beyond `S.subfmls`. The middle component is needed on top of the other two because
`boxT`-saturation unboxes `□(ψ 🡒 □ψ)` into the antecedent, and the resulting `ψ 🡒 □ψ` must both
stay inside the closure and get its own slot in the complexity-sorted saturation pass.
-/
noncomputable def _root_.LogicGL.Sequent.subfmlsGrz (S : Sequent α) : FormulaFinset α :=
  S.subfmls
    ∪ (S.subfmls.prebox.image (λ ψ => ψ 🡒 □ψ))
    ∪ (S.subfmls.prebox.image (λ ψ => □(ψ 🡒 □ψ)))

variable {S : Sequent α}

@[grind .]
lemma subfmls_subset_subfmlsGrz : S.subfmls ⊆ S.subfmlsGrz := by
  intro C hC;
  simp [Sequent.subfmlsGrz, hC];

@[grind =>]
lemma imp_mem_subfmlsGrz (h : A 🡒 B ∈ S.subfmlsGrz) : A ∈ S.subfmls ∧ B ∈ S.subfmls := by
  simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image] at h;
  rcases h with (h | ⟨ψ, hψ, heq⟩) | ⟨ψ, hψ, heq⟩;
  · exact ⟨Sequent.mem_subfmls_subfmls h Formula.mem_subfmls_imp_left,
      Sequent.mem_subfmls_subfmls h Formula.mem_subfmls_imp_right⟩;
  · obtain ⟨rfl, rfl⟩ : A = ψ ∧ B = □ψ := by grind;
    have hψ : □A ∈ S.subfmls := FormulaFinset.iff_mem_prebox_mem.mp hψ;
    exact ⟨Sequent.mem_subfmls_subfmls hψ Formula.mem_subfmls_box, hψ⟩;
  · exact absurd heq (by grind);

@[grind =>]
lemma box_mem_subfmlsGrz (h : □A ∈ S.subfmlsGrz) : A ∈ S.subfmlsGrz := by
  simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image] at h;
  rcases h with (h | ⟨ψ, _, heq⟩) | ⟨ψ, hψ, heq⟩;
  · exact subfmls_subset_subfmlsGrz (Sequent.mem_subfmls_subfmls h Formula.mem_subfmls_box);
  · exact absurd heq (by grind);
  · obtain rfl : A = ψ 🡒 □ψ := by grind;
    simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image];
    exact Or.inl (Or.inr ⟨ψ, hψ, rfl⟩);

@[grind =>]
lemma grzCompanions_mem_subfmlsGrz (h : □A ∈ S.subfmls) :
  (A 🡒 □A) ∈ S.subfmlsGrz ∧ □(A 🡒 □A) ∈ S.subfmlsGrz := by
  have h : A ∈ S.subfmls.prebox := FormulaFinset.iff_mem_prebox_mem.mpr h;
  constructor;
  · simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image];
    exact Or.inl (Or.inr ⟨A, h, rfl⟩);
  · simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image];
    exact Or.inr ⟨A, h, rfl⟩;

/--
  A `LogicGrz.ProofGentzen`-unprovable sequent saturated for `impL`/`impR`, closed under the
  reflexivity rule `boxT` on its antecedent, and bounded by the subformula closure of a base
  sequent `BS`. The bound is deliberately asymmetric: the antecedent may range over the enlarged
  `BS.subfmlsGrz` but the succedent stays within the plain `BS.subfmls`, so that a boxed formula
  `□A` in the succedent is guaranteed to have its Grz companion `A 🡒 □A` inside `BS.subfmlsGrz`.
-/
structure ExpandedSequent (BS : Sequent α) extends Sequent α where
  saturated   : toSequent.Saturated
  boxT_closed : ∀ {A : Formula α}, □A ∈ toSequent.ant → A ∈ toSequent.ant
  ant_subset  : toSequent.ant ⊆ BS.subfmlsGrz
  suc_subset  : toSequent.suc ⊆ BS.subfmls
  unprovable  : ⊬ᵍ[Grz] toSequent

namespace ExpandedSequent

attribute [grind .] ExpandedSequent.saturated ExpandedSequent.boxT_closed
  ExpandedSequent.ant_subset ExpandedSequent.suc_subset ExpandedSequent.unprovable

variable {BS : Sequent α} {S : ExpandedSequent BS} {A : Formula α}

@[grind .]
lemma not_mem_both : ¬(A ∈ S.1.1 ∧ A ∈ S.1.2) := by
  push Not;
  intro h₁ h₂;
  apply S.unprovable;
  exact ProvableGentzen.union' _ h₁ h₂;

@[grind .] lemma not_mem_bot_ant : ⊥ ∉ S.1.1 := by grind;
@[grind =>] lemma of_mem_imp_ant (h : A 🡒 B ∈ S.1.1 := by grind) : A ∈ S.1.2 ∨ B ∈ S.1.1 := S.saturated.impL h
@[grind =>] lemma of_mem_imp_suc (h : A 🡒 B ∈ S.1.2 := by grind) : A ∈ S.1.1 ∧ B ∈ S.1.2 := S.saturated.impR h

end ExpandedSequent

end LogicGrz

end
