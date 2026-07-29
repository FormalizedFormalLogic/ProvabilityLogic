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

open Classical in
/--
  One step of the Lindenbaum-style saturation for `LogicGrz.ProofGentzen`: process the given
  list of formulas, saturating the sequent for `impL`, `impR` and `boxT` while preserving
  `LogicGrz.ProofGentzen`-unprovability.
-/
@[grind]
noncomputable def lindenbaum_indexed (S₀ : Sequent α) (S₀_unprovable : ⊬ᵍ[Grz] S₀) : FormulaList α → { S : Sequent α // ⊬ᵍ[Grz] S }
| [] => ⟨S₀, S₀_unprovable⟩
| (A 🡒 B) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed S₀ S₀_unprovable Γ;
  if h : (A 🡒 B) ∈ S.1 then
    if h : ⊬ᵍ[Grz] ((S.1) ⟹ (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
    else ⟨((insert B S.1) ⟹ S.2), by
      push Not at h;
      contrapose! hS;
      have := ProvableGentzen.impL h hS;
      rwa [(show insert (A 🡒 B) S.1 = S.1 by grind)] at this;
    ⟩
  else if h : (A 🡒 B) ∈ S.2 then ⟨
    ((insert A S.1) ⟹ (insert B S.2)),
    by
      contrapose! hS;
      have := ProvableGentzen.impR hS;
      rwa [(show insert (A 🡒 B) S.2 = S.2 by grind)] at this;
  ⟩
  else ⟨S, hS⟩
| (□A) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed S₀ S₀_unprovable Γ;
  if h : (□A) ∈ S.1 then ⟨
    ((insert A S.1) ⟹ S.2),
    by
      contrapose! hS;
      have := ProvableGentzen.boxT hS;
      rwa [(show insert (□A) S.1 = S.1 by grind)] at this;
  ⟩
  else ⟨S, hS⟩
| _ :: Γ => lindenbaum_indexed S₀ S₀_unprovable Γ

variable {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[Grz] S₀} {Γ : FormulaList α}

/-- Every step of `lindenbaum_indexed` only ever extends `S₀`. -/
lemma subset_lindenbaum_indexed : S₀ ⊆ (lindenbaum_indexed S₀ S₀_unprovable Γ).1 := by
  induction Γ with
  | nil =>
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons A Γ ih =>
    match A with
    | #a | ⊥ => exact ih
    | A 🡒 B =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2.trans (Finset.subset_insert _ _)⟩
      · exact ⟨ih.1, ih.2⟩;
    | □A =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2⟩;

variable {BS : Sequent α}

/--
  Two-sided invariant of `lindenbaum_indexed`: if the antecedent of `S₀` stays inside
  `BS.subfmlsGrz` and its succedent inside `BS.subfmls`, so do those of the resulting sequent.
  The bound is asymmetric like `ExpandedSequent` itself; each membership is derived from the
  invariant already established for the shorter list together with the closure lemmas for
  `Sequent.subfmlsGrz`, so no side condition on `Γ` is needed.
-/
lemma bounds_lindenbaum_indexed (S₀_ant : S₀.ant ⊆ BS.subfmlsGrz) (S₀_suc : S₀.suc ⊆ BS.subfmls) :
  (lindenbaum_indexed S₀ S₀_unprovable Γ).1.ant ⊆ BS.subfmlsGrz ∧
  (lindenbaum_indexed S₀ S₀_unprovable Γ).1.suc ⊆ BS.subfmls := by
  induction Γ with
  | nil => exact ⟨S₀_ant, S₀_suc⟩
  | cons C Γ ih =>
    match C with
    | #a | ⊥ => exact ih
    | A 🡒 B =>
      dsimp only [lindenbaum_indexed];
      split_ifs with h1 h2 h3;
      · exact ⟨Finset.insert_subset (subfmls_subset_subfmlsGrz (imp_mem_subfmlsGrz (ih.1 h1)).2) ih.1, ih.2⟩;
      · exact ⟨ih.1, Finset.insert_subset (imp_mem_subfmlsGrz (ih.1 h1)).1 ih.2⟩;
      · exact ⟨
          Finset.insert_subset (subfmls_subset_subfmlsGrz (Sequent.mem_subfmls_subfmls (ih.2 h3) Formula.mem_subfmls_imp_left)) ih.1,
          Finset.insert_subset (Sequent.mem_subfmls_subfmls (ih.2 h3) Formula.mem_subfmls_imp_right) ih.2
        ⟩;
      · exact ih;
    | □A =>
      dsimp only [lindenbaum_indexed];
      split_ifs with h;
      · exact ⟨Finset.insert_subset (box_mem_subfmlsGrz (ih.1 h)) ih.1, ih.2⟩;
      · exact ih;

end ExpandedSequent

end LogicGrz

end
