module

public import SeqPL.Kripke.Basic
public import SeqPL.Gentzen.Basic

@[expose]
public section

variable [Nonempty κ] {M : Model κ} {A B : Formula} {Γ Γ' Δ Δ' : FormulaFinset}


abbrev trivial_GL_model : Model (Fin 1) where
  Rel' := λ _ _ => False
  Val := λ _ _ => False

instance : trivial_GL_model.IsFiniteGL where
  finite := inferInstance;
  trans  := by tauto;
  irrefl := by tauto;


namespace Model.World

@[grind]
def ForcesSequent (x : M.World) (S : Sequent) : Prop := (∀ C ∈ S.ant, x ⊩ C) → (∃ D ∈ S.suc, x ⊩ D)
infix:55 " ⊩ " => ForcesSequent

lemma forced_succ_singleton_sequent {M : Model κ} {x : M.World} : x ⊩ (Γ ⟹ {A}) ↔ (∀ C ∈ Γ, x ⊩ C) → x ⊩ A := by grind;

end Model.World



namespace Model

@[grind]
def ValidateSequent (M : Model κ) (S : Sequent) : Prop := ∀ x : M.World, x ⊩ S
infix:50 " ⊧ " => ValidateSequent

variable {M : Model κ} {Γ Γ' Δ Δ' : FormulaFinset} {A B : Formula}

lemma validate_gentzen_axm : M ⊧ ({A} ⟹ {A}) := by
  intro x h;
  use A;
  constructor;
  . grind;
  . exact h _ (by grind);

lemma validate_gentzen_botL : M ⊧ ({⊥} ⟹ ∅) := by
  intro x;
  simp [World.ForcesSequent];

lemma validate_gentzen_wkL (h : M ⊧ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ' := by grind) : M ⊧ (Γ' ⟹ Δ) := by
  intro x h';
  apply h;
  grind;

lemma validate_gentzen_wkR (h : M ⊧ (Γ ⟹ Δ)) (hΔ : Δ ⊆ Δ' := by grind) : M ⊧ (Γ ⟹ Δ') := by
  intro x hΓ;
  obtain ⟨D, hD₁, hD₂⟩ := h x hΓ;
  grind;

lemma validate_gentzen_impL (hA : M ⊧ (Γ ⟹ insert A Δ)) (hB : M ⊧ (insert B Γ ⟹ Δ)) : M ⊧ ((insert (A 🡒 B) Γ) ⟹ Δ) := by
  intro x h;
  replace hA := hA x
  replace hB := hB x;
  simp only [Finset.mem_insert, forall_eq_or_imp] at h;
  grind;

lemma validate_gentzen_impR (h : M ⊧ ((insert A Γ) ⟹ (insert B Δ))) : M ⊧ (Γ ⟹ (insert (A 🡒 B) Δ)) := by
  intro x hΓ;
  by_cases x ⊩ A;
  . obtain ⟨D, hD₁, hD₂⟩ := h x $ by grind;
    simp at hD₁;
    rcases hD₁ with (rfl | hD₁);
    . use A 🡒 D; grind;
    . use D; grind;
  . use A 🡒 B;
    grind;

open Model.World
lemma validate_gentzen_boxGL [M.IsGL] (h : M ⊧ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : M ⊧ (Γ.box ⟹ {□A}) := by
  intro x;
  apply forced_succ_singleton_sequent.mpr;
  intro hΓ y Rxy;
  apply forced_succ_singleton_sequent.mp $ h y;
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, forall_eq_or_imp];
  refine ⟨?_, ?_⟩;
  . by_contra hC;
    obtain ⟨z, Ryz, hz⟩ := iff_not_forced_box.mp hC;
    obtain ⟨t, ⟨Ryt, hntA⟩, ht₂⟩ := M.has_terminal ({z | y ≺ z ∧ ¬z ⊩ A}) ⟨z, ⟨Ryz, hz⟩⟩;
    apply hntA;
    apply forced_succ_singleton_sequent.mp $ h t;
    simp;
    constructor;
    . rintro t' Rtt';
      by_contra;
      exact ht₂ t' ⟨_root_.trans Ryt Rtt', by assumption⟩ Rtt';
    . rintro C (hC | ⟨C, hC, rfl⟩);
      . apply hΓ (□C) (by simpa) t;
        apply _root_.trans Rxy Ryt;
      . intro t' Rtt';
        apply hΓ (□C) (by simpa) t';
        apply _root_.trans (_root_.trans Rxy Ryt) Rtt';
  . rintro C (hC | ⟨C, hC, rfl⟩);
    . exact hΓ (□C) (by simpa) y Rxy;
    . intro z Ryz;
      exact hΓ (□C) (by simpa) z (_root_.trans Rxy Ryz);

end Model


namespace ProvableGentzen

namespace Kripke

open Model in
theorem soundness (h : ⊢ᵍ S) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ, [M.IsGL] → M ⊧ S := by
  obtain ⟨p⟩ := h;
  intro _ M M_finiteGL;
  induction p with
  | axm A => exact validate_gentzen_axm
  | botL => exact validate_gentzen_botL
  | wkL h _ ih => exact validate_gentzen_wkL ih;
  | wkR h _ ih => exact validate_gentzen_wkR ih;
  | impL _ _ ih₁ ih₂ => exact validate_gentzen_impL ih₁ ih₂
  | impR _ ih => exact validate_gentzen_impR ih
  | boxGL _ ih => exact validate_gentzen_boxGL ih

theorem finite_soundness (h : ⊢ᵍ S) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ, [M.IsFiniteGL] → M ⊧ S := λ _ _ M [M.IsFiniteGL] => soundness h M

end Kripke

@[simp, grind .]
theorem not_provable_empty : ⊬ᵍ (∅ ⟹ ∅) := by
  by_contra h;
  have : (0 : trivial_GL_model.World) ⊩ (∅ ⟹ ∅) := Kripke.finite_soundness h trivial_GL_model 0;
  grind;

end ProvableGentzen




namespace Formula

def subfmls : Formula → Finset Formula
| #a    => {#a}
| ⊥     => {⊥}
| A 🡒 B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)
| □A    => insert (□A) A.subfmls

@[grind .]
lemma mem_subfmls_self : A ∈ A.subfmls := by cases A <;> simp [Formula.subfmls];

end Formula


namespace FormulaFinset

@[grind]
def subfmls (Γ : FormulaFinset) : Finset Formula := Finset.biUnion Γ Formula.subfmls

@[grind .] lemma subset_self_subfmls : Γ ⊆ Γ.subfmls := by grind;

@[grind]
noncomputable def prebox (Γ : FormulaFinset) : FormulaFinset := Γ.preimage (□·) $ by grind [Set.InjOn];

@[grind =]
lemma iff_mem_prebox_mem : A ∈ Γ.prebox ↔ □A ∈ Γ := by simp [FormulaFinset.prebox];

end FormulaFinset


namespace Sequent

@[grind]
def subfmls (S : Sequent) : Finset Formula := S.ant.subfmls ∪ S.suc.subfmls

structure subset (S T : Sequent) : Prop where
  ant_subset : S.ant ⊆ T.ant
  suc_subset : S.suc ⊆ T.suc

instance : HasSubset (Sequent) := ⟨subset⟩

variable {S : Sequent}

@[grind .] lemma subset_self_subfmls : S.ant ∪ S.suc ⊆ S.subfmls := by grind;

structure Saturated (S : Sequent) where
  impL : ∀ {A B}, A 🡒 B ∈ S.1 → A ∈ S.2 ∨ B ∈ S.1
  impR : ∀ {A B}, A 🡒 B ∈ S.2 → A ∈ S.1 ∧ B ∈ S.2

structure Expanded (BS : Sequent) (S : Sequent) extends S.Saturated where
  subset_subfmls : S.1 ∪ S.2 ⊆ BS.subfmls
  unProvableGentzen     : ⊬ᵍ S

end Sequent


structure ExpandedSequent (BS : Sequent) extends Sequent where
  saturated         : toSequent.Saturated
  subset_subfmls    : toSequent.1 ∪ toSequent.2 ⊆ BS.subfmls
  unProvableGentzen : ⊬ᵍ toSequent

namespace ExpandedSequent

attribute [grind .] ExpandedSequent.saturated ExpandedSequent.subset_subfmls ExpandedSequent.unProvableGentzen

variable {BS : Sequent} {S : ExpandedSequent BS} {A : Formula}

@[grind .] lemma not_mem_both : ¬(A ∈ S.1.1 ∧ A ∈ S.1.2) := by grind;
@[grind .] lemma not_mem_bot_ant : ⊥ ∉ S.1.1 := by grind;
@[grind =>] lemma of_mem_imp_ant (h : A 🡒 B ∈ S.1.1 := by grind) : A ∈ S.1.2 ∨ B ∈ S.1.1 := S.saturated.impL h
@[grind =>] lemma of_mem_imp_suc (h : A 🡒 B ∈ S.1.2 := by grind) : A ∈ S.1.1 ∧ B ∈ S.1.2 := S.saturated.impR h

section

variable [Fact (⊬ᵍ BS)]

open Classical in
noncomputable def lindenbaum_indexed (BS : Sequent) [Fact (⊬ᵍ BS)] {S₀} (hS₀ : ⊬ᵍ S₀) : List Formula → { S : Sequent // ⊬ᵍ S }
| [] => ⟨S₀, hS₀⟩
| ((A 🡒 B) :: l) =>
  let ⟨S, hS⟩ := lindenbaum_indexed BS hS₀ l;
  if h : (A 🡒 B) ∈ S.1 then
    if h : ⊬ᵍ ((S.1) ⟹ (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
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
| (_ :: l) => lindenbaum_indexed BS hS₀ l

lemma mem_lindenbaum_indexed {BS : Sequent} [Fact (⊬ᵍ BS)] {S₀} {S₀_unProvableGentzen : ⊬ᵍ S₀} :
  A ∈ (lindenbaum_indexed BS S₀_unProvableGentzen l).1.1 → A ∈ S₀.1 := by
  induction l with
  | nil => simp [lindenbaum_indexed];
  | cons A l ih =>
    match A with
    | #a | □A | ⊥ => simpa [lindenbaum_indexed];
    | (A 🡒 B) =>
      dsimp [lindenbaum_indexed];
      generalize eT : lindenbaum_indexed BS S₀_unProvableGentzen l = T at ih;
      split;
      . split;
        . sorry;
        . sorry;
      . sorry;

noncomputable def lindenbaum (BS : Sequent) [Fact (⊬ᵍ BS)]
  {S₀} (S₀_subfml : (S₀.ant ∪ S₀.suc) ⊆ BS.subfmls) (S₀_unProvableGentzen : ⊬ᵍ S₀)
  : ExpandedSequent BS :=
  let S := lindenbaum_indexed BS S₀_unProvableGentzen (BS.subfmls.toList);
  {
    toSequent := S.1,
    unProvableGentzen := S.2,
    saturated := {
      impL := by
        intro A B h;

        sorry;
      impR := by
        intro A B h;
        sorry;
    }
    subset_subfmls := by
      intro A hA;
      apply S₀_subfml;
      sorry;
  }

lemma subset_lindenbaum (BS : Sequent) [Fact (⊬ᵍ BS)] {S₀} (S₀_subfml : (S₀.ant ∪ S₀.suc) ⊆ BS.subfmls) (hS₀ : ⊬ᵍ S₀) : S₀ ⊆ (lindenbaum BS S₀_subfml hS₀).1 := by
  sorry

end

instance : Finite (ExpandedSequent BS) := by
  sorry;

instance [Fact (⊬ᵍ BS)] : Nonempty (ExpandedSequent BS) := ⟨lindenbaum BS (S₀ := BS) (by grind) (Fact.elim inferInstance)⟩

end ExpandedSequent



namespace ProvableGentzen.Kripke

variable {BS : Sequent} [Fact (⊬ᵍ BS)]

@[grind]
def countermodelOf (BS : Sequent) [Fact (⊬ᵍ BS)] : Model (ExpandedSequent BS) where
  Val S a := #a ∈ S.1.1
  Rel' S T :=
    S.1.1.prebox ⊂ T.1.1.prebox ∧
    S.1.1.prebox ⊆ T.1.1

instance : (countermodelOf BS).IsFiniteGL where
  finite := inferInstance
  trans := by grind;
  irrefl := by grind;

variable {S : (countermodelOf BS).World} {A : Formula}

lemma truthlemma :
  (A ∈ S.1.1 → S ⊩ A) ∧ (A ∈ S.1.2 → ¬S ⊩ A)
  := by
  induction A generalizing S with
  | box A ih =>
    constructor;
    . intro h T RST;
      exact ih.1 $ RST.2 (by simpa [FormulaFinset.prebox]);
    . intro h;
      have : ⊬ᵍ (insert (□A) (S.1.1.prebox ∪ S.1.1.prebox.box) ⟹ {A}) := by
        have := S.unProvableGentzen;
        contrapose! this;
        exact ProvableGentzen.wk (ProvableGentzen.boxGL this)
          (show S.1.1.prebox.box ⊆ S.1.1 by grind)
          (show {□A} ⊆ S.1.2 by grind);
      let T := ExpandedSequent.lindenbaum BS (by
        intro B;
        sorry;
        /-
        simp only [Finset.insert_union, Finset.union_assoc, Finset.union_singleton,
          Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_image];
        rintro (rfl | rfl | hB | ⟨B, hB, rfl⟩);
        . app@apply S.subset_subfmls (□A);
          sorry
        . exact S.subset_subfmls (by grind);
        . apply S.subset_subfmls
          simp;
          sorry;
        . sorry;
        -/
      ) this;
      have hT := ExpandedSequent.subset_lindenbaum BS (by sorry) this;
      apply S.iff_not_forced_box.mpr;
      use T;
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      . intro B hB;
        simp only [FormulaFinset.iff_mem_prebox_mem]
        apply hT.1;
        sorry;
        -- grind;
      . apply Set.not_subset.mpr;
        use A;
        constructor;
        . apply FormulaFinset.iff_mem_prebox_mem.mpr;
          apply hT.1;
          simp;
        . sorry;
          -- grind [ExpandedSequent.not_mem_both (S := S) (A := A)]
      . intro B hB;
        apply hT.1;
        grind;
      . exact ih.2 $ hT.2 (by simp);
  | _ => sorry; -- grind;

lemma truthlemma_ant : A ∈ S.1.1 → S ⊩ A := truthlemma.1
lemma truthlemma_suc : A ∈ S.1.2 → ¬S ⊩ A := truthlemma.2

theorem completeness {S : Sequent} (h : ∀ {κ : Type 0}, [Nonempty κ] → ∀ M : Model κ, [M.IsFiniteGL] → M ⊧ S) : ⊢ᵍ S := by
  contrapose! h;
  replace h : Fact (⊬ᵍ S) := ⟨iff_unprovableGentzen_isEmpty_ProofGentzen.mpr h⟩;
  use (ExpandedSequent S), inferInstance, (countermodelOf S);
  constructor;
  . infer_instance;
  . dsimp [Model.ValidateSequent, Model.World.ForcesSequent];
    push Not;
    use (ExpandedSequent.lindenbaum S (S₀ := S) (by grind) (Fact.elim inferInstance));
    constructor;
    . intro C hC; exact truthlemma_ant $ ExpandedSequent.subset_lindenbaum S _ _ |>.1 hC;
    . intro D hD; exact truthlemma_suc $ ExpandedSequent.subset_lindenbaum S _ _ |>.2 hD;

end Kripke

theorem deduction_theorem : ⊢ᵍ (insert A Γ ⟹ {B}) ↔ ⊢ᵍ (Γ ⟹ {A 🡒 B}) := by
  constructor;
  . intro h;
    apply Kripke.completeness;
    intro κ _ M _ x _;
    use A 🡒 B;
    constructor;
    . simp;
    . intro hA;
      exact (Model.World.forced_succ_singleton_sequent.mp $ Kripke.finite_soundness h M x) (by grind);
  . intro h;
    apply Kripke.completeness;
    intro κ _ M _ x;
    apply Model.World.forced_succ_singleton_sequent.mpr;
    intro H;
    exact (Model.World.forced_succ_singleton_sequent.mp $ Kripke.finite_soundness h M x) (by grind) (by grind);

end ProvableGentzen
