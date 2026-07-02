module

public import SeqPL.Logic.GL.CIP
public import SeqPL.Logic.S.GL

@[expose]
public section

universe u
variable {α : Type u}


namespace Formula

variable [DecidableEq α] {A B : Formula α}

@[simp, grind =]
lemma atoms_and (A B : Formula α) : (A ⋏ B).atoms = A.atoms ∪ B.atoms := by
  simp [Formula.atoms]

/-- The atoms of a subformula `B` of `A` are contained in the atoms of `A`. -/
@[grind →]
lemma atoms_subset_of_mem_subfmls (h : B ∈ A.subfmls) : B.atoms ⊆ A.atoms := by
  induction A <;> grind [Formula.subfmls, Formula.atoms]

end Formula


private lemma atoms_lconj_subset [DecidableEq α] (L : FormulaList α) :
    (⋀L).atoms ⊆ L.toFinset.biUnion Formula.atoms := by
  match L with
  | [] => simp [FormulaList.conj, Formula.atoms, Formula.top, Formula.neg]
  | [A] => simp
  | A :: B :: L =>
    simp only [FormulaList.conj, Formula.atoms_and]
    have ih := atoms_lconj_subset (B :: L)
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [List.toFinset_cons, Finset.mem_biUnion]
      exact ⟨A, Finset.mem_insert_self _ _, hx⟩
    · obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp (ih hx)
      refine Finset.mem_biUnion.mpr ⟨y, ?_, hxy⟩
      simp only [List.toFinset_cons] at hy ⊢
      exact Finset.mem_insert_of_mem hy

namespace FormulaFinset

variable [DecidableEq α] {Γ Δ : FormulaFinset α} {A B : Formula α}

/-- The atoms of `⋀Γ` are contained in the atoms of `Γ`. -/
@[grind .]
lemma atoms_conj_subset (Γ : FormulaFinset α) : (⋀Γ).atoms ⊆ Γ.atoms := by
  have := atoms_lconj_subset Γ.toList
  simpa [FormulaFinset.conj, FormulaFinset.atoms] using this

end FormulaFinset


namespace ProvableHilbert

variable [DecidableEq α] {A B C D : Formula α}

/-- `⋀Γ ⋏ ⋀Δ` derives `⋀(Γ ∪ Δ)`. -/
@[grind <=]
lemma imp_fconj_union (Γ Δ : FormulaFinset α) : ⊢ʰ ((⋀Γ) ⋏ (⋀Δ)) 🡒 ⋀(Γ ∪ Δ) := by
  apply ProvableHilbert.Kripke.completeness
  intro κ _ M _ x
  grind

omit [DecidableEq α] in
/-- Combinatory reassociation of a conjunction: `(A ⋏ B) 🡒 (C 🡒 D)` derives `(A ⋏ C) 🡒 (B 🡒 D)`. -/
@[simp, grind .]
lemma imp_reassoc : ⊢ʰ ((A ⋏ B) 🡒 (C 🡒 D)) 🡒 ((A ⋏ C) 🡒 (B 🡒 D)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hAC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ A ⋏ C := DeducibleHilbert.ofContext (by grind)
  have hA : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andL) hAC
  have hC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andR) hAC
  have hB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ (A ⋏ B) 🡒 (C 🡒 D) :=
    DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hAB) hC

omit [DecidableEq α] in
/-- Elimination of a conjunction: `(A ⋏ B) 🡒 C` derives `A 🡒 (B 🡒 C)`. -/
@[simp, grind .]
lemma imp_uncurry_and : ⊢ʰ ((A ⋏ B) 🡒 C) 🡒 (A 🡒 (B 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind)
  have hB : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ (A ⋏ B) 🡒 C := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp himp hAB

omit [DecidableEq α] in
/-- Swapping antecedents: `A 🡒 (B 🡒 C)` derives `B 🡒 (A 🡒 C)`. -/
@[simp, grind .]
lemma imp_swap : ⊢ʰ (A 🡒 (B 🡒 C)) 🡒 (B 🡒 (A 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({A, B, A 🡒 (B 🡒 C)} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind)
  have hB : ({A, B, A 🡒 (B 🡒 C)} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have himp : ({A, B, A 🡒 (B 🡒 C)} : FormulaSet α) ⊢ʰ A 🡒 (B 🡒 C) := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hA) hB

end ProvableHilbert


namespace LogicS

variable [DecidableEq α] {A B : Formula α}

/-- `(A 🡒 B).subfmlsS` equals `A.subfmlsS ∪ B.subfmlsS`. -/
@[simp, grind =]
lemma subfmlsS_imp (A B : Formula α) : (A 🡒 B).subfmlsS = A.subfmlsS ∪ B.subfmlsS := by
  unfold Formula.subfmlsS
  rw [show (A 🡒 B).subfmls.prebox = A.subfmls.prebox ∪ B.subfmls.prebox from ?_, Finset.image_union]
  ext C
  simp [FormulaFinset.prebox, Formula.subfmls]

/-- The atoms of `⋀A.subfmlsS` are contained in the atoms of `A`. -/
@[grind .]
lemma atoms_fconj_subfmlsS_subset (A : Formula α) : (⋀A.subfmlsS).atoms ⊆ A.atoms := by
  apply subset_trans (FormulaFinset.atoms_conj_subset _)
  intro x hx
  simp only [Formula.subfmlsS, FormulaFinset.atoms, Finset.mem_biUnion, Finset.mem_image] at hx
  obtain ⟨_, ⟨C, hC, rfl⟩, hx⟩ := hx
  simp only [Formula.atoms, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact Formula.atoms_subset_of_mem_subfmls
      (Formula.subfmls_trans Formula.mem_subfmls_box (FormulaFinset.iff_mem_prebox_mem.mp hC)) hx
  · exact Formula.atoms_subset_of_mem_subfmls (FormulaFinset.iff_mem_prebox_mem.mp hC) hx

/--
  Lemma 1 (lifting `A 🡒 B ∈ LogicS` to GL, in reassociated form):
  `(⋀A.subfmlsS ⋏ A) 🡒 (⋀B.subfmlsS 🡒 B) ∈ LogicGL`.
-/
lemma provable_reassoc_of_provable_imp (h : (A 🡒 B) ∈ LogicS) :
    (((⋀A.subfmlsS) ⋏ A) 🡒 ((⋀B.subfmlsS) 🡒 B)) ∈ LogicGL := by
  have hGL : (⋀(A 🡒 B).subfmlsS 🡒 (A 🡒 B)) ∈ LogicGL := iff_provable_S_provable_GL.mp h
  rw [subfmlsS_imp] at hGL
  have hUnion : ⊢ʰ ((⋀A.subfmlsS) ⋏ (⋀B.subfmlsS)) 🡒 (A 🡒 B) :=
    ProvableHilbert.impTrans (ProvableHilbert.imp_fconj_union _ _) hGL
  exact ProvableHilbert.mdp ProvableHilbert.imp_reassoc hUnion

/--
  **The interpolant of Logic S's Craig interpolation theorem**: if `A 🡒 B ∈ LogicS`, there is a
  formula `C` whose atoms are contained in `A.atoms ∩ B.atoms`, such that `A 🡒 C ∈ LogicS` and
  `C 🡒 B ∈ LogicS`.
  Formalizes `Beklemishev1987` Theorem 2, derived from GL's Craig interpolation property
  (`LogicGL.interpolant`, `SeqPL/Gentzen/Maehara.lean`) and `iff_provable_S_provable_GL`
  (`Assertion 1`).
-/
noncomputable def interpolant (h : (A 🡒 B) ∈ LogicS) : Formula α :=
  LogicGL.interpolant (provable_reassoc_of_provable_imp h)

lemma interpolant_provable_ant (h : (A 🡒 B) ∈ LogicS) : (A 🡒 interpolant h) ∈ LogicS := by
  have hX : (((⋀A.subfmlsS) ⋏ A) 🡒 interpolant h) ∈ LogicGL :=
    LogicGL.interpolant_provable_ant (h := provable_reassoc_of_provable_imp h)
  have hP : (⋀A.subfmlsS 🡒 (A 🡒 interpolant h)) ∈ LogicGL :=
    ProvableHilbert.mdp ProvableHilbert.imp_uncurry_and hX
  exact Logic.sumQuasiNormal.mdp (provable_of_provable_GL hP) provable_fconj_subfmlsS

lemma interpolant_provable_suc (h : (A 🡒 B) ∈ LogicS) : (interpolant h 🡒 B) ∈ LogicS := by
  have hY : (interpolant h 🡒 ((⋀B.subfmlsS) 🡒 B)) ∈ LogicGL :=
    LogicGL.interpolant_provable_suc (h := provable_reassoc_of_provable_imp h)
  have hQ : (⋀B.subfmlsS 🡒 (interpolant h 🡒 B)) ∈ LogicGL :=
    ProvableHilbert.mdp ProvableHilbert.imp_swap hY
  exact Logic.sumQuasiNormal.mdp (provable_of_provable_GL hQ) provable_fconj_subfmlsS

lemma interpolant_atoms (h : (A 🡒 B) ∈ LogicS) : (interpolant h).atoms ⊆ A.atoms ∩ B.atoms := by
  have hAtoms := LogicGL.interpolant_atoms (h := provable_reassoc_of_provable_imp h)
  refine hAtoms.trans (Finset.inter_subset_inter ?_ ?_)
  · simp only [Formula.atoms_and, Finset.union_subset_iff]
    exact ⟨atoms_fconj_subfmlsS_subset A, subset_refl _⟩
  · simp only [Formula.atoms, Finset.union_subset_iff]
    exact ⟨atoms_fconj_subfmlsS_subset B, subset_refl _⟩

/--
  **Craig interpolation property** (`Beklemishev1987`, Theorem 2): `Logic S` has the Craig
  interpolation property.
-/
theorem CIP (h : (A 🡒 B) ∈ LogicS) : ∃ C : Formula α, (A 🡒 C) ∈ LogicS ∧ (C 🡒 B) ∈ LogicS ∧ C.atoms ⊆ A.atoms ∩ B.atoms :=
  ⟨interpolant h, interpolant_provable_ant h, interpolant_provable_suc h, interpolant_atoms h⟩

end LogicS

end
