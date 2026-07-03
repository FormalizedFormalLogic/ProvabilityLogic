module

public import SeqPL.Logic.GL.CIP
public import SeqPL.Logic.S.GL

@[expose]
public section

universe u
variable {α : Type u}


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
