module

public import ProvabilityLogic.Formula.Modalized
public import ProvabilityLogic.Gentzen.GL.Maehara
public import ProvabilityLogic.Kripke.Overwrite

/-!
# Fixed point theorem for GL via Gentzen-style sequent calculus

`LogicGL.fixpointTheorem`: a formula `A` in which the atom `p` is modalized — i.e. occurs only
within the scope of `□`, `Formula.ModalizedIn` — has a fixed point, unique up to GL-provable
equivalence. Existence is obtained by extracting the fixed point as a Maehara interpolant in the
cut-free sequent calculus `ProofGentzen`, and uniqueness semantically via Kripke completeness.

- [SV82, Section 4, Corollary 3.8, Lemma 4.3, Theorem 4.4]
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace Model

open Formula

variable [Nonempty κ] {M : Model κ α} {p q : α} {A B : Formula α}

section

variable {x : M.World}

/-- If `p` and `q` have the same valuation at `x` and all worlds above `x`,
then substituting `q` for `p` does not change forcing at `x`. Requires transitivity. -/
lemma World.forces_subst_single_iff_of_agree [IsTrans _ M.Rel] (B : Formula α) :
    ∀ x : M.World, (∀ w : M.World, (w = x ∨ x ≺ w) → (M.Val w p ↔ M.Val w q)) →
      (x ⊩[_] B⟦p ↦ #q⟧ ↔ x ⊩[_] B) := by
  induction B with
  | atom a =>
    intro x h
    by_cases hap : a = p
    . subst hap
      simpa [Forces] using (h x (.inl rfl)).symm
    . simp [hap]
  | bot => simp
  | imp A B ihA ihB =>
    intro x h
    have := ihA x h
    have := ihB x h
    grind
  | box A ih =>
    intro x h
    simp only [subst_box, forces_box]
    have hy : ∀ y : M.World, x ≺ y → ∀ w : M.World, (w = y ∨ y ≺ w) → (M.Val w p ↔ M.Val w q) := by
      intro y Rxy w hw
      apply h w
      rcases hw with rfl | h'
      . exact .inr Rxy
      . exact .inr (IsTrans.trans _ _ _ Rxy h')
    constructor
    . intro hf y Rxy
      exact (ih y (hy y Rxy)).mp (hf y Rxy)
    . intro hf y Rxy
      exact (ih y (hy y Rxy)).mpr (hf y Rxy)

/-- If `p` is modalized in `B` and `p`, `q` agree at all worlds strictly above `x`,
then substituting `q` for `p` does not change forcing at `x`. -/
lemma World.forces_subst_single_iff_of_agree_succ [IsTrans _ M.Rel] (B : Formula α)
    (h : ∀ w : M.World, x ≺ w → (M.Val w p ↔ M.Val w q)) (hB : B.ModalizedIn p) :
    x ⊩[_] B⟦p ↦ #q⟧ ↔ x ⊩[_] B := by
  induction B with
  | atom a =>
    have : a ≠ p := hB
    simp [this]
  | bot => simp
  | imp A B ihA ihB =>
    obtain ⟨hA', hB'⟩ := hB
    have := ihA hA'
    have := ihB hB'
    grind
  | box A _ =>
    simp only [subst_box, forces_box]
    have hy : ∀ y : M.World, x ≺ y → ∀ w : M.World, (w = y ∨ y ≺ w) → (M.Val w p ↔ M.Val w q) := by
      intro y Rxy w hw
      apply h w
      rcases hw with rfl | h'
      . exact Rxy
      . exact IsTrans.trans _ _ _ Rxy h'
    constructor
    . intro hf y Rxy
      exact (forces_subst_single_iff_of_agree A y (hy y Rxy)).mp (hf y Rxy)
    . intro hf y Rxy
      exact (forces_subst_single_iff_of_agree A y (hy y Rxy)).mpr (hf y Rxy)

/-- Semantic core of the uniqueness of fixed points:
if `A 🡘 p` and `A⟦p ↦ q⟧ 🡘 q` hold at `x` and hereditarily above `x`,
then `p` and `q` agree at `x` and hereditarily above `x`.

- [SV82, Lemma 4.3]
-/
lemma World.val_iff_of_fixpoints [M.IsGL] (hA : A.ModalizedIn p)
    (h₁ : ∀ y : M.World, (y = x ∨ x ≺ y) → (y ⊩[_] A ↔ M.Val y p))
    (h₂ : ∀ y : M.World, (y = x ∨ x ≺ y) → (y ⊩[_] A⟦p ↦ #q⟧ ↔ M.Val y q)) :
    ∀ y : M.World, (y = x ∨ x ≺ y) → (M.Val y p ↔ M.Val y q) := by
  intro y
  induction y using WellFounded.induction (IsConverseWellFounded.cwf (rel := M.Rel)) with
  | _ y ih =>
    intro hy
    have hsucc : ∀ w : M.World, y ≺ w → (M.Val w p ↔ M.Val w q) := by
      intro w Ryw
      apply ih w Ryw
      rcases hy with rfl | h'
      . exact .inr Ryw
      . exact .inr (IsTrans.trans _ _ _ h' Ryw)
    calc M.Val y p ↔ y ⊩[_] A := (h₁ y hy).symm
      _ ↔ y ⊩[_] A⟦p ↦ #q⟧ := (forces_subst_single_iff_of_agree_succ A hsucc hA).symm
      _ ↔ M.Val y q := h₂ y hy

end

namespace overwrite

variable {t : κ} {v : Prop}

omit [DecidableEq α] in
/-- Forcing of formulas in which `p` is modalized is unchanged at `t` itself.
Requires transitivity and irreflexivity: `t` is never reachable from itself. -/
lemma forces_iff_of_modalized [IsTrans _ M.Rel] [Std.Irrefl M.Rel] (B : Formula α)
    (hB : B.ModalizedIn p) :
    t ⊩[M.overwrite t p v] B ↔ t ⊩[M] B := by
  induction B with
  | atom a => exact val_of_ne_atom hB
  | bot => simp [Model.World.Forces]
  | imp A B ihA ihB =>
    obtain ⟨hA', hB'⟩ := hB
    have := ihA hA'
    have := ihB hB'
    simp only [Model.World.Forces]
    grind
  | box A _ =>
    simp only [Model.World.Forces]
    have hy : ∀ y : κ, M.Rel t y → y ≠ t ∧ ¬M.Rel y t := by
      intro y Rty
      constructor
      . rintro rfl; exact Std.Irrefl.irrefl _ Rty
      . intro h'; exact Std.Irrefl.irrefl t (IsTrans.trans _ _ _ Rty h')
    constructor
    . intro hf y Rty
      exact (forces_iff_of_not_rel A y (hy y Rty).1 (hy y Rty).2).mp (hf y Rty)
    . intro hf y Rty
      exact (forces_iff_of_not_rel A y (hy y Rty).1 (hy y Rty).2).mpr (hf y Rty)

end overwrite

end Model


namespace LogicGL

namespace ProvableGentzen

open Formula

variable {Γ Δ : FormulaFinset α} {A B D E : Formula α} {p q : α}

/-! ### Removing modalized atoms

- [SV82, Corollary 3.8]
-/

/-- Antecedent case of removing a modalized atom.

- [SV82, Corollary 3.8]
-/
theorem remove_modalized_atom_ant
    (hΓ : ∀ C ∈ Γ, C.ModalizedIn p) (hΔ : ∀ C ∈ Δ, C.ModalizedIn p)
    (h : ⊢ᵍ[GL] (insert (#p) Γ ⟹ Δ)) : ⊢ᵍ[GL] (Γ ⟹ Δ) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  by_contra hsuc
  push Not at hsuc
  let M' := M.overwrite x p True
  have hM' : ∀ C : Formula α, C.ModalizedIn p →
      (x ⊩[M'] C ↔ x ⊩[M] C) :=
    fun C hC => Model.overwrite.forces_iff_of_modalized C hC
  obtain ⟨D, hD, hfD⟩ := Kripke.finite_soundness h M' x (by
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    . exact Model.overwrite.val_self.mpr trivial
    . exact (hM' C (hΓ C hC)).mpr (hant C hC))
  exact hsuc D hD ((hM' D (hΔ D hD)).mp hfD)

/-- Succedent case of removing a modalized atom.

- [SV82, Corollary 3.8]
-/
theorem remove_modalized_atom_suc
    (hΓ : ∀ C ∈ Γ, C.ModalizedIn p) (hΔ : ∀ C ∈ Δ, C.ModalizedIn p)
    (h : ⊢ᵍ[GL] (Γ ⟹ insert (#p) Δ)) : ⊢ᵍ[GL] (Γ ⟹ Δ) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  by_contra hsuc
  push Not at hsuc
  let M' := M.overwrite x p False
  have hM' : ∀ C : Formula α, C.ModalizedIn p →
      (x ⊩[M'] C ↔ x ⊩[M] C) :=
    fun C hC => Model.overwrite.forces_iff_of_modalized C hC
  obtain ⟨D, hD, hfD⟩ := Kripke.finite_soundness h M' x
    (fun C hC => (hM' C (hΓ C hC)).mpr (hant C hC))
  rcases Finset.mem_insert.mp hD with rfl | hD
  . exact Model.overwrite.val_self.mp hfD
  . exact hsuc D hD ((hM' D (hΔ D hD)).mp hfD)

/-! ### Uniqueness of fixed points

- [SV82, Lemma 4.3]
-/

/-- Fixed points are unique.

- [SV82, Lemma 4.3]
-/
theorem fixpoint_uniqueness (hA : A.ModalizedIn p) :
    ⊢ᵍ[GL] ({⊡(A 🡘 #p), ⊡((A⟦p ↦ #q⟧) 🡘 #q)} ⟹ {(#p : Formula α) 🡘 #q}) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  have h₁ : x ⊩[_] ⊡(A 🡘 #p) := hant _ (by simp)
  have h₂ : x ⊩[_] ⊡((A⟦p ↦ #q⟧) 🡘 #q) := hant _ (by simp)
  use (#p : Formula α) 🡘 #q, by simp
  have hval := Model.World.val_iff_of_fixpoints (x := x) (q := q) hA
    (by
      intro y hy
      rcases hy with rfl | hy
      . have := Model.World.forces_boxdot.mp h₁ |>.1; grind
      . have := Model.World.forces_boxdot.mp h₁ |>.2 y hy; grind)
    (by
      intro y hy
      rcases hy with rfl | hy
      . have := Model.World.forces_boxdot.mp h₂ |>.1; grind
      . have := Model.World.forces_boxdot.mp h₂ |>.2 y hy; grind)
    x (.inl rfl)
  grind

/-- Uniqueness for arbitrary formulas `D` and `E` in place of the atoms `p` and `q`. Substituting
`p ↦ D` before `q ↦ E` is what makes a freshness assumption on `E` unnecessary.

- [SV82, Lemma 4.3]
-/
theorem fixpoint_unique (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms)
    (hqD : q ∉ D.atoms) :
    ⊢ᵍ[GL] ({⊡((A⟦p ↦ D⟧) 🡘 D), ⊡((A⟦p ↦ E⟧) 🡘 E)} ⟹ {D 🡘 E}) := by
  have hpA : p ∉ (A⟦p ↦ #q⟧).atoms := by
    intro h;
    rcases Finset.mem_union.mp (atoms_subst_single_subset h) with h | h;
    . simp at h;
    . simp [atoms] at h; exact hpq h;
  have hqA : q ∉ (A⟦p ↦ D⟧).atoms := by
    intro h;
    rcases Finset.mem_union.mp (atoms_subst_single_subset h) with h | h;
    . exact hq (Finset.mem_sdiff.mp h).1;
    . exact hqD h;
  have h₁ : ⊢ᵍ[GL] ({⊡((A⟦p ↦ D⟧) 🡘 D), ⊡((A⟦p ↦ #q⟧) 🡘 #q)} ⟹ {D 🡘 (#q : Formula α)}) := by
    have := subst (Substitution.single p D) (fixpoint_uniqueness (q := q) hA);
    simpa [Finset.image_insert, subst_single_eq_self_of_not_mem_atoms hpA, hpq.symm] using this;
  have := subst (Substitution.single q E) h₁;
  simpa [Finset.image_insert, subst_single_eq_self_of_not_mem_atoms hqA,
    subst_single_eq_self_of_not_mem_atoms hqD, subst_single_subst_single hq] using this;

/-! ### Existence of fixed points

- [SV82, Theorem 4.4]
-/

/-- The premise sequent from which the fixed point is extracted by interpolation. -/
lemma fixpoint_premise (hA : A.ModalizedIn p) :
    ⊢ᵍ[GL] ({#p, A, □(A 🡘 #p), □((A⟦p ↦ #q⟧) 🡘 #q)} ⟹ {(#q : Formula α), A⟦p ↦ #q⟧}) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  by_contra hsuc
  push Not at hsuc
  have hxp : x ⊩[_] (#p : Formula α) := hant _ (by simp)
  have hxA : x ⊩[_] A := hant _ (by simp)
  have hbox₁ : x ⊩[_] □(A 🡘 #p) := hant _ (by simp)
  have hbox₂ : x ⊩[_] □((A⟦p ↦ #q⟧) 🡘 #q) := hant _ (by simp)
  have hxq : ¬x ⊩[_] (#q : Formula α) := hsuc _ (by simp)
  have hxA' : ¬x ⊩[_] A⟦p ↦ #q⟧ := hsuc _ (by simp)
  have hval := Model.World.val_iff_of_fixpoints (x := x) (q := q) hA
    (by
      intro y hy
      rcases hy with rfl | hy
      . grind
      . have := hbox₁ y hy; grind)
    (by
      intro y hy
      rcases hy with rfl | hy
      . grind
      . have := hbox₂ y hy; grind)
    x (.inl rfl)
  grind

/-- The partition of the premise sequent used to extract the fixed point. -/
def fixpointPartition (hpq : p ≠ q) (hq : q ∉ A.atoms) :
    PartitionOf (({#p, A, □(A 🡘 #p), □((A⟦p ↦ #q⟧) 🡘 #q)} : FormulaFinset α)
      ⟹ ({(#q : Formula α), A⟦p ↦ #q⟧} : FormulaFinset α)) where
  Γ₁ := {#p, A, □(A 🡘 #p)}
  Γ₂ := {□((A⟦p ↦ #q⟧) 🡘 #q)}
  Δ₁ := ∅
  Δ₂ := {(#q : Formula α), A⟦p ↦ #q⟧}
  Γ_ant := by grind
  Δ_suc := by simp
  Γ_disj := by
    rw [Finset.disjoint_singleton_right]
    -- `q` occurs in `□((A⟦p ↦ q⟧) 🡘 q)` but not in `#p`, `A`, `□(A 🡘 p)`, as `p ≠ q` and
    -- `q ∉ A.atoms`
    have hqmem : q ∈ (□((A⟦p ↦ #q⟧) 🡘 #q)).atoms := by simp [Formula.atoms]
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | hmem
    . exact absurd h (by simp)
    rcases Finset.mem_insert.mp hmem with h | hmem
    . exact hq (h ▸ hqmem)
    . rw [Finset.mem_singleton] at hmem
      have hqA : q ∉ (□(A 🡘 #p)).atoms := by
        simp only [Formula.atoms, Finset.mem_union]
        grind
      exact hqA (hmem ▸ hqmem)
  Δ_disj := by simp

/-- The fixed point of `A`, extracted as the Maehara interpolant of the premise sequent. -/
noncomputable def fixpointFormula (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    Formula α := interpolant (fixpointPartition hpq hq) (fixpoint_premise hA)

lemma fixpointFormula_atoms (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    (fixpointFormula hpq hA hq).atoms ⊆ A.atoms \ {p} := by
  intro a ha
  have h := interpolant_atoms (P := fixpointPartition hpq hq) (h := fixpoint_premise hA) ha
  have hA' := atoms_subst_single_subset (A := A) (p := p) (B := (#q : Formula α))
  simp only [fixpointPartition, FormulaFinset.atoms_insert, FormulaFinset.atoms_singleton,
    FormulaFinset.atoms_empty, Formula.atoms] at h
  grind [Formula.atoms]

/-- Existence: `fixpointFormula` is a fixed point of `A`.

- [SV82, Theorem 4.4]
-/
theorem fixpoint_existence (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ⊢ᵍ[GL] ((∅ : FormulaFinset α) ⟹
      {(A⟦p ↦ fixpointFormula hpq hA hq⟧) 🡘 fixpointFormula hpq hA hq}) := by
  set D := fixpointFormula hpq hA hq with hD
  have hD' : interpolant (fixpointPartition hpq hq) (fixpoint_premise hA) = D := by rw [hD]; rfl
  have hpD : p ∉ D.atoms := fun h => by simpa using fixpointFormula_atoms hpq hA hq h
  have hqD : q ∉ D.atoms := fun h => hq (Finset.mem_sdiff.mp (fixpointFormula_atoms hpq hA hq h)).1
  -- the two halves of the interpolation of `fixpoint_premise` along `fixpointPartition`
  have h₁ : ⊢ᵍ[GL] ((insert (#p) {A, □(A 🡘 #p)}) ⟹ ({D} : FormulaFinset α)) := by
    have := interpolant_provable_ant (P := fixpointPartition hpq hq) (h := fixpoint_premise hA)
    rw [hD'] at this
    simpa [fixpointPartition] using this
  have h₂ : ⊢ᵍ[GL] ((insert D {□((A⟦p ↦ #q⟧) 🡘 #q)}) ⟹
      insert (#q) ({A⟦p ↦ #q⟧} : FormulaFinset α)) := by
    have := interpolant_provable_suc (P := fixpointPartition hpq hq) (h := fixpoint_premise hA)
    rw [hD'] at this
    simpa [fixpointPartition] using this
  have h₄ : ⊢ᵍ[GL] (({A, □(A 🡘 #p)} : FormulaFinset α) ⟹ {D}) := by
    apply remove_modalized_atom_ant (p := p) ?_ ?_ h₁
    . intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      . exact hA
      . rw [Finset.mem_singleton.mp hC]
        exact ModalizedIn.box
    . intro C hC
      rw [Finset.mem_singleton.mp hC]
      exact ModalizedIn.of_not_mem_atoms hpD
  have h₅ : ⊢ᵍ[GL] ((insert D {□((A⟦p ↦ #q⟧) 🡘 #q)}) ⟹ ({A⟦p ↦ #q⟧} : FormulaFinset α)) := by
    apply remove_modalized_atom_suc (p := q) ?_ ?_ h₂
    . intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      . exact ModalizedIn.of_not_mem_atoms hqD
      . rw [Finset.mem_singleton.mp hC]
        exact ModalizedIn.box
    . intro C hC
      rw [Finset.mem_singleton.mp hC]
      exact hA.subst_single hq
  have h₆ : ⊢ᵍ[GL] ((insert D {□(A 🡘 #p)}) ⟹ ({A} : FormulaFinset α)) := by
    have := subst (Substitution.single q (#p)) h₅
    simpa [Finset.image_insert, subst_single_cancel hq,
      subst_single_eq_self_of_not_mem_atoms hqD] using this
  have h₇ : ⊢ᵍ[GL] (({□(A 🡘 #p)} : FormulaFinset α) ⟹ {A 🡘 D}) := iffR h₄ h₆
  have h₈ : ⊢ᵍ[GL] (({□((A⟦p ↦ D⟧) 🡘 D)} : FormulaFinset α) ⟹ {(A⟦p ↦ D⟧) 🡘 D}) := by
    have := subst (Substitution.single p D) h₇
    simpa [subst_single_eq_self_of_not_mem_atoms hpD] using this
  have := ruleLoeb (Γ := (∅ : FormulaFinset α)) (A := (A⟦p ↦ D⟧) 🡘 D)
    (by simpa [FormulaFinset.box] using h₈)
  simpa [FormulaFinset.box] using this

end ProvableGentzen


open Formula

variable {A D E : Formula α} {p q : α}

/-- Fixed points of a formula in which `p` is modalized are unique up to GL-provable equivalence.

- [SV82, Lemma 4.3]
-/
theorem fixpoint_unique (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms)
    (hqD : q ∉ D.atoms)
    (hD : ((A⟦p ↦ D⟧) 🡘 D) ∈ LogicGL) (hE : ((A⟦p ↦ E⟧) 🡘 E) ∈ LogicGL) :
    (D 🡘 E) ∈ LogicGL := by
  have hbd : ∀ {C : Formula α}, C ∈ LogicGL → ⊢ᵍᶜ[GL] ((∅ : FormulaFinset α) ⟹ insert (⊡C) ∅) := by
    intro C h;
    have h₁ : ⊢ᵍ[GL] ((∅ : FormulaFinset α) ⟹ insert C ∅) := by
      simpa using iff_provableGentzen.mp h;
    have h₂ : ⊢ᵍ[GL] ((∅ : FormulaFinset α) ⟹ insert (□C) ∅) := by
      simpa using ProvableGentzen.nec (iff_provableGentzen.mp h);
    exact GentzenWithCutProvable.of_without_cut (ProvableGentzen.andR h₁ h₂);
  apply iff_provableGentzen.mpr;
  apply ProvableGentzen.of_with_cut;
  have h₀ := GentzenWithCutProvable.of_without_cut
    (ProvableGentzen.fixpoint_unique (E := E) hpq hA hq hqD);
  have h₁ := GentzenWithCutProvable.cut (hbd hD) h₀;
  have h₂ : ⊢ᵍᶜ[GL] (((∅ : FormulaFinset α) ∪ ∅) ⟹ ((∅ : FormulaFinset α) ∪ {D 🡘 E})) :=
    GentzenWithCutProvable.cut (hbd hE) (by simpa using h₁);
  simpa using h₂;

/-- The fixed point theorem for GL. The witness is the explicit interpolant
`ProvableGentzen.fixpointFormula`, so the fixed point is obtained effectively; the fresh atom `q`
serves only as a placeholder in its construction.

- [SV82, Lemma 4.3, Theorem 4.4]
-/
theorem fixpointTheorem
    (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D : Formula α, D.atoms ⊆ A.atoms \ {p} ∧ ((A⟦p ↦ D⟧) 🡘 D) ∈ LogicGL ∧
      ∀ E : Formula α, ((A⟦p ↦ E⟧) 🡘 E) ∈ LogicGL → (D 🡘 E) ∈ LogicGL := by
  have h₁ := ProvableGentzen.fixpointFormula_atoms hpq hA hq;
  have h₂ := iff_provableGentzen.mpr (ProvableGentzen.fixpoint_existence hpq hA hq);
  have h₃ : q ∉ (ProvableGentzen.fixpointFormula hpq hA hq).atoms :=
    fun h => hq (Finset.mem_sdiff.mp (h₁ h)).1;
  exact ⟨_, h₁, h₂, fun E hE => fixpoint_unique hpq hA hq h₃ h₂ hE⟩;

end LogicGL

end
