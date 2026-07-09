module

public import SeqPL.Gentzen.Maehara
public import SeqPL.Gentzen.WithCut
public import SeqPL.Formula.Letterless
public import SeqPL.Formula.Substitution
public import SeqPL.Kripke.Overwrite

/-!
# Fixed point theorem for GL via Gentzen-style sequent calculus

Following Sambin & Valentini (1982) "The modal logic of provability. The sequential approach",
Section 4, we prove the fixed point theorem for GL using the cut-free sequent calculus
`ProofGentzen` and the Maehara interpolation developed in `SeqPL.Gentzen.Maehara`.

Main ingredients:
- `Formula.ModalizedIn`: `p` occurs only in the scope of `□` in `A`.
- `ProvableGentzen.subst`: the calculus is closed under substitution.
- `ProvableGentzen.ruleLoeb`: Löb's rule is admissible (via cut admissibility).
- `ProvableGentzen.remove_modalized_atom_ant`/`suc` (SV82, Corollary 3.8):
  a modalized atom can be removed from a provable sequent.
  Instead of SV82's proof-theoretic argument via the decision procedure, we give a
  semantic proof: flip the valuation of `p` at a single world of a finite countermodel;
  since GL-models are transitive and irreflexive, this does not affect formulas in which
  `p` is modalized.
- `ProvableGentzen.fixpoint_uniqueness` (SV82, Lemma 4.3, UF): proved semantically via
  completeness and converse well-founded induction.
- `ProvableGentzen.fixpoint_existence` (SV82, Theorem 4.4): via Maehara interpolation.
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace Formula

variable {p q : α} {A B C : Formula α}

/-- `p` occurs only in the scope of `□` in `A` (SV82: "`p` is modalized in `A`"). -/
@[grind]
def ModalizedIn (p : α) : Formula α → Prop
  | #a    => a ≠ p
  | ⊥     => True
  | A 🡒 B => A.ModalizedIn p ∧ B.ModalizedIn p
  | □_    => True

lemma ModalizedIn.of_not_mem_atoms (h : p ∉ A.atoms) : A.ModalizedIn p := by
  induction A <;> grind [atoms]

omit [DecidableEq α] in
@[simp] lemma ModalizedIn.box : (□A).ModalizedIn p := by simp [ModalizedIn]

/-- Substituting fresh `q` for a modalized `p` yields a formula in which `q` is modalized. -/
lemma ModalizedIn.subst_single (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    (A⟦p ↦ #q⟧).ModalizedIn q := by
  induction A <;> grind [atoms, ModalizedIn]

end Formula


namespace Model

open Formula

variable [Nonempty κ] {M : Model κ α} {p q : α} {A B : Formula α}

section

variable {x : M.World}

/-- If `p` and `q` have the same valuation at `x` and all worlds above `x`,
then substituting `q` for `p` does not change forcing at `x`. Requires transitivity. -/
lemma World.forces_subst_single_iff_of_agree [IsTrans _ M.Rel] (B : Formula α) :
    ∀ x : M.World, (∀ w : M.World, (w = x ∨ x ≺ w) → (M.Val w p ↔ M.Val w q)) →
      (x ⊩ B⟦p ↦ #q⟧ ↔ x ⊩ B) := by
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
    x ⊩ B⟦p ↦ #q⟧ ↔ x ⊩ B := by
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

/-- Semantic core of the uniqueness of fixed points (SV82, Lemma 4.3):
if `A 🡘 p` and `A⟦p ↦ q⟧ 🡘 q` hold at `x` and hereditarily above `x`,
then `p` and `q` agree at `x` and hereditarily above `x`.
Proved by converse well-founded induction. -/
lemma World.val_iff_of_fixpoints [M.IsGL] (hA : A.ModalizedIn p)
    (h₁ : ∀ y : M.World, (y = x ∨ x ≺ y) → (y ⊩ A ↔ M.Val y p))
    (h₂ : ∀ y : M.World, (y = x ∨ x ≺ y) → (y ⊩ A⟦p ↦ #q⟧ ↔ M.Val y q)) :
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
    calc M.Val y p ↔ y ⊩ A := (h₁ y hy).symm
      _ ↔ y ⊩ A⟦p ↦ #q⟧ := (forces_subst_single_iff_of_agree_succ A hsucc hA).symm
      _ ↔ M.Val y q := h₂ y hy

end

namespace overwrite

variable {t : κ} {v : Prop}

omit [DecidableEq α] in
/-- Forcing of formulas in which `p` is modalized is unchanged at `t` itself.
Requires transitivity and irreflexivity: `t` is never reachable from itself. -/
lemma forces_iff_of_modalized [IsTrans _ M.Rel] [Std.Irrefl M.Rel] (B : Formula α)
    (hB : B.ModalizedIn p) :
    Model.World.Forces (M := M.overwrite t p v) t B ↔ Model.World.Forces (M := M) t B := by
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


namespace ProvableGentzen

open Formula

variable {Γ Δ : FormulaFinset α} {A B D : Formula α} {p q : α}

/-! ### Substitution closure (GL.typ, Proposition 1.2) -/

/-- `ProofGentzen` is closed under substitution. -/
theorem subst (s : Substitution α α) {S : Sequent α} (h : ⊢ᵍ S) :
    ⊢ᵍ (S.ant.image (·⟦s⟧) ⟹ S.suc.image (·⟦s⟧)) := by
  induction h with
  | axm A => simpa using axm (A⟦s⟧)
  | botL => simpa using botL
  | wkL h h' ih => exact wkL ih (Finset.image_subset_image h')
  | wkR h h' ih => exact wkR ih (Finset.image_subset_image h')
  | impL h₁ h₂ ih₁ ih₂ =>
    simp only [Finset.image_insert] at ih₁ ih₂ ⊢
    exact impL ih₁ ih₂
  | impR h ih =>
    simp only [Finset.image_insert] at ih ⊢
    exact impR ih
  | boxGL h ih =>
    have e : ∀ Γ : FormulaFinset α,
        (FormulaFinset.box Γ).image (·⟦s⟧) = FormulaFinset.box (Γ.image (·⟦s⟧)) := by
      intro Γ
      simp [FormulaFinset.box, Finset.image_image]
      rfl
    simp only [Finset.image_insert, Finset.image_union, e, Finset.image_singleton] at ih ⊢
    exact boxGL (by simpa using ih)

/-! ### Admissibility of Löb's rule (GL.typ, rule Löb) -/

/-- Löb's rule is admissible in `ProofGentzen`, via admissibility of cut. -/
theorem ruleLoeb (h : ⊢ᵍ ((insert (□A) (Γ ∪ Γ.box)) ⟹ {A})) : ⊢ᵍ (Γ ∪ Γ.box ⟹ {A}) := by
  apply of_with_cut
  have h₁ : ⊢ᵍᶜ ((Γ ∪ Γ.box) ⟹ insert (□A) ∅) :=
    GentzenWithCutProvable.wkR
      (GentzenWithCutProvable.wkL (GentzenWithCutProvable.of_without_cut (boxGL h)) (by grind))
      (by grind)
  have h₂ : ⊢ᵍᶜ (insert (□A) (Γ ∪ Γ.box) ⟹ {A}) := GentzenWithCutProvable.of_without_cut h
  simpa using GentzenWithCutProvable.cut h₁ h₂

/-! ### Removing modalized atoms (SV82, Corollary 3.8; GL.typ, Lemma 3.9)

SV82 proves this by inspecting the proof-search tree of the decision procedure.
We give a semantic proof instead: take a finite countermodel of `Γ ⟹ Δ` with
countermodel world `x`, and overwrite the valuation of `p` at `x`. Since finite
GL-models are transitive and irreflexive, `x` is not reachable from itself, so the
truth values at `x` of formulas in which `p` is modalized are unchanged. -/

/-- SV82, Corollary 3.8 (antecedent case): if `⊢ᵍ p, Γ ⟹ Δ` and `p` is modalized
in all formulas of `Γ` and `Δ`, then `⊢ᵍ Γ ⟹ Δ`. -/
theorem remove_modalized_atom_ant
    (hΓ : ∀ C ∈ Γ, C.ModalizedIn p) (hΔ : ∀ C ∈ Δ, C.ModalizedIn p)
    (h : ⊢ᵍ (insert (#p) Γ ⟹ Δ)) : ⊢ᵍ (Γ ⟹ Δ) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  by_contra hsuc
  push Not at hsuc
  let M' := M.overwrite x p True
  have hM' : ∀ C, C.ModalizedIn p →
      (Model.World.Forces (M := M') x C ↔ Model.World.Forces (M := M) x C) :=
    fun C hC => Model.overwrite.forces_iff_of_modalized C hC
  obtain ⟨D, hD, hfD⟩ := Kripke.finite_soundness h M' x (by
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    . exact Model.overwrite.val_self.mpr trivial
    . exact (hM' C (hΓ C hC)).mpr (hant C hC))
  exact hsuc D hD ((hM' D (hΔ D hD)).mp hfD)

/-- SV82, Corollary 3.8 (succedent case): if `⊢ᵍ Γ ⟹ Δ, p` and `p` is modalized
in all formulas of `Γ` and `Δ`, then `⊢ᵍ Γ ⟹ Δ`. -/
theorem remove_modalized_atom_suc
    (hΓ : ∀ C ∈ Γ, C.ModalizedIn p) (hΔ : ∀ C ∈ Δ, C.ModalizedIn p)
    (h : ⊢ᵍ (Γ ⟹ insert (#p) Δ)) : ⊢ᵍ (Γ ⟹ Δ) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  by_contra hsuc
  push Not at hsuc
  let M' := M.overwrite x p False
  have hM' : ∀ C, C.ModalizedIn p →
      (Model.World.Forces (M := M') x C ↔ Model.World.Forces (M := M) x C) :=
    fun C hC => Model.overwrite.forces_iff_of_modalized C hC
  obtain ⟨D, hD, hfD⟩ := Kripke.finite_soundness h M' x
    (fun C hC => (hM' C (hΓ C hC)).mpr (hant C hC))
  rcases Finset.mem_insert.mp hD with rfl | hD
  . exact Model.overwrite.val_self.mp hfD
  . exact hsuc D hD ((hM' D (hΔ D hD)).mp hfD)

/-! ### Auxiliary sequent-calculus lemmas -/

/-- Introduce `🡘` on the right from both implications. -/
lemma iffR (h₁ : ⊢ᵍ (insert A Γ ⟹ {B})) (h₂ : ⊢ᵍ (insert B Γ ⟹ {A})) : ⊢ᵍ (Γ ⟹ {A 🡘 B}) := by
  have e : ({A 🡘 B} : FormulaFinset α) = insert ((A 🡒 B) ⋏ (B 🡒 A)) ∅ := by rfl
  rw [e]
  apply andR
  . exact impR (by simpa using h₁)
  . exact impR (by simpa using h₂)

/-! ### Uniqueness of fixed points (SV82, Lemma 4.3; GL.typ, Lemma 3.8)

Proved semantically via completeness and converse well-founded induction
(`Model.World.val_iff_of_fixpoints`). -/

/-- SV82, Lemma 4.3 (UF): fixed points are unique. -/
theorem fixpoint_uniqueness (hA : A.ModalizedIn p) :
    ⊢ᵍ ({⊡(A 🡘 #p), ⊡((A⟦p ↦ #q⟧) 🡘 #q)} ⟹ {(#p : Formula α) 🡘 #q}) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  have h₁ : x ⊩ ⊡(A 🡘 #p) := hant _ (by simp)
  have h₂ : x ⊩ ⊡((A⟦p ↦ #q⟧) 🡘 #q) := hant _ (by simp)
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

/-! ### Existence of fixed points (SV82, Theorem 4.4; GL.typ, Lemma 3.10) -/

/-- The premise sequent for the interpolation argument, proved semantically:
`p, A, □(A 🡘 p), □(A' 🡘 q) ⟹ q, A'` where `A' = A⟦p ↦ q⟧`. -/
lemma fixpoint_premise (hA : A.ModalizedIn p) :
    ⊢ᵍ ({#p, A, □(A 🡘 #p), □((A⟦p ↦ #q⟧) 🡘 #q)} ⟹ {(#q : Formula α), A⟦p ↦ #q⟧}) := by
  apply Kripke.completeness
  intro κ _ M _ x hant
  by_contra hsuc
  push Not at hsuc
  have hxp : x ⊩ (#p : Formula α) := hant _ (by simp)
  have hxA : x ⊩ A := hant _ (by simp)
  have hbox₁ : x ⊩ □(A 🡘 #p) := hant _ (by simp)
  have hbox₂ : x ⊩ □((A⟦p ↦ #q⟧) 🡘 #q) := hant _ (by simp)
  have hxq : ¬x ⊩ (#q : Formula α) := hsuc _ (by simp)
  have hxA' : ¬x ⊩ A⟦p ↦ #q⟧ := hsuc _ (by simp)
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
    -- `□(A' 🡘 q)` contains `q`, whereas `#p`, `A`, `□(A 🡘 p)` do not (as `p ≠ q`, `q ∉ A.atoms`)
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

/-- SV82, Theorem 4.4 (existence): `⊢ᵍ ∅ ⟹ A⟦p ↦ D⟧ 🡘 D` for the constructed `D`. -/
theorem fixpoint_existence (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ⊢ᵍ ((∅ : FormulaFinset α) ⟹
      {(A⟦p ↦ fixpointFormula hpq hA hq⟧) 🡘 fixpointFormula hpq hA hq}) := by
  set D := fixpointFormula hpq hA hq with hD
  have hD' : interpolant (fixpointPartition hpq hq) (fixpoint_premise hA) = D := by rw [hD]; rfl
  have hpD : p ∉ D.atoms := fun h => by simpa using fixpointFormula_atoms hpq hA hq h
  have hqD : q ∉ D.atoms := fun h => hq (Finset.mem_sdiff.mp (fixpointFormula_atoms hpq hA hq h)).1
  -- (1) `⊢ᵍ p, A, □(A 🡘 p) ⟹ D` (interpolant, antecedent side)
  have h₁ : ⊢ᵍ ((insert (#p) {A, □(A 🡘 #p)}) ⟹ ({D} : FormulaFinset α)) := by
    have := interpolant_provable_ant (P := fixpointPartition hpq hq) (h := fixpoint_premise hA)
    rw [hD'] at this
    simpa [fixpointPartition] using this
  -- (2) `⊢ᵍ D, □(A' 🡘 q) ⟹ q, A'` (interpolant, succedent side)
  have h₂ : ⊢ᵍ ((insert D {□((A⟦p ↦ #q⟧) 🡘 #q)}) ⟹
      insert (#q) ({A⟦p ↦ #q⟧} : FormulaFinset α)) := by
    have := interpolant_provable_suc (P := fixpointPartition hpq hq) (h := fixpoint_premise hA)
    rw [hD'] at this
    simpa [fixpointPartition] using this
  -- (4) remove the modalized `p` from (1) (SV82, Corollary 3.8)
  have h₄ : ⊢ᵍ (({A, □(A 🡘 #p)} : FormulaFinset α) ⟹ {D}) := by
    apply remove_modalized_atom_ant (p := p) ?_ ?_ h₁
    . intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      . exact hA
      . rw [Finset.mem_singleton.mp hC]
        exact ModalizedIn.box
    . intro C hC
      rw [Finset.mem_singleton.mp hC]
      exact ModalizedIn.of_not_mem_atoms hpD
  -- (5) remove the modalized `q` from (2) (SV82, Corollary 3.8)
  have h₅ : ⊢ᵍ ((insert D {□((A⟦p ↦ #q⟧) 🡘 #q)}) ⟹ ({A⟦p ↦ #q⟧} : FormulaFinset α)) := by
    apply remove_modalized_atom_suc (p := q) ?_ ?_ h₂
    . intro C hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      . exact ModalizedIn.of_not_mem_atoms hqD
      . rw [Finset.mem_singleton.mp hC]
        exact ModalizedIn.box
    . intro C hC
      rw [Finset.mem_singleton.mp hC]
      exact hA.subst_single hq
  -- (6) substitute `q ↦ p` in (5); the calculus is closed under substitution
  have h₆ : ⊢ᵍ ((insert D {□(A 🡘 #p)}) ⟹ ({A} : FormulaFinset α)) := by
    have := subst (Substitution.single q (#p)) h₅
    simpa [Finset.image_insert, subst_single_cancel hq,
      subst_single_eq_self_of_not_mem_atoms hqD] using this
  -- (7) glue (4) and (6) into `⊢ᵍ □(A 🡘 p) ⟹ A 🡘 D`
  have h₇ : ⊢ᵍ (({□(A 🡘 #p)} : FormulaFinset α) ⟹ {A 🡘 D}) := iffR h₄ h₆
  -- (8) substitute `p ↦ D`
  have h₈ : ⊢ᵍ (({□((A⟦p ↦ D⟧) 🡘 D)} : FormulaFinset α) ⟹ {(A⟦p ↦ D⟧) 🡘 D}) := by
    have := subst (Substitution.single p D) h₇
    simpa [subst_single_eq_self_of_not_mem_atoms hpD] using this
  -- (9) apply Löb's rule
  have := ruleLoeb (Γ := (∅ : FormulaFinset α)) (A := (A⟦p ↦ D⟧) 🡘 D)
    (by simpa [FormulaFinset.box] using h₈)
  simpa [FormulaFinset.box] using this

end ProvableGentzen


namespace LogicGL

open Formula

/-- The fixed point theorem for GL (SV82, Theorem 4.4; GL.typ, final theorem):
for `p` modalized in `A` and a fresh atom `q`, there effectively exists a fixed point `D`
of `A` containing only atoms of `A` other than `p`. -/
theorem fixpointTheorem {A : Formula α} {p q : α}
    (hpq : p ≠ q) (hA : A.ModalizedIn p) (hq : q ∉ A.atoms) :
    ∃ D : Formula α, D.atoms ⊆ A.atoms \ {p} ∧ ((A⟦p ↦ D⟧) 🡘 D) ∈ LogicGL :=
  ⟨ProvableGentzen.fixpointFormula hpq hA hq,
    ProvableGentzen.fixpointFormula_atoms hpq hA hq,
    LogicGL.iff_provableGentzen.mpr (ProvableGentzen.fixpoint_existence hpq hA hq)⟩

end LogicGL

end
