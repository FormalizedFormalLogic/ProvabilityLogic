module

public import ProvabilityLogic.Logic.GLPoint3.Basic
public import ProvabilityLogic.Gentzen.GLPoint3.Kripke
public import ProvabilityLogic.Kripke.Reindex

/-!
# Soundness and Kripke completeness of `LogicGLPoint3`

This file bundles: the translation from `GL.3` Gentzen-provability to `LogicGLPoint3`-membership
(Step M, `LogicGLPoint3.of_provableGentzen`/`of_provableGentzen_formula`); the soundness of
`LogicGLPoint3` over finite linear GL models (`LogicGLPoint3.sound`); and, combining both with the
sequent calculus results of `ProvabilityLogic/Gentzen/GLPoint3/Kripke.lean`, the packaged Kripke completeness
theorem `LogicGLPoint3.provability_TFAE` and its corollary `LogicGLPoint3.iff_forces_root`.
-/

@[expose]
public section

open LogicGL

/-!
# Step M: from `GL.3` Gentzen-provability to `LogicGLPoint3`-membership

This is the `GL.3` counterpart of `ProvableHilbert.of_provableGentzen`
(`ProvabilityLogic/Hilbert/Basic.lean`): every sequent provable in the combinatorial `GL.3` Gentzen
calculus `⊢ᵍ[GLPoint3]` (`ProvabilityLogic/Gentzen/GLPoint3/Basic.lean`) translates into a `LogicGLPoint3`
membership statement. The proof is a structural induction on `LogicGLPoint3.ProofGentzen`,
mirroring `ProvableHilbert.of_provableGentzen` case by case; the only new case is
`boxGLPoint3`, discharged by the Step L soundness theorem `LogicGLPoint3.boxGLPoint3`.
-/

namespace LogicGL.ProvableHilbert

universe u
variable {α : Type u} [DecidableEq α] {A B C D : Formula α}

/-- Packaged (implication) form of `bridge_impL`, bundling its two premises into a single
antecedent conjunction so that it applies via `mdp'` to two `LogicGLPoint3`-membership facts. -/
private lemma bridge_impL_imp :
    ⊢ʰ[GL] ((C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)) 🡒 (((A 🡒 B) ⋏ C) 🡒 D) := by
  apply Kripke.completeness;
  intro κ _ M _ x;
  grind;

/-- Packaged (implication) form of `bridge_impR`, bundling its premise as an antecedent so that
it applies via `mdp'` to a `LogicGLPoint3`-membership fact. -/
private lemma bridge_impR_imp :
    ⊢ʰ[GL] ((A ⋏ C) 🡒 (B ⋎ D)) 🡒 (C 🡒 ((A 🡒 B) ⋎ D)) := by
  apply Kripke.completeness;
  intro κ _ M _ x;
  grind;

end LogicGL.ProvableHilbert

namespace LogicGLPoint3

universe u
variable {α : Type u} [DecidableEq α]

theorem of_provableGentzen {S : Sequent α} (h : ⊢ᵍ[GLPoint3] S) :
    ((⋀S.ant) 🡒 (⋁S.suc)) ∈ LogicGLPoint3 := by
  obtain ⟨h⟩ := h
  induction h with
  | axm A => simp; exact LogicGLPoint3.of_GL ProvableHilbert.impId
  | botL => simp; exact LogicGLPoint3.of_GL ProvableHilbert.efq
  | wkL _ hΓ ih =>
    exact LogicGLPoint3.impTrans (LogicGLPoint3.of_GL (ProvableHilbert.imp_fconj_fconj_of_subset (by grind))) ih
  | wkR _ hΔ ih =>
    exact LogicGLPoint3.impTrans ih (LogicGLPoint3.of_GL (ProvableHilbert.imp_fdisj_fdisj_of_subset (by grind)))
  | impL h₁ h₂ ih₁ ih₂ =>
    -- ih₁ : ⋀Γ 🡒 ⋁(insert A Δ) ∈ L,  ih₂ : ⋀(insert B Γ) 🡒 ⋁Δ ∈ L
    -- goal : ⋀(insert (A 🡒 B) Γ) 🡒 ⋁Δ ∈ L
    have e₁ := LogicGLPoint3.impTrans ih₁ (LogicGLPoint3.of_GL ProvableHilbert.imp_fdisj_insert)
    have e₂ := LogicGLPoint3.impTrans (LogicGLPoint3.of_GL ProvableHilbert.imp_fconj_insert) ih₂
    have ebridge := LogicGLPoint3.mdp' ProvableHilbert.bridge_impL_imp (LogicGLPoint3.andIntro' e₁ e₂)
    exact LogicGLPoint3.impTrans (LogicGLPoint3.of_GL ProvableHilbert.imp_insert_fconj) ebridge
  | impR h ih =>
    -- ih : ⋀(insert A Γ) 🡒 ⋁(insert B Δ) ∈ L
    -- goal : ⋀Γ 🡒 ⋁(insert (A 🡒 B) Δ) ∈ L
    have e := LogicGLPoint3.impTrans (LogicGLPoint3.of_GL ProvableHilbert.imp_fconj_insert)
      (LogicGLPoint3.impTrans ih (LogicGLPoint3.of_GL ProvableHilbert.imp_fdisj_insert))
    have ebridge := LogicGLPoint3.mdp' ProvableHilbert.bridge_impR_imp e
    exact LogicGLPoint3.impTrans ebridge (LogicGLPoint3.of_GL ProvableHilbert.imp_insert_fdisj)
  | boxGLPoint3 hΔ h ih =>
    exact LogicGLPoint3.boxGLPoint3 hΔ ih

theorem of_provableGentzen_formula {A : Formula α} (h : ⊢ᵍ[GLPoint3] (∅ ⟹ {A})) :
    A ∈ LogicGLPoint3 := by
  have h' := of_provableGentzen h
  simp at h'
  exact Logic.sumNormal.mdp h' (LogicGLPoint3.of_GL ProvableHilbert.top)

end LogicGLPoint3

variable {α : Type u}

namespace LogicGLPoint3

open Model Model.World

/-- Soundness of `LogicGLPoint3` over finite linear GL models. -/
lemma sound [DecidableEq α] {κ : Type u} [Nonempty κ] {M : Model κ α}
    [M.IsFiniteGLPoint3] {A : Formula α} (h : A ∈ LogicGLPoint3) : M ⊧ A := by
  induction h using LogicGLPoint3.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.finite_soundness h M;
  | axiomWeakPoint3 => exact Model.validate_axiomWeakPoint3;
  | mdp ihAB ihA => exact fun x => (ihAB x) (ihA x);
  | nec ih => exact fun x y _ => ih y;

variable [DecidableEq α] {A : Formula α}

/--
Kripke completeness: a formula is provable in `LogicGLPoint3` iff it is valid over all finite `GL.3` models
iff it is provable in the `GL.3` sequent calculus `⊢ᵍ[GLPoint3]` iff it is forced at the root of all finite rooted `GL.3` models.

- [VS83, Theorem 10, Theorem 11(b), Theorem 11(c)]
-/
theorem provability_TFAE : [
  A ∈ LogicGLPoint3,
  ⊢ᵍ[GLPoint3] (∅ ⟹ {A}),
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A,
  ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGLPoint3] → M ⊧ A,
  ∀ (n : ℕ) [NeZero n] (M : RootedModel (Fin n) α), [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A
].TFAE := by
  tfae_have 2 → 1 := LogicGLPoint3.of_provableGentzen_formula;
  tfae_have 1 → 3 := fun h {κ} _ M _ => LogicGLPoint3.sound h;
  tfae_have 5 → 2 := by
    intro h;
    apply LogicGLPoint3.ProvableGentzen.Kripke.completeness;
    intro n _ M _;
    exact Model.validateSequent_singleton_iff.mpr (h n M);
  tfae_have 3 → 4 := fun h {κ} _ M _ => h M.toModel M.root.1;
  tfae_have 4 → 3 := by
    intro h κ _ M _ x;
    exact Model.toRootedModel.forces_same_at_root.mp (h (M.toRootedModel x));
  tfae_have 3 → 5 := by
    intro h n _ M _;
    exact Model.validate_reindex_iff.mp <| h (M.reindex (Equiv.ulift (α := Fin n)).symm);
  tfae_have 5 → 3 := by
    intro h κ _ M _;
    haveI : Finite κ := (inferInstance : Finite M.World);
    exact Model.validate_toConcrete_iff.mp <| h M.card M.toConcrete;
  tfae_have 4 → 6 := by
    intro h n _ M _;
    exact RootedModel.forces_reindex_root_iff.mp <| h (M.reindex (Equiv.ulift (α := Fin n)).symm);
  tfae_have 6 → 4 := by
    intro h κ _ M _;
    haveI : Finite κ := (inferInstance : Finite M.World);
    exact RootedModel.forces_toConcrete_root_iff.mp <| h M.card M.toConcrete;
  tfae_finish;

theorem iff_forces : A ∈ LogicGLPoint3 ↔
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A :=
  provability_TFAE.out 0 2

/--
A formula is a theorem of `LogicGLPoint3` iff it is forced at the root of every
finite rooted linear GL model.
-/
theorem iff_forces_root : A ∈ LogicGLPoint3 ↔
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A :=
  provability_TFAE.out 0 3

theorem iff_forces_concrete : A ∈ LogicGLPoint3 ↔
  ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGLPoint3] → M ⊧ A :=
  provability_TFAE.out 0 4

theorem iff_forces_root_concrete : A ∈ LogicGLPoint3 ↔
  ∀ (n : ℕ) [NeZero n] (M : RootedModel (Fin n) α), [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A :=
  provability_TFAE.out 0 5

variable {n : ℕ} [NeZero n]

/-- A rooted concrete finite `GL.3`-model refuting `A` at its root shows `A` is not a
`GL.3`-theorem. -/
theorem not_mem_of_concrete_root_not_forces (M : RootedModel (Fin n) α) [M.IsFiniteGLPoint3]
  (h : M.root.1 ⊮[_] A) : A ∉ LogicGLPoint3 :=
  fun hA => h <| iff_forces_root_concrete.mp hA n M

/-- If `A` is a `GL.3`-theorem, it is forced at the root of every rooted concrete finite
`GL.3`-model. -/
theorem concrete_root_forces_of_mem (M : RootedModel (Fin n) α) [M.IsFiniteGLPoint3]
  (h : A ∈ LogicGLPoint3) : M.root.1 ⊩[_] A :=
  iff_forces_root_concrete.mp h n M

/-- A concrete finite `GL.3`-model with a world not forcing `A` shows `A` is not a
`GL.3`-theorem. -/
theorem not_mem_of_concrete_not_forces (M : Model (Fin n) α) [M.IsFiniteGLPoint3] {x : M.World}
  (h : x ⊮[M] A) : A ∉ LogicGLPoint3 :=
  fun hA => h <| iff_forces_concrete.mp hA n M x

/-- If `A` is a `GL.3`-theorem, it is forced at every world of every concrete finite
`GL.3`-model. -/
theorem concrete_forces_of_mem (M : Model (Fin n) α) [M.IsFiniteGLPoint3] (h : A ∈ LogicGLPoint3)
  (x : M.World) : x ⊩[M] A :=
  iff_forces_concrete.mp h n M x

end LogicGLPoint3

end
