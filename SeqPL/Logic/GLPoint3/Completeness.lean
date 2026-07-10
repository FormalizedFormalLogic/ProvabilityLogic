module

public import SeqPL.Logic.GLPoint3.Basic
public import SeqPL.Gentzen.GLPoint3.Basic
public import SeqPL.Gentzen.GLPoint3.Kripke
public import SeqPL.Kripke.RootedModel
public import Mathlib.Tactic.TFAE

@[expose]
public section

/-!
# Soundness and Kripke completeness of `LogicGLPoint3`

This file bundles: the translation from `GL.3` Gentzen-provability to `LogicGLPoint3`-membership
(Step M, `GLPoint3.of_provableGentzen`/`of_provableGentzen_formula`); the soundness of
`LogicGLPoint3` over finite linear GL models (`LogicGLPoint3.sound`); and, combining both with the
sequent calculus results of `SeqPL/Gentzen/GLPoint3/Kripke.lean`, the packaged Kripke completeness
theorem `LogicGLPoint3.provability_TFAE` and its corollary `LogicGLPoint3.iff_forces_root`.
-/

/-!
# Step M: from `GL.3` Gentzen-provability to `LogicGLPoint3`-membership

This is the `GL.3` counterpart of `ProvableHilbert.of_provableGentzen`
(`SeqPL/Hilbert/Basic.lean`): every sequent provable in the combinatorial `GL.3` Gentzen
calculus `⊢ᵍ³` (`SeqPL/Gentzen/GLPoint3/Basic.lean`) translates into a `LogicGLPoint3`
membership statement. The proof is a structural induction on `GLPoint3.ProofGentzen`,
mirroring `ProvableHilbert.of_provableGentzen` case by case; the only new case is
`boxGLPoint3`, discharged by the Step L soundness theorem `LogicGLPoint3.boxGLPoint3`.
-/

namespace ProvableHilbert

universe u
variable {α : Type u} {A B C D : Formula α}

/-- Packaged (implication) form of `bridge_impL`: instead of taking the two premises
`ha, hb` as separately `⊢ʰ`-provable facts, this bundles them into a single antecedent
conjunction, so that it can be applied via `mdp'` to two `LogicGLPoint3`-membership facts. -/
private lemma bridge_impL_imp :
    ⊢ʰ ((C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)) 🡒 (((A 🡒 B) ⋏ C) 🡒 D) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `X = {(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)}`, goal `D`
  have hHab : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α)
      ⊢ʰ (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D) := DeducibleHilbert.ofContext (by grind);
  have ha : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α) ⊢ʰ C 🡒 (A ⋎ D) :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hHab;
  have hb : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α) ⊢ʰ (B ⋏ C) 🡒 D :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hHab;
  have hmem : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α) ⊢ʰ (A 🡒 B) ⋏ C :=
    DeducibleHilbert.ofContext (by grind);
  have hC : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α) ⊢ʰ C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem;
  have hAD : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α) ⊢ʰ A ⋎ D :=
    DeducibleHilbert.mdp ha hC;
  have hAtoD : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α) ⊢ʰ A 🡒 D := by
    apply DeducibleHilbert.deduction_theorem.mp;
    -- context now additionally holds `A`
    have hmem' : (insert A ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α))
        ⊢ʰ (A 🡒 B) ⋏ C := DeducibleHilbert.of_subset_ctx (by grind) hmem;
    have hb' : (insert A ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α))
        ⊢ʰ (B ⋏ C) 🡒 D := DeducibleHilbert.of_subset_ctx (by grind) hb;
    have hAB : (insert A ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α))
        ⊢ʰ A 🡒 B := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hmem';
    have hCi : (insert A ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α))
        ⊢ʰ C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem';
    have hA : (insert A ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α))
        ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
    have hB : (insert A ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α))
        ⊢ʰ B := DeducibleHilbert.mdp hAB hA;
    have hBC : (insert A ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α))
        ⊢ʰ B ⋏ C := DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hB) hCi;
    exact DeducibleHilbert.mdp hb' hBC;
  have hDtoD : ({(A 🡒 B) ⋏ C, (C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)} : FormulaSet α) ⊢ʰ D 🡒 D :=
    DeducibleHilbert.ofProvable impId;
  exact DeducibleHilbert.orElim hAtoD hDtoD hAD;

/-- Packaged (implication) form of `bridge_impR`: the single premise `h` is bundled as an
antecedent, so that it can be applied via `mdp'` to a `LogicGLPoint3`-membership fact. -/
private lemma bridge_impR_imp :
    ⊢ʰ ((A ⋏ C) 🡒 (B ⋎ D)) 🡒 (C 🡒 ((A 🡒 B) ⋎ D)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `X = {C, (A ⋏ C) 🡒 (B ⋎ D)}`, goal `(A 🡒 B) ⋎ D`
  have hh : ({C, (A ⋏ C) 🡒 (B ⋎ D)} : FormulaSet α) ⊢ʰ (A ⋏ C) 🡒 (B ⋎ D) :=
    DeducibleHilbert.ofContext (by grind);
  have hCc : ({C, (A ⋏ C) 🡒 (B ⋎ D)} : FormulaSet α) ⊢ʰ C := DeducibleHilbert.ofContext (by grind);
  have hAB_D : ({C, (A ⋏ C) 🡒 (B ⋎ D)} : FormulaSet α) ⊢ʰ A 🡒 (B ⋎ D) := by
    apply DeducibleHilbert.deduction_theorem.mp;
    have hh' : (insert A ({C, (A ⋏ C) 🡒 (B ⋎ D)} : FormulaSet α)) ⊢ʰ (A ⋏ C) 🡒 (B ⋎ D) :=
      DeducibleHilbert.of_subset_ctx (by grind) hh;
    have hCc' : (insert A ({C, (A ⋏ C) 🡒 (B ⋎ D)} : FormulaSet α)) ⊢ʰ C :=
      DeducibleHilbert.of_subset_ctx (by grind) hCc;
    have hA : (insert A ({C, (A ⋏ C) 🡒 (B ⋎ D)} : FormulaSet α)) ⊢ʰ A :=
      DeducibleHilbert.ofContext (by grind);
    have hAC : (insert A ({C, (A ⋏ C) 🡒 (B ⋎ D)} : FormulaSet α)) ⊢ʰ A ⋏ C :=
      DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA) hCc';
    exact DeducibleHilbert.mdp hh' hAC;
  exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable imp_push_disj) hAB_D;

end ProvableHilbert

namespace GLPoint3

universe u
variable {α : Type u} [DecidableEq α]

theorem of_provableGentzen {S : Sequent α} (h : ⊢ᵍ³ S) :
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

theorem of_provableGentzen_formula {A : Formula α} (h : ⊢ᵍ³ (∅ ⟹ {A})) :
    A ∈ LogicGLPoint3 := by
  have h' := of_provableGentzen h
  simp at h'
  exact Logic.sumNormal.mdp h' (LogicGLPoint3.of_GL ProvableHilbert.top)

end GLPoint3

variable {α : Type u}

namespace LogicGLPoint3

open Model Model.World

/-- Soundness of `GLPoint3` over finite linear GL models. -/
lemma sound [DecidableEq α] {κ : Type u} [Nonempty κ] {M : Model κ α}
    [M.IsFiniteGLPoint3] {A : Formula α} (h : A ∈ LogicGLPoint3) : M ⊧ A := by
  induction h using LogicGLPoint3.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.finite_soundness h M;
  | axiomWeakPoint3 => exact Model.validate_axiomWeakPoint3;
  | mdp ihAB ihA => exact fun x => (ihAB x) (ihA x);
  | nec ih => exact fun x y _ => ih y;

/--
  **Kripke completeness of `GLPoint3`**, packaged as a `List.TFAE` of the four equivalent
  characterizations of `LogicGLPoint3`-provability: membership in the Hilbert-style closure,
  provability in the `GL.3` sequent calculus `⊢ᵍ³`, validity over all finite `GL.3` models, and
  forcing at the root of all finite rooted `GL.3` models.

  The soundness direction (1 → 3) is `LogicGLPoint3.sound`. The completeness direction
  (3 → 2 → 1) corresponds to Theorem 10 (completeness of the sequent calculus `LS`) and
  Theorem 11 (b), (c) (finite model property and completeness with respect to `(ω, >)`) of
  Valentini & Solitro 1983.
-/
theorem provability_TFAE [DecidableEq α] {A : Formula α} : [
  A ∈ LogicGLPoint3,
  ⊢ᵍ³ (∅ ⟹ {A}),
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩ A
].TFAE := by
  tfae_have 2 → 1 := GLPoint3.of_provableGentzen_formula;
  tfae_have 1 → 3 := fun h {κ} _ M _ => LogicGLPoint3.sound h;
  tfae_have 3 → 2 := by
    intro h;
    apply GLPoint3.ProvableGentzen.Kripke.completeness_universe;
    intro κ _ M _;
    exact Model.validateSequent_singleton_iff.mpr (h M);
  tfae_have 3 → 4 := fun h {κ} _ M _ => h M.toModel M.root.1;
  tfae_have 4 → 3 := by
    intro h κ _ M _ x;
    exact Model.toRootedModel.forces_same_at_root.mp (h (M.toRootedModel x));
  tfae_finish;

/--
  A formula is a theorem of `GLPoint3` (`GLLin`) iff it is forced at the root of every
  finite rooted linear GL model.
-/
theorem iff_forces_root [DecidableEq α] {A : Formula α} :
  A ∈ LogicGLPoint3 ↔
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩ A :=
  provability_TFAE.out 0 3

end LogicGLPoint3

end
