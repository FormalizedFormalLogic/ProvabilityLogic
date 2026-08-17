module

public import ProvabilityLogic.Gentzen.A.Basic
public import ProvabilityLogic.Gentzen.GL.Kripke
public import ProvabilityLogic.Gentzen.GL.WithCut
public import ProvabilityLogic.Kripke.GraftOmega

/-!
# Soundness and completeness for the sequent calculus for `A`

Soundness and completeness of level-`1` `LogicA`-Gentzen provability with respect to
`RootedModel.graftOmega` semantics, the resulting `List.TFAE` package tying it to
`LogicGL`-provability, and semantic cut elimination. Original to this formalization: it
assembles `LogicGL` completeness, `RootedModel.graftOmega`, and a pigeonhole argument for a
reflexive world, following the structure of the analogous result for `LogicD`, but the
level-`1` statement for `LogicA` itself is not stated in this form in the literature.
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

open Model.World RootedModel
open scoped LogicA

namespace LogicA.GentzenWithCutProvable

/-- Soundness of level-`0` `LogicA`-with-cut proofs w.r.t. arbitrary `IsGL` Kripke models. -/
theorem soundness_zero {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[0] Δ)) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → M ⊧ (Γ ⟹ Δ) :=
  LogicGL.ProvableGentzen.Kripke.soundness (toProvableGentzenGL h)

/-- Soundness of level-`1` `LogicA`-with-cut proofs at the root of every ω-graft model built
from a finite rooted `GL` model. -/
theorem soundness_graftOmega {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[1] Δ)) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
  ∀ (a : M.World) (Rra : M.root.1 ≺ a),
  (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ) := by
  have key : ∀ {S : TwoLayeredSequent α}, ⊢ᵍᶜ[A] S → S.level = 1 →
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ (a : M.World) (Rra : M.root.1 ≺ a),
    (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] S.toSequent := by
    rintro S hS hl κ _ M _ a Rra;
    induction hS generalizing M with
    | axm l A => exact forces_sequent_axm;
    | botL l => exact forces_sequent_botL;
    | wkL h h' ih => exact forces_sequent_wkL (ih hl M a Rra) h';
    | wkR h h' ih => exact forces_sequent_wkR (ih hl M a Rra) h';
    | impL h₁ h₂ ih₁ ih₂ => exact forces_sequent_impL (ih₁ hl M a Rra) (ih₂ hl M a Rra);
    | impR h ih => exact forces_sequent_impR (ih hl M a Rra);
    | liftUp h ih =>
      have ha : a ≠ M.root.1 := fun h => Std.Irrefl.irrefl _ (h ▸ Rra);
      let Mω := M.graftOmega ⟨a, ha⟩;
      haveI : Mω.IsGL := graftOmega.isGL (a := ⟨a, ha⟩) Rra;
      exact soundness_zero h Mω.toModel Mω.root.1;
    | boxGL h ih => simp at hl;
    | boxGP h ih =>
      intro hΓ;
      obtain ⟨D, hD, hxD⟩ := ih hl M a Rra hΓ;
      rcases Finset.mem_insert.mp hD with rfl | hD;
      . exact absurd hxD graftOmega.root_not_forces_boxItr_bot;
      . exact ⟨D, hD, hxD⟩;
    | cut h₁ h₂ ih₁ ih₂ =>
      exact forces_sequent_cut (ih₁ hl M a Rra) (ih₂ hl M a Rra);
  intro κ _ M _ a Rra;
  exact key h rfl M a Rra;

end LogicA.GentzenWithCutProvable

namespace LogicA.ProvableGentzen

/-- Completeness of level-`1` cut-free `LogicA`-Gentzen provability w.r.t. `graftOmega`
semantics: if a sequent is forced at the root of every ω-graft extension of every finite
rooted `GL` model, it is cut-free provable. -/
theorem completeness {Γ Δ : FormulaFinset α}
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ (a : M.World) (Rra : M.root.1 ≺ a),
    (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ)) :
  ⊢ᵍ[A] (Γ ⟹[1] Δ) := by
  sorry

end LogicA.ProvableGentzen

/-- The four equivalent characterizations of `Γ ⟹ Δ` being a theorem of level-`1`
`LogicA.ProofGentzen`: with-cut provability, cut-free provability, forcing at the root of
every ω-graft extension of every finite rooted `GL` model, and a `GL`-provable deduction-
theorem form. -/
theorem LogicA.semantical_TFAE {Γ Δ : FormulaFinset α} : [
    ⊢ᵍᶜ[A] (Γ ⟹[1] Δ),
    ⊢ᵍ[A] (Γ ⟹[1] Δ),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      ∀ (a : M.World) (Rra : M.root.1 ≺ a),
      (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ),
    ∃ n : ℕ, ⊢ᵍ[GL] (Γ ⟹ insert (□^[n]⊥) Δ)
  ].TFAE := by
  sorry

namespace LogicA.GentzenWithCutProvable

/-- Semantic cut elimination for level-`1` `LogicA`-Gentzen provability: every with-cut
proof yields a cut-free proof. -/
theorem cutElimination {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[1] Δ)) : ⊢ᵍ[A] (Γ ⟹[1] Δ) := by
  sorry

end LogicA.GentzenWithCutProvable

end
