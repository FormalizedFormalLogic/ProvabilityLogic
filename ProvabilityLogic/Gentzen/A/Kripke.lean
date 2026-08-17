module

public import ProvabilityLogic.Gentzen.A.Basic
public import ProvabilityLogic.Gentzen.GL.Kripke
public import ProvabilityLogic.Gentzen.GL.WithCut
public import ProvabilityLogic.Kripke.GraftOmega

@[expose]
public section

variable {α : Type u} [DecidableEq α]

open Model.World RootedModel

namespace LogicA.GentzenWithCutProvable

/-- Soundness of level-`0` `LogicA`-with-cut proofs w.r.t. arbitrary `IsGL` Kripke models. -/
theorem soundness_zero {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[0] Δ)) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → M ⊧ (Γ ⟹ Δ) := by
  obtain ⟨p⟩ := h;
  exact LogicGL.ProvableGentzen.Kripke.soundness (LogicGL.ProvableGentzen.of_with_cut ⟨p.toGentzenWithCutProofGL⟩);

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
    intro S hS;
    induction hS with
    | axm l A => intro _ κ _ M _ a Rra; exact forces_sequent_axm;
    | botL l => intro _ κ _ M _ a Rra; exact forces_sequent_botL;
    | wkL h h' ih => intro hl κ _ M _ a Rra; exact forces_sequent_wkL (ih hl M a Rra) h';
    | wkR h h' ih => intro hl κ _ M _ a Rra; exact forces_sequent_wkR (ih hl M a Rra) h';
    | impL h₁ h₂ ih₁ ih₂ =>
      intro hl κ _ M _ a Rra;
      exact forces_sequent_impL (ih₁ hl M a Rra) (ih₂ hl M a Rra);
    | impR h ih => intro hl κ _ M _ a Rra; exact forces_sequent_impR (ih hl M a Rra);
    | liftUp h ih =>
      intro _ κ _ M _ a Rra;
      have ha : a ≠ M.root.1 := fun h => Std.Irrefl.irrefl _ (h ▸ Rra);
      let Mω := M.graftOmega ⟨a, ha⟩;
      haveI : Mω.IsGL := graftOmega.isGL (a := ⟨a, ha⟩) Rra;
      exact soundness_zero h Mω.toModel Mω.root.1;
    -- `boxGL` concludes a level-`0` sequent, so the level guard is unsatisfiable.
    | boxGL h ih => simp;
    | boxGP h ih =>
      intro hl κ _ M _ a Rra hΓ;
      obtain ⟨D, hD, hxD⟩ := ih hl M a Rra hΓ;
      rcases Finset.mem_insert.mp hD with rfl | hD;
      . exact absurd hxD graftOmega.root_not_forces_boxItr_bot;
      . exact ⟨D, hD, hxD⟩;
    | cut h₁ h₂ ih₁ ih₂ =>
      intro hl κ _ M _ a Rra;
      exact forces_sequent_cut (ih₁ hl M a Rra) (ih₂ hl M a Rra);
  intro κ _ M _ a Rra;
  exact key h rfl M a Rra;

end LogicA.GentzenWithCutProvable

end
