module

public import ProvabilityLogic.Gentzen.A.Basic
public import ProvabilityLogic.Gentzen.GL.Kripke
public import ProvabilityLogic.Gentzen.GL.WithCut
public import ProvabilityLogic.Kripke.GraftOmega

/-!
# Soundness and completeness for the sequent calculus for `A`

Soundness and completeness of level-`1` `LogicA`-Gentzen provability w.r.t.
`RootedModel.graftOmega` semantics, and the resulting semantic cut elimination.
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

open LogicGL LogicGL.ProvableGentzen.Kripke in
/-- A `GL`-unprovable sequent has a finite `GL` countermodel with a world forcing every
antecedent formula and refuting every succedent formula. -/
private lemma exists_countermodel {Γ Δ : FormulaFinset α}
  (h : ⊬ᵍ[GL] (Γ ⟹ Δ)) :
  ∃ (κ : Type u) (_ : Nonempty κ) (M : Model κ α) (_ : M.IsFiniteGL) (x : M.World),
  (∀ C ∈ Γ, x ⊩[M] C) ∧ (∀ D ∈ Δ, x ⊮[M] D) := by
  haveI : Fact (⊬ᵍ[GL] (Γ ⟹ Δ)) := ⟨h⟩;
  exact ⟨_, inferInstance, countermodelOf (Γ ⟹ Δ), inferInstance,
    ExpandedSequent.lindenbaum _ h Sequent.subset_self_subfmls,
    fun _ hC => truthlemma_ant (ExpandedSequent.subset_lindenbaum.1 hC),
    fun _ hD => truthlemma_suc (ExpandedSequent.subset_lindenbaum.2 hD)⟩;

open Model.toRootedModel RootedModel.graftOmega in
/-- `graftOmega` forcing of `Γ ⟹ Δ` yields `GL`-provability of `Γ ⟹ insert (□^[n]⊥) Δ` for
every `n` exceeding the number of boxed subformulas of `Γ ⟹ Δ`. -/
private lemma provableGentzenGL_of_forces_graftOmega {Γ Δ : FormulaFinset α}
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ (a : M.World) (Rra : M.root.1 ≺ a),
    (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ))
  {n : ℕ} (hn : (FormulaFinset.prebox (Γ ⟹ Δ : Sequent α).subfmls).card < n) :
  ⊢ᵍ[GL] (Γ ⟹ insert (□^[n]⊥) Δ) := by
  by_contra hnp;
  set N := (FormulaFinset.prebox (Γ ⟹ Δ : Sequent α).subfmls).card with hN;
  obtain ⟨_, _, M₀, _, x, hΓ, hΔ⟩ := exists_countermodel hnp;
  haveI : Fintype M₀.World := Fintype.ofFinite _;
  have h₁ : N < x.rank := by
    have : ¬(x.rank < n) := fun hc =>
      hΔ _ (Finset.mem_insert_self _ _) (Model.iff_rank_lt_forces_boxItr_bot.mp hc);
    omega;
  obtain ⟨z, Rxz, hz⟩ := Model.exists_forces_axiomT_of_card_lt_rank (hN ▸ h₁);
  have key := fun {C : Formula α} (hC : C ∈ (Γ ⟹ Δ : Sequent α).subfmls) =>
    mainlemma_of_closed (M := M₀.toRootedModel x) (Φ := (Γ ⟹ Δ : Sequent α).subfmls)
      (by grind) (by grind)
      ⟨⟨z, Or.inr Rxz⟩,
        fun hB => forces_same_at_cone_point.mpr (hz _ (FormulaFinset.iff_mem_prebox_mem.mpr hB))⟩
      Rxz hC;
  obtain ⟨D, hD, hfD⟩ := h (M₀.toRootedModel x) ⟨z, Or.inr Rxz⟩ Rxz
    (fun C hC => (key (Sequent.subset_self_subfmls (Finset.mem_union_left _ hC))).2 _
      |>.mpr (forces_same_at_root.mpr (hΓ C hC)));
  exact hΔ D (Finset.mem_insert_of_mem hD) <| forces_same_at_root.mp <|
    (key (Sequent.subset_self_subfmls (Finset.mem_union_right _ hD))).2 _ |>.mp hfD;

/-- Completeness of level-`1` cut-free `LogicA`-Gentzen provability w.r.t. `graftOmega`
semantics: if a sequent is forced at the root of every ω-graft extension of every finite
rooted `GL` model, it is cut-free provable. -/
theorem completeness {Γ Δ : FormulaFinset α}
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ (a : M.World) (Rra : M.root.1 ≺ a),
    (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ)) :
  ⊢ᵍ[A] (Γ ⟹[1] Δ) :=
  of_provableGentzen_insert_boxItr_bot
    (provableGentzenGL_of_forces_graftOmega h (Nat.lt_succ_self _))

end LogicA.ProvableGentzen

/-- `Γ ⟹ Δ` is a theorem of level-`1` `LogicA.ProofGentzen`, in each of four equivalent senses:
with-cut provability, cut-free provability, forcing at the root of every ω-graft extension of
every finite rooted `GL` model, and a `GL`-provable deduction-theorem form. -/
theorem LogicA.sequent_TFAE {Γ Δ : FormulaFinset α} : [
    ⊢ᵍᶜ[A] (Γ ⟹[1] Δ),
    ⊢ᵍ[A] (Γ ⟹[1] Δ),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      ∀ (a : M.World) (Rra : M.root.1 ≺ a),
      (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ),
    ∃ n : ℕ, ⊢ᵍ[GL] (Γ ⟹ insert (□^[n]⊥) Δ)
  ].TFAE := by
  tfae_have 2 → 1 := GentzenWithCutProvable.of_without_cut;
  tfae_have 1 → 3 := GentzenWithCutProvable.soundness_graftOmega;
  tfae_have 3 → 2 := ProvableGentzen.completeness;
  tfae_have 3 → 4 := fun h =>
    ⟨_, ProvableGentzen.provableGentzenGL_of_forces_graftOmega h (Nat.lt_succ_self _)⟩;
  tfae_have 4 → 2 := fun ⟨_, h⟩ => ProvableGentzen.of_provableGentzen_insert_boxItr_bot h;
  tfae_finish;

namespace LogicA.GentzenWithCutProvable

/-- Semantic cut elimination for level-`1` `LogicA`-Gentzen provability: every with-cut
proof yields a cut-free proof. -/
theorem cutElimination {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[1] Δ)) : ⊢ᵍ[A] (Γ ⟹[1] Δ) := by
  sorry

end LogicA.GentzenWithCutProvable

end
