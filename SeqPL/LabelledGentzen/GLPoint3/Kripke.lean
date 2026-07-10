module

public import SeqPL.Kripke.Linearity
public import SeqPL.LabelledGentzen.GLPoint3.Basic
public import SeqPL.LabelledGentzen.Kripke

@[expose]
public section

open LabelledGentzen

variable {κ : Type u} [Nonempty κ]
         {α : Type v} [DecidableEq α]
         {M : Model κ α}

namespace Model

variable {L : M.LabelMap} {R : Finset LabelledGentzen.LabelRel} {Γ Δ : Finset (LabelledGentzen.LabelledFormula α)}
         {x y z : LabelledGentzen.Label} {A B : Formula α}

/-- Relabelling `y` to `z` in a sequent does not change its validity under a label map
identifying `y` and `z`. -/
lemma validate_labelled_relabel_of_eq {S : LabelledGentzen.LabelledSequent α} (heq : L y = L z) :
  M ⊧ˡ[L] (S.relabel y z) ↔ M ⊧ˡ[L] S := by
  have hL : ∀ a : LabelledGentzen.Label, L (if a = y then z else a) = L a := by
    intro a; by_cases h : a = y <;> simp [h, heq];
  simp only [Model.ValidateLabelled, LabelledGentzen.LabelledSequent.relabel,
    LabelledGentzen.LabelledFormula.relabel, Finset.forall_mem_image, Finset.exists_mem_image, hL];

/-- Soundness of the `Lin` rule: on a linear frame, any two successors `y`, `z`
of a common world `x` are related by `y ≺ z`, `y = z`, or `z ≺ y`, and the corresponding
premise closes the sequent in each case. -/
lemma validate_labelled_lin [M.IsGLPoint3]
  (hxy : (x, y) ∈ R) (hxz : (x, z) ∈ R)
  (h₁ : M ⊧ˡ[L] (insert (y, z) R ⸴ Γ ⟹ˡ Δ))
  (h₂ : M ⊧ˡ[L] (insert (z, y) R ⸴ Γ ⟹ˡ Δ))
  (h₃ : M ⊧ˡ[L] ((R ⸴ Γ ⟹ˡ Δ).relabel y z))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ) := by
  intro hrel hant;
  rcases Model.linear (hrel (x, y) hxy) (hrel (x, z) hxz) with hyz | heq | hzy;
  · exact h₁ (by rintro p hp; rcases Finset.mem_insert.mp hp with rfl | hp; exacts [hyz, hrel p hp]) hant;
  · exact (validate_labelled_relabel_of_eq heq).mp h₃ hrel hant;
  · exact h₂ (by rintro p hp; rcases Finset.mem_insert.mp hp with rfl | hp; exacts [hzy, hrel p hp]) hant;

end Model


namespace LabelledGentzen.GLPoint3.ProvableLabelledGentzen

namespace Kripke

open Model in
/-- Soundness of the labelled calculus for `LogicGLPoint3` with respect to Kripke semantics on
linear `GL` models. -/
theorem soundness {S : LabelledGentzen.LabelledSequent α} (h : ⊢ˡ³ S) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGLPoint3] → ∀ L : M.LabelMap, M ⊧ˡ[L] S := by
  obtain ⟨p⟩ := h;
  intro κ _ M _;
  induction p with
  | axm x A => exact λ _ => validate_labelled_axm;
  | botL x => exact λ _ => validate_labelled_botL;
  | wkRel _ hR ih => exact λ L => validate_labelled_wkRel (ih L) hR;
  | wkAnt _ hΓ ih => exact λ L => validate_labelled_wkAnt (ih L) hΓ;
  | wkSuc _ hΔ ih => exact λ L => validate_labelled_wkSuc (ih L) hΔ;
  | impL _ _ ih₁ ih₂ => exact λ L => validate_labelled_impL (ih₁ L) (ih₂ L);
  | impR _ ih => exact λ L => validate_labelled_impR (ih L);
  | boxL x y A hxy hxA _ ih => exact λ L => validate_labelled_boxL hxy hxA (ih L);
  | boxRLob x y A hfresh _ ih => exact λ L => validate_labelled_boxRLob hfresh ih;
  | irref x hxx => exact λ _ => validate_labelled_irref hxx;
  | trans x y z hxy hyz _ ih => exact λ L => validate_labelled_trans hxy hyz (ih L);
  | lin x y z hxy hxz _ _ _ ih₁ ih₂ ih₃ => exact λ L => validate_labelled_lin hxy hxz (ih₁ L) (ih₂ L) (ih₃ L);

/-- A formula provable as `∅ ⸴ ∅ ⟹ˡ {x ∶ A}` is valid in every `LogicGLPoint3` model. -/
theorem soundness_formula {x : LabelledGentzen.Label} {A : Formula α} (h : ⊢ˡ³ (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGLPoint3] → M.Validate A := by
  intro κ _ M _ w;
  obtain ⟨lf, hlf, hf⟩ := soundness h M (λ _ => w) (by grind) (by grind);
  grind;

end Kripke

end LabelledGentzen.GLPoint3.ProvableLabelledGentzen

end
