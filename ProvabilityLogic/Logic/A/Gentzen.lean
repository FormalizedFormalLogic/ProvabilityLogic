module

public import ProvabilityLogic.Gentzen.A.Kripke
public import ProvabilityLogic.Logic.A.Basic

@[expose]
public section

open LogicA

variable {α : Type u} [DecidableEq α] {A : Formula α} {n : ℕ}

/-- The axiom `∼□^[n]⊥` is with-cut-provable at level `1`. -/
lemma LogicA.provableGentzenWithCut_neg_boxItr_bot (n) : ⊢ᵍᶜ[A] ((∅ : FormulaFinset α) ⟹[1] {∼□^[n]⊥}) := by
  show ⊢ᵍᶜ[A] ((∅ : FormulaFinset α) ⟹[1] {□^[n]⊥ 🡒 ⊥});
  rw [← Finset.insert_empty];
  apply GentzenWithCutProvable.impR;
  apply GentzenWithCutProvable.boxGP (n := n);
  apply GentzenWithCutProvable.wkR (GentzenWithCutProvable.axm 1 (□^[n]⊥));
  grind;

/-- Modus ponens for level-`1` `LogicA`-with-cut provability, via the `cut` rule. -/
theorem LogicA.GentzenWithCutProvable.mdp {A B : Formula α}
  (hAB : ⊢ᵍᶜ[A] (∅ ⟹[1] {A 🡒 B})) (hA : ⊢ᵍᶜ[A] (∅ ⟹[1] {A})) : ⊢ᵍᶜ[A] (∅ ⟹[1] {B}) := by
  have h₁ : ⊢ᵍᶜ[A] ((insert (A 🡒 B) (∅ : FormulaFinset α)) ⟹[1] {B}) :=
    GentzenWithCutProvable.impL (GentzenWithCutProvable.wkR hA (by grind))
      (GentzenWithCutProvable.wkL (GentzenWithCutProvable.axm 1 B) (by grind))
  have h₂ : ⊢ᵍᶜ[A] ((∅ : FormulaFinset α) ⟹[1] insert (A 🡒 B) (∅ : FormulaFinset α)) := by
    rwa [Finset.insert_empty]
  simpa using GentzenWithCutProvable.cut h₂ h₁

/-- `LogicA`-provability implies level-`1` `LogicA`-with-cut provability. -/
theorem LogicA.of_provable {A : Formula α} (h : A ∈ LogicA) : ⊢ᵍᶜ[A] (∅ ⟹[1] {A}) := by
  sorry

/-- `LogicA`-provability is characterized by provability in the with-cut two-layered
sequent calculus for `A`, at level `1`. -/
theorem LogicA.iff_provable_provableGentzenWithCut {A : Formula α} :
  A ∈ LogicA ↔ ⊢ᵍᶜ[A] (∅ ⟹[1] {A}) := by
  sorry

end
