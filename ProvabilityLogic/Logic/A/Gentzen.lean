module

public import ProvabilityLogic.Gentzen.A.Kripke
public import ProvabilityLogic.Logic.A.Basic

@[expose]
public section

open LogicA

variable {α : Type u} [DecidableEq α] {A : Formula α} {n : ℕ}

/-- The axiom `∼□^[n]⊥` is with-cut-provable at level `1`. -/
lemma LogicA.provableGentzenWithCut_neg_boxItr_bot (n) : ⊢ᵍᶜ[A] ((∅ : FormulaFinset α) ⟹[1] {∼□^[n]⊥}) := by
  sorry

/-- Modus ponens for level-`1` `LogicA`-with-cut provability, via the `cut` rule. -/
theorem LogicA.GentzenWithCutProvable.mdp {A B : Formula α}
  (hAB : ⊢ᵍᶜ[A] (∅ ⟹[1] {A 🡒 B})) (hA : ⊢ᵍᶜ[A] (∅ ⟹[1] {A})) : ⊢ᵍᶜ[A] (∅ ⟹[1] {B}) := by
  sorry

/-- `LogicA`-provability implies level-`1` `LogicA`-with-cut provability. -/
theorem LogicA.of_provable {A : Formula α} (h : A ∈ LogicA) : ⊢ᵍᶜ[A] (∅ ⟹[1] {A}) := by
  sorry

/-- `LogicA`-provability is characterized by provability in the with-cut two-layered
sequent calculus for `A`, at level `1`. -/
theorem LogicA.iff_provable_provableGentzenWithCut {A : Formula α} :
  A ∈ LogicA ↔ ⊢ᵍᶜ[A] (∅ ⟹[1] {A}) := by
  sorry

end
