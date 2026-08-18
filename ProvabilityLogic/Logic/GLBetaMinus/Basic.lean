module

public import ProvabilityLogic.Logic.GL.Letterless
public import ProvabilityLogic.Kripke.FiniteLineModel
public import ProvabilityLogic.ToFoundation.Vorspiel.Set.Basic
public import ProvabilityLogic.Formula.Countable
public import ProvabilityLogic.ProvabilityLogic.GL.Uniform
public import ProvabilityLogic.ToFoundation.FirstOrder.Basic.Compactness

@[expose]
public section

noncomputable abbrev TBBMinus [DecidableEq α] (X : Set ℕ) (X_finite : X.Finite := by grind) : Formula α := ∼⋀(X_finite.toFinset.image TBB)

abbrev LogicGLBetaMinus {α} [DecidableEq α] (𝔹 : Set ℕ) (𝔹_cofinite : 𝔹ᶜ.Finite := by grind) : Logic α := (@LogicGL α) +ᴸ (LetterlessFormulaSet.lift { TBBMinus _ 𝔹_cofinite })

end
