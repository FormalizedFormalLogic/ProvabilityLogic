module

public import ProvabilityLogic.Logic.GL.Letterless
public import ProvabilityLogic.Kripke.FiniteLineModel
public import ProvabilityLogic.ToFoundation.Vorspiel.Set.Basic
public import ProvabilityLogic.Formula.Countable
public import ProvabilityLogic.ProvabilityLogic.GL.Uniform
public import ProvabilityLogic.ToFoundation.FirstOrder.Basic.Compactness

@[expose]
public section

abbrev LogicGLAlpha {α} (𝔸 : Set ℕ) : Logic α := (@LogicGL α) +ᴸ ↑(𝔸.image $ TBB (α := Empty))

end
