module

public import SeqPL.Logic.GL.Basic

@[expose]
public section

namespace LogicGL

variable {α : Type*} [DecidableEq α] {A B C : Formula α}

/-- The implication-transitivity tautology is a GL theorem. -/
theorem imp_trans : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 A 🡒 C) ∈ @LogicGL α := by
  apply ProvableHilbert.Kripke.completeness
  intro κ _ M _ x
  grind

end LogicGL

end
