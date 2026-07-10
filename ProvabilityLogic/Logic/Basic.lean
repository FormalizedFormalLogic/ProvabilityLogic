module

public import ProvabilityLogic.Hilbert.Basic
public import ProvabilityLogic.Kripke.Cone
public import Mathlib.Tactic.TFAE

@[expose]
public section

variable {α : Type u}

abbrev Logic (α) := Set (Formula α)

end
