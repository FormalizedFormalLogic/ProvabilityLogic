module

public import SeqPL.Hilbert.Basic
public import SeqPL.Kripke.PointGenerate
public import Mathlib.Tactic.TFAE

@[expose]
public section

variable {α : Type u}

abbrev Logic (α) := Set (Formula α)

end
