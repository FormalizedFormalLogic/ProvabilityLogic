module

public import SeqPL.Kripke.Basic

@[expose]
public section

variable [Nonempty κ]

abbrev Model.Root (M : Model κ α) := { r : M.World // ∀ x, x ≠ r → r ≺ x }

structure RootedModel (κ) [Nonempty κ] (α) extends Model κ α where
  root : toModel.Root

namespace RootedModel

variable {M : RootedModel κ α} {s : Formula.Substitution α}

/-- Rooted model obtained by composing the valuation with a substitution `s`
(the frame and the root are unchanged). -/
abbrev substModel (M : RootedModel κ α) (s : Formula.Substitution α) : RootedModel κ α where
  toModel := M.toModel.substModel s
  root := M.root

end RootedModel

end
