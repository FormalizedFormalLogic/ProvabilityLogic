module

public import ProvabilityLogic.Kripke.Basic

@[expose]
public section

variable [Nonempty κ]

abbrev Model.Root (M : Model κ α) := { r : M.World // ∀ x, x ≠ r → r ≺ x }

structure RootedModel (κ) [Nonempty κ] (α) extends Model κ α where
  root : toModel.Root

namespace RootedModel

abbrev NonRoot (M : RootedModel κ α) := { a : M.World // a ≠ M.root.1 }

variable {M : RootedModel κ α} {s : Formula.Substitution α α}

abbrev substModel (M : RootedModel κ α) (s : Formula.Substitution α α) : RootedModel κ α where
  toModel := M.toModel.substModel s
  root := M.root

end RootedModel

end
