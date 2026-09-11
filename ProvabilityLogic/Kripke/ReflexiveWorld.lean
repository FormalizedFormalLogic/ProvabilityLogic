module

public import ProvabilityLogic.Kripke.Basic

@[expose]
public section

universe u v

variable {α : Type u} [DecidableEq α]

namespace Model.World

variable {κ : Type v} [Nonempty κ] {M : Model κ α}

/--
  A world `x` is `X`-reflexive if `□A 🡒 A` is forced at `x` for every `□A ∈ X`; called
  `Σ`-reflexive in the source.

  - [KK23]
-/
def IsReflexiveOf (X : FormulaFinset α) (x : M.World) : Prop :=
  ∀ {A}, □A ∈ X → x ⊩[_] (□A 🡒 A)

omit [DecidableEq α] in
lemma IsReflexiveOf.anti {X X' : FormulaFinset α} {x : M.World}
  (hx : x.IsReflexiveOf X') (hXX' : X ⊆ X') : x.IsReflexiveOf X :=
  fun hA => hx (hXX' hA)

end Model.World

variable {κ : Type v} [Nonempty κ] {M : Model κ α}

abbrev Model.ReflexiveWorldOf (M : Model κ α) (X : FormulaFinset α) := {x : M.World // x.IsReflexiveOf X}

namespace Model.ReflexiveWorldOf

variable {X : FormulaFinset α}

instance : CoeOut (M.ReflexiveWorldOf X) M.World := ⟨Subtype.val⟩

end Model.ReflexiveWorldOf

end
