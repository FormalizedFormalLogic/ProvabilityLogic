module

public import SeqPL.Kripke.Basic
public import SeqPL.Formula.Map

@[expose]
public section

/-!
This file is separate from `Kripke/Basic.lean` because `Model.forces_map` states a fact
about `Formula.map`, and `Formula.Map` transitively depends on `Kripke.Basic` (via
`Hilbert.Basic → Gentzen.WithCut → Kripke.Gentzen`); importing `Formula.Map` from
`Kripke.Basic` itself would create an import cycle. `Model.mapModel`, not needing
`Formula.map`, stays in `Kripke.Basic`.
-/

namespace Model

variable {κ α β : Type*} [Nonempty κ] {M : Model κ β}

/-- Forcing a renamed formula is forcing in the pulled-back model. -/
lemma forces_map {f : α → β} {A : Formula α} {x : M.World} :
    x ⊩ A.map f ↔ Model.World.Forces (M := M.mapModel f) x A := by
  induction A generalizing x with
  | atom a => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp A B ihA ihB => simp only [Formula.map_imp, Model.World.Forces]; rw [ihA, ihB]
  | box A ih =>
    simp only [Formula.map_box, Model.World.Forces];
    constructor;
    · intro h y hy; exact ih.mp (h y hy);
    · intro h y hy; exact ih.mpr (h y hy);

end Model

end
