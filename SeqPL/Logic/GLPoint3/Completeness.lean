module

public import SeqPL.Logic.GLPoint3.Basic
public import SeqPL.Kripke.RootedModel

@[expose]
public section

variable {α : Type u}

namespace LogicGLPoint3

/--
  **Kripke completeness of `GLPoint3`** with respect to finite rooted linear GL models:
  a formula is a theorem of `LogicGLPoint3` iff it is forced at the root of every
  finite rooted linear GL model.

  The soundness direction is `LogicGLPoint3.sound`. The completeness direction
  corresponds to Theorem 10 (completeness of the sequent calculus `LS`) and
  Theorem 11 (b), (c) (finite model property and completeness with respect to
  `(ω, >)`) of Valentini & Solitro 1983.
-/
theorem iff_forces_root [DecidableEq α] {A : Formula α} :
  A ∈ LogicGLPoint3 ↔
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩ A := by
  constructor;
  . intro h κ _ M _;
    exact LogicGLPoint3.sound h M.root.1;
  . intro h;
    -- Reason for the sorry: this is the Kripke completeness of `GLPoint3` with respect to
    -- finite rooted linear GL models, corresponding to Theorem 10 (completeness of the
    -- sequent calculus `LS`) and Theorem 11 (b), (c) (finite model property and
    -- completeness with respect to `(ω, >)`) of Valentini & Solitro 1983. Left as `sorry`
    -- per user instruction, as it requires a substantial Kripke semantics argument.
    sorry;

end LogicGLPoint3

end
