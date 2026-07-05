module

public import SeqPL.Logic.GLPoint3.Basic
public import SeqPL.Kripke.RootedModel

@[expose]
public section

variable {α : Type u}

namespace LogicGLPoint3

/--
  **Kripke completeness of `GLPoint3`** with respect to finite rooted linear GL models:
  a formula is a theorem of `GLPoint3` (`GLLin`) iff it is forced at the root of every
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
    -- sorry の理由: `GLPoint3` のKripke完全性（有限根付き線形モデルに関する完全性）．
    -- Valentini & Solitro 1983 の Theorem 10（sequent calculus `LS` の完全性定理）および
    -- Theorem 11 (b), (c)（`GLlin` の有限モデル性・`(ω, >)` に関する完全性）に相当する，
    -- Kripke 意味論の深い議論であり，ユーザー指示により `sorry` とする．
    sorry;

end LogicGLPoint3

end
