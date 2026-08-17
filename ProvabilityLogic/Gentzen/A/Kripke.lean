module

public import ProvabilityLogic.Gentzen.A.Basic
public import ProvabilityLogic.Gentzen.GL.Kripke
public import ProvabilityLogic.Gentzen.GL.WithCut
public import ProvabilityLogic.Kripke.GraftOmega

@[expose]
public section

variable {α : Type u} [DecidableEq α]

open LogicA

/-- Soundness of level-`0` `LogicA`-with-cut proofs w.r.t. arbitrary `IsGL` Kripke models. -/
theorem LogicA.GentzenWithCutProvable.soundness_zero {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[0] Δ)) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] → M ⊧ (Γ ⟹ Δ) := by
  sorry

/-- Soundness of level-`1` `LogicA`-with-cut proofs at the root of every ω-graft model built
from a finite rooted `GL` model. -/
theorem LogicA.GentzenWithCutProvable.soundness_graftOmega {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[1] Δ)) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
  ∀ (a : M.World) (Rra : M.root.1 ≺ a),
  (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ) := by
  sorry

end
