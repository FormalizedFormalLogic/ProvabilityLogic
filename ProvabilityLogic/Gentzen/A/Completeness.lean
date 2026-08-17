module

public import ProvabilityLogic.Gentzen.A.Kripke
public import ProvabilityLogic.Logic.A.Basic

/-!
# Cut-free completeness and semantic cut elimination for the sequent calculus for `A`

Completeness of level-`1` `LogicA`-Gentzen provability with respect to `RootedModel.graftOmega`
semantics, the resulting `List.TFAE` package tying it to `LogicGL`-provability, semantic cut
elimination, and the connection to `LogicA`-provability. Original to this formalization: it
assembles `LogicGL` completeness, `RootedModel.graftOmega`, and a pigeonhole argument for a
reflexive world, following the structure of the analogous result for `LogicD`, but the level-`1`
statement for `LogicA` itself is not stated in this form in the literature.
-/

@[expose]
public section

universe u v

variable {α : Type u} [DecidableEq α]

open LogicGL Model
open scoped LogicA

/-- Completeness of level-`1` cut-free `LogicA`-Gentzen provability w.r.t. `graftOmega`
semantics: if a sequent is forced at the root of every ω-graft extension of every finite
rooted `GL` model, it is cut-free provable. -/
theorem LogicA.ProvableGentzen.completeness {Γ Δ : FormulaFinset α}
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    ∀ (a : M.World) (Rra : M.root.1 ≺ a),
    (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ)) :
  ⊢ᵍ[A] (Γ ⟹[1] Δ) := by
  sorry

/-- The four equivalent characterizations of `Γ ⟹ Δ` being a theorem of level-`1`
`LogicA.ProofGentzen`: with-cut provability, cut-free provability, forcing at the root of
every ω-graft extension of every finite rooted `GL` model, and a `GL`-provable deduction-
theorem form. -/
theorem LogicA.semantical_TFAE {Γ Δ : FormulaFinset α} : [
    ⊢ᵍᶜ[A] (Γ ⟹[1] Δ),
    ⊢ᵍ[A] (Γ ⟹[1] Δ),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      ∀ (a : M.World) (Rra : M.root.1 ≺ a),
      (M.graftOmega ⟨a, fun h => Std.Irrefl.irrefl _ (h ▸ Rra)⟩).root.1 ⊩[_] (Γ ⟹ Δ),
    ∃ n : ℕ, ⊢ᵍ[GL] (Γ ⟹ insert (□^[n]⊥) Δ)
  ].TFAE := by
  sorry

/-- Semantic cut elimination for level-`1` `LogicA`-Gentzen provability: every with-cut
proof yields a cut-free proof. -/
theorem LogicA.GentzenWithCutProvable.cutElimination {Γ Δ : FormulaFinset α}
  (h : ⊢ᵍᶜ[A] (Γ ⟹[1] Δ)) : ⊢ᵍ[A] (Γ ⟹[1] Δ) := by
  sorry

/-- `LogicA`-provability is characterized by cut-free provability in the two-layered
sequent calculus for `A`, at level `1`. -/
theorem LogicA.iff_provable_provableGentzen {A : Formula α} :
  A ∈ LogicA ↔ ⊢ᵍ[A] (∅ ⟹[1] {A}) := by
  sorry

end
