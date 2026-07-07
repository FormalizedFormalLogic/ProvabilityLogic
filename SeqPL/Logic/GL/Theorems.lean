module

public import SeqPL.Logic.GL.Basic
meta import SeqPL.Logic.GL.Basic

@[expose]
public section

namespace LogicGL

variable {α : Type*} [DecidableEq α] {A B C : Formula α}

omit [DecidableEq α] in
/-- The implication-transitivity tautology is a GL theorem: built from the propositional
atoms `#0, #1, #2` (checked mechanically via `decide`, using `LogicGL.decidableMem`) and
then transported to arbitrary `A B C : Formula α` along the atom-to-formula assignment
`#0 ↦ A, #1 ↦ B, #2 ↦ C`, using closure of `LogicGL` under substitution
(`ProvableHilbert.subst`, `LogicGL.iff_provableHilbert`). -/
theorem imp_trans : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 A 🡒 C) ∈ @LogicGL α := by
  suffices h : ((#0 🡒 #1) 🡒 (#1 🡒 #2) 🡒 #0 🡒 #2) ∈ @LogicGL ℕ by
    simpa using ProvableHilbert.subst (s := fun n =>
      match n with
      | 0 => A
      | 1 => B
      | _ => C
    ) h;
  native_decide;

end LogicGL

/-! ### Examples from Maggesi–Perini Brogi [MPB23], §6.3

Ground instances (over `Formula ℕ`, with a fixed atom `#0` standing in for the schema
variable used in the paper) of the meta-mathematical examples discussed there, checked
automatically via `LogicGL.decidableMem` (itself running the labelled proof search
`search0`). The kernel-level `decide` tactic gets stuck unfolding `search0`'s
well-founded recursion, so `native_decide` (trusting the compiler) is used instead;
`#eval decide (... ∈ LogicGL)` confirms the same results via the same instance. -/

/-- Undecidability of consistency: if `PA` does not prove its own inconsistency, then its
consistency is undecidable. -/
example : ∼□□⊥ 🡒 (∼□(∼□⊥) ⋏ ∼□(∼∼□⊥)) ∈ @LogicGL ℕ := by native_decide

/-- Undecidability of Gödel's formula: if `A` is a fixed point of `¬□A` and `PA` does not
prove its own inconsistency, then `A` is undecidable in `PA`. -/
example : (□((#0) 🡘 ∼□#0) ⋏ ∼□□⊥) 🡒 (∼□#0 ⋏ ∼□(∼#0)) ∈ @LogicGL ℕ := by native_decide

/-- Reflection and iterated consistency. -/
example : □((□(#0) 🡒 #0) 🡒 ◇◇⊤) 🡒 ◇◇⊤ 🡒 □#0 🡒 #0 ∈ @LogicGL ℕ := by native_decide

/-- Formalised Gödel's second incompleteness theorem: if `PA` is consistent, it cannot
prove its own consistency. -/
example : ∼□⊥ 🡒 ∼□◇⊤ ∈ @LogicGL ℕ := by native_decide

end
