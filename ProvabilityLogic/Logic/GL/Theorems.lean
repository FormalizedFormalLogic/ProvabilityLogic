module

public import ProvabilityLogic.Logic.GL.Basic
meta import ProvabilityLogic.Logic.GL.Basic

@[expose]
public section

namespace LogicGL

variable {α : Type*} [DecidableEq α] {A B C : Formula α}

open ProvableHilbert Model.World

/-- The implication-transitivity tautology is a GL theorem. -/
theorem imp_trans : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 A 🡒 C) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

omit [DecidableEq α] in
/-- Contraposition: from `A 🡒 B` derive `∼B 🡒 ∼A`. -/
theorem contra (h : (A 🡒 B) ∈ LogicGL) : (∼B 🡒 ∼A) ∈ LogicGL :=
  mdp (elimContra (A := ∼A) (B := ∼B))
    (impTrans dne (impTrans h dni))

omit [DecidableEq α] in
/-- Axiom `4` transported through `◇`: `◇◇A 🡒 ◇A`. -/
theorem dia4 : (◇◇A 🡒 ◇A) ∈ LogicGL :=
  contra (impTrans modal4 (boxImp dni))

/-- From `∼(A ⋏ ∼B)` derive `A 🡒 B`. -/
theorem imp_of_not_and_not : (∼(A ⋏ ∼B) 🡒 (A 🡒 B)) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

/-- Commutativity of conjunction: `(A ⋏ B) 🡒 (B ⋏ A)`. -/
theorem conj_comm : ((A ⋏ B) 🡒 (B ⋏ A)) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

/-- Distributivity of conjunction over disjunction: `(A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))`. -/
theorem distrib_and_or : ((A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

omit [DecidableEq α] in
/-- Monotonicity of disjunction in the left disjunct: from `A 🡒 B` derive
`(A ⋎ C) 🡒 (B ⋎ C)`. -/
theorem or_imp_left (h : (A 🡒 B) ∈ LogicGL) : ((A ⋎ C) 🡒 (B ⋎ C)) ∈ LogicGL :=
  orElim' (impTrans h orL) orR

/-- `◇⊥` derives `⊥`. -/
theorem dia_bot : (◇(⊥ : Formula α) 🡒 ⊥) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

omit [DecidableEq α] in
/-- Monotonicity of `◇`: from `A 🡒 B` derive `◇A 🡒 ◇B`. -/
theorem diaImp (h : (A 🡒 B) ∈ LogicGL) : (◇A 🡒 ◇B) ∈ LogicGL :=
  contra (boxImp (contra h))

/-- `□A ⋏ ◇B` derives `◇(A ⋏ B)`. -/
theorem imp_dia_and : ((□A ⋏ ◇B) 🡒 ◇(A ⋏ B)) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

/-- Diamond case split: `◇A 🡒 (◇(A ⋏ B) ⋎ ◇(A ⋏ ∼B))`. -/
theorem dia_cases : (◇A 🡒 (◇(A ⋏ B) ⋎ ◇(A ⋏ ∼B))) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

/-- From `∼□A` derive `◇(□A ⋏ ∼A)`, the Hilbert-level terminal-box-refuter fact. -/
theorem dia_boxRefuter : (∼□A 🡒 ◇(□A ⋏ ∼A)) ∈ LogicGL :=
  contra (impTrans (boxImp (imp_of_not_and_not (A := □A) (B := A))) modalL)

/-- The conditional `LogicGLPoint3` dichotomy: from `□((⊡∼A) 🡒 ∼B) ⋎ □((⊡∼B) 🡒 ∼A)`
(the `LogicGLPoint3` axiom, with `A` and `B` substituted for its negations), derive that
`◇A ⋏ ◇B` implies one of `◇(A ⋏ B)`, `◇(A ⋏ ◇B)`, or `◇(B ⋏ ◇A)`. -/
theorem weakPoint3_dichotomy :
    (((□((⊡(∼A)) 🡒 ∼B)) ⋎ (□((⊡(∼B)) 🡒 ∼A))) 🡒
      ((◇A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)))) ∈ LogicGL := by
  apply Kripke.completeness;
  intro κ _ M _ x h hAB;
  have hAB' := forces_and.mp hAB;
  obtain ⟨y, hxy, hyA⟩ := forces_dia.mp hAB'.1;
  obtain ⟨z, hxz, hzB⟩ := forces_dia.mp hAB'.2;
  rcases forces_or.mp h with h1 | h2;
  · have hz := forces_box.mp h1 z hxz;
    by_cases hzA : z ⊩ A;
    · exact forces_or.mpr (Or.inl (forces_or.mpr (Or.inl
        (forces_dia.mpr ⟨z, hxz, forces_and.mpr ⟨hzA, hzB⟩⟩))));
    · have hnbd : ¬ z ⊩ (⊡(∼A)) := by
        intro hc;
        rcases forces_imp.mp hz with hc' | hb;
        · exact hc' hc;
        · exact absurd hzB (forces_neg.mp hb);
      obtain ⟨w, hzw, hwA⟩ : ∃ w, z ≺ w ∧ w ⊩ A := by
        by_contra hcon;
        push Not at hcon;
        exact hnbd (forces_boxdot.mpr
          ⟨forces_neg.mpr hzA, fun w hzw => forces_neg.mpr (hcon w hzw)⟩);
      exact forces_or.mpr (Or.inr (forces_dia.mpr
        ⟨z, hxz, forces_and.mpr ⟨hzB, forces_dia.mpr ⟨w, hzw, hwA⟩⟩⟩));
  · have hy := forces_box.mp h2 y hxy;
    by_cases hyB : y ⊩ B;
    · exact forces_or.mpr (Or.inl (forces_or.mpr (Or.inl
        (forces_dia.mpr ⟨y, hxy, forces_and.mpr ⟨hyA, hyB⟩⟩))));
    · have hnbd : ¬ y ⊩ (⊡(∼B)) := by
        intro hc;
        rcases forces_imp.mp hy with hc' | hb;
        · exact hc' hc;
        · exact absurd hyA (forces_neg.mp hb);
      obtain ⟨w, hyw, hwB⟩ : ∃ w, y ≺ w ∧ w ⊩ B := by
        by_contra hcon;
        push Not at hcon;
        exact hnbd (forces_boxdot.mpr
          ⟨forces_neg.mpr hyB, fun w hyw => forces_neg.mpr (hcon w hyw)⟩);
      exact forces_or.mpr (Or.inl (forces_or.mpr (Or.inr
        (forces_dia.mpr ⟨y, hxy, forces_and.mpr ⟨hyA, forces_dia.mpr ⟨w, hyw, hwB⟩⟩⟩))));

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
