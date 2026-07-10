module

public import SeqPL.Hilbert.Basic

@[expose]
public section

/-!
# Diamond toolbox for the Hilbert calculus `⊢ʰ`

This file collects `◇`- and `⊡`-related modal lemmas at the level of the pure `GL`
Hilbert calculus `⊢ʰ` (`ProvableHilbert`), without introducing any new proof system.
These are the "Step J" lemmas of the `LogicGLPoint3` completeness plan:

- `dia_boxRefuter` (J1): a Hilbert-level version of the terminal-box-refuter fact.
- The `J2` toolbox: monotonicity of `◇`, `K`/`4`-style diamond lemmas, and a diamond
  case split.
- `weakPoint3_dichotomy` (J3): the conditional `LogicGLPoint3` dichotomy, from which the `LogicGLPoint3`
  axiom's consequence for `◇A ⋏ ◇B` follows by instantiating the axiom itself.
-/

namespace ProvableHilbert

variable {α : Type u} {A B : Formula α}

/-! ### Propositional toolbox -/

/-- Contraposition: `A 🡒 B` derives `∼B 🡒 ∼A`. -/
lemma contra (h : ⊢ʰ A 🡒 B) : ⊢ʰ ∼B 🡒 ∼A :=
  mdp (elimContra (A := ∼A) (B := ∼B)) (impTrans dne (impTrans h dni))

/-- From `∼(A ⋏ ∼B)` derive `A 🡒 B`. -/
lemma imp_of_not_and_not : ⊢ʰ ∼(A ⋏ ∼B) 🡒 (A 🡒 B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  have hA : ({∼B, A, ∼(A ⋏ ∼B)} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
  have hnB : ({∼B, A, ∼(A ⋏ ∼B)} : FormulaSet α) ⊢ʰ ∼B := DeducibleHilbert.ofContext (by grind);
  have hAnB : ({∼B, A, ∼(A ⋏ ∼B)} : FormulaSet α) ⊢ʰ A ⋏ ∼B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA) hnB;
  have hn : ({∼B, A, ∼(A ⋏ ∼B)} : FormulaSet α) ⊢ʰ ∼(A ⋏ ∼B) := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hn hAnB;

/-! ### J1: the Hilbert-level terminal-box-refuter lemma -/

/-- **(J1)** From `∼□A` derive `◇(□A ⋏ ∼A)`. -/
lemma dia_boxRefuter : ⊢ʰ ∼□A 🡒 ◇(□A ⋏ ∼A) :=
  contra (impTrans (boxImp (imp_of_not_and_not (A := □A) (B := A))) modalL)

/-- Boxing a curried implication distributes over both arrows:
from `A 🡒 (B 🡒 C)` derive `□A 🡒 (□B 🡒 □C)`. -/
lemma box_curry2 {C : Formula α} (h : ⊢ʰ A 🡒 (B 🡒 C)) : ⊢ʰ □A 🡒 (□B 🡒 □C) :=
  impTrans (boxImp h) modalK

/-- Context-level contraposition: from `X ⊢ʰ A 🡒 B` derive `X ⊢ʰ ∼B 🡒 ∼A`. -/
lemma _root_.DeducibleHilbert.contra {X : FormulaSet α} (h : X ⊢ʰ A 🡒 B) : X ⊢ʰ ∼B 🡒 ∼A :=
  DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (elimContra (A := ∼A) (B := ∼B)))
    (DeducibleHilbert.impTrans (DeducibleHilbert.ofProvable dne)
      (DeducibleHilbert.impTrans h (DeducibleHilbert.ofProvable dni)))

/-- Contraposition on the second component of a curried implication:
from `A 🡒 (B 🡒 C)` derive `A 🡒 (∼C 🡒 ∼B)`. -/
lemma imp_contra_right {C : Formula α} (h : ⊢ʰ A 🡒 (B 🡒 C)) : ⊢ʰ A 🡒 (∼C 🡒 ∼B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hBC : ({A} : FormulaSet α) ⊢ʰ B 🡒 C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h) (DeducibleHilbert.ofContext (by grind));
  exact DeducibleHilbert.contra hBC;

/-- Currying, other direction: from `A 🡒 (B 🡒 C)` derive `(A ⋏ B) 🡒 C`. -/
lemma imp_and_of_imp_imp {C : Formula α} (h : ⊢ʰ A 🡒 (B 🡒 C)) : ⊢ʰ (A ⋏ B) 🡒 C := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hAB : ({A ⋏ B} : FormulaSet α) ⊢ʰ A ⋏ B := DeducibleHilbert.ofContext (by grind);
  have hA : ({A ⋏ B} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hAB;
  have hB : ({A ⋏ B} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hAB;
  have hBC : ({A ⋏ B} : FormulaSet α) ⊢ʰ B 🡒 C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h) hA;
  exact DeducibleHilbert.mdp hBC hB;

/-- From `A` derive `∼(A ⋏ B) 🡒 ∼B`. -/
lemma not_and_imp : ⊢ʰ A 🡒 (∼(A ⋏ B) 🡒 ∼B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have hA : ({B, ∼(A ⋏ B), A} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
  have hB : ({B, ∼(A ⋏ B), A} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind);
  have hAB : ({B, ∼(A ⋏ B), A} : FormulaSet α) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA) hB;
  have hn : ({B, ∼(A ⋏ B), A} : FormulaSet α) ⊢ʰ ∼(A ⋏ B) := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hn hAB;

/-- From `A 🡒 B` derive `∼(A ⋏ B) 🡒 ∼A`. -/
lemma imp_not_and_not : ⊢ʰ (A 🡒 B) 🡒 (∼(A ⋏ B) 🡒 ∼A) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have hA : ({A, ∼(A ⋏ B), A 🡒 B} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
  have hAB' : ({A, ∼(A ⋏ B), A 🡒 B} : FormulaSet α) ⊢ʰ A 🡒 B := DeducibleHilbert.ofContext (by grind);
  have hB : ({A, ∼(A ⋏ B), A 🡒 B} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.mdp hAB' hA;
  have hAnB : ({A, ∼(A ⋏ B), A 🡒 B} : FormulaSet α) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA) hB;
  have hn : ({A, ∼(A ⋏ B), A 🡒 B} : FormulaSet α) ⊢ʰ ∼(A ⋏ B) := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hn hAnB;

/-- De Morgan (hard direction): `∼(A ⋏ B) 🡒 (∼A ⋎ ∼B)`. -/
lemma not_or_of_not_and : ⊢ʰ ∼(A ⋏ B) 🡒 (∼A ⋎ ∼B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  have hnn : ({∼(∼A ⋎ ∼B), ∼(A ⋏ B)} : FormulaSet α) ⊢ʰ ∼(∼A ⋎ ∼B) := DeducibleHilbert.ofContext (by grind);
  have hnnA : ({∼(∼A ⋎ ∼B), ∼(A ⋏ B)} : FormulaSet α) ⊢ʰ ∼∼A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (contra (orL (A := ∼A) (B := ∼B)))) hnn;
  have hA : ({∼(∼A ⋎ ∼B), ∼(A ⋏ B)} : FormulaSet α) ⊢ʰ A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne) hnnA;
  have hnnB : ({∼(∼A ⋎ ∼B), ∼(A ⋏ B)} : FormulaSet α) ⊢ʰ ∼∼B :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (contra (orR (A := ∼A) (B := ∼B)))) hnn;
  have hB : ({∼(∼A ⋎ ∼B), ∼(A ⋏ B)} : FormulaSet α) ⊢ʰ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne) hnnB;
  have hAB : ({∼(∼A ⋎ ∼B), ∼(A ⋏ B)} : FormulaSet α) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA) hB;
  have hn : ({∼(∼A ⋎ ∼B), ∼(A ⋏ B)} : FormulaSet α) ⊢ʰ ∼(A ⋏ B) := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hn hAB;

/-- De Morgan (easy direction): `(∼A ⋏ ∼B) 🡒 ∼(A ⋎ B)`. -/
lemma imp_not_of_or_not : ⊢ʰ (∼A ⋏ ∼B) 🡒 ∼(A ⋎ B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have hAB : ({A ⋎ B, ∼A ⋏ ∼B} : FormulaSet α) ⊢ʰ ∼A ⋏ ∼B := DeducibleHilbert.ofContext (by grind);
  have hnA : ({A ⋎ B, ∼A ⋏ ∼B} : FormulaSet α) ⊢ʰ ∼A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hAB;
  have hnB : ({A ⋎ B, ∼A ⋏ ∼B} : FormulaSet α) ⊢ʰ ∼B :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hAB;
  have hAorB : ({A ⋎ B, ∼A ⋏ ∼B} : FormulaSet α) ⊢ʰ A ⋎ B := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.orElim hnA hnB hAorB;

/-- Excluded middle: `A ⋎ ∼A`. -/
lemma lem : ⊢ʰ A ⋎ ∼A := by
  apply mdp dne;
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hn : ({∼(A ⋎ ∼A)} : FormulaSet α) ⊢ʰ ∼(A ⋎ ∼A) := DeducibleHilbert.ofContext (by grind);
  have hnA : ({∼(A ⋎ ∼A)} : FormulaSet α) ⊢ʰ ∼A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (contra (orL (A := A) (B := ∼A)))) hn;
  have hAorNotA : ({∼(A ⋎ ∼A)} : FormulaSet α) ⊢ʰ A ⋎ ∼A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (orR (A := A) (B := ∼A))) hnA;
  exact DeducibleHilbert.mdp hn hAorNotA;

/-- Distributivity of conjunction over disjunction: `(A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))`. -/
lemma distrib_and_or {C : Formula α} : ⊢ʰ (A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hABC : ({A ⋏ (B ⋎ C)} : FormulaSet α) ⊢ʰ A ⋏ (B ⋎ C) := DeducibleHilbert.ofContext (by grind);
  have hA : ({A ⋏ (B ⋎ C)} : FormulaSet α) ⊢ʰ A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hABC;
  have hBoC : ({A ⋏ (B ⋎ C)} : FormulaSet α) ⊢ʰ B ⋎ C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hABC;
  have caseB : ({A ⋏ (B ⋎ C)} : FormulaSet α) ⊢ʰ B 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by
    apply DeducibleHilbert.deduction_theorem.mp;
    have hB : (insert B ({A ⋏ (B ⋎ C)} : FormulaSet α)) ⊢ʰ B := DeducibleHilbert.ofContext (by grind);
    have hA' : (insert B ({A ⋏ (B ⋎ C)} : FormulaSet α)) ⊢ʰ A :=
      DeducibleHilbert.of_subset_ctx (by grind) hA;
    have hAB : (insert B ({A ⋏ (B ⋎ C)} : FormulaSet α)) ⊢ʰ A ⋏ B :=
      DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA') hB;
    exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable orL) hAB;
  have caseC : ({A ⋏ (B ⋎ C)} : FormulaSet α) ⊢ʰ C 🡒 ((A ⋏ B) ⋎ (A ⋏ C)) := by
    apply DeducibleHilbert.deduction_theorem.mp;
    have hC : (insert C ({A ⋏ (B ⋎ C)} : FormulaSet α)) ⊢ʰ C := DeducibleHilbert.ofContext (by grind);
    have hA' : (insert C ({A ⋏ (B ⋎ C)} : FormulaSet α)) ⊢ʰ A :=
      DeducibleHilbert.of_subset_ctx (by grind) hA;
    have hAC : (insert C ({A ⋏ (B ⋎ C)} : FormulaSet α)) ⊢ʰ A ⋏ C :=
      DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA') hC;
    exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable orR) hAC;
  exact DeducibleHilbert.orElim caseB caseC hBoC;

/-! ### J2: K/4 toolbox for `◇` -/

/-- **(J2)** Monotonicity of `◇`: from `A 🡒 B` derive `◇A 🡒 ◇B`. -/
lemma diaImp (h : ⊢ʰ A 🡒 B) : ⊢ʰ ◇A 🡒 ◇B := contra (boxImp (contra h))

/-- `□(A 🡒 B) ⋏ ◇A` derives `◇(A ⋏ B)`, the implicational form of `imp_dia_and`. -/
lemma dia_box_imp : ⊢ʰ (□(A 🡒 B) ⋏ ◇A) 🡒 ◇(A ⋏ B) :=
  imp_and_of_imp_imp (imp_contra_right (box_curry2 imp_not_and_not))

/-- **(J2)** `□A ⋏ ◇B` derives `◇(A ⋏ B)`. -/
lemma imp_dia_and : ⊢ʰ (□A ⋏ ◇B) 🡒 ◇(A ⋏ B) :=
  imp_and_of_imp_imp (imp_contra_right (box_curry2 not_and_imp))

/-- `◇` distributes over disjunction: `◇(A ⋎ B) 🡒 (◇A ⋎ ◇B)`. -/
lemma dia_or : ⊢ʰ ◇(A ⋎ B) 🡒 (◇A ⋎ ◇B) :=
  impTrans (contra (impTrans imp_box_and (boxImp imp_not_of_or_not))) not_or_of_not_and

/-- **(J2)** Axiom `4` transported through `◇`: `◇◇A 🡒 ◇A`. -/
lemma dia4 : ⊢ʰ ◇◇A 🡒 ◇A :=
  contra (impTrans modal4 (boxImp dni))

/-- **(J2)** `◇⊥` derives `⊥`. -/
lemma dia_bot : ⊢ʰ ◇(⊥ : Formula α) 🡒 ⊥ := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have h1 : ({◇(⊥ : Formula α)} : FormulaSet α) ⊢ʰ □(∼(⊥ : Formula α)) :=
    DeducibleHilbert.ofProvable (nec top);
  have h2 : ({◇(⊥ : Formula α)} : FormulaSet α) ⊢ʰ ◇(⊥ : Formula α) := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp h2 h1;

/-- **(J2)** Diamond case split: `◇A 🡒 (◇(A ⋏ B) ⋎ ◇(A ⋏ ∼B))`. -/
lemma dia_cases : ⊢ʰ ◇A 🡒 (◇(A ⋏ B) ⋎ ◇(A ⋏ ∼B)) := by
  have step1 : ⊢ʰ A 🡒 (A ⋏ (B ⋎ ∼B)) := by
    apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
    have hA : ({A} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
    have hBB : ({A} : FormulaSet α) ⊢ʰ B ⋎ ∼B := DeducibleHilbert.ofProvable lem;
    exact DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hA) hBB;
  exact impTrans (diaImp (impTrans step1 distrib_and_or)) dia_or;

/-- Post-composing the conclusion of a curried implication: from `A 🡒 (B 🡒 C)` and
`C 🡒 D` derive `A 🡒 (B 🡒 D)`. -/
lemma imp_postcompose {C D : Formula α} (h : ⊢ʰ A 🡒 (B 🡒 C)) (h2 : ⊢ʰ C 🡒 D) : ⊢ʰ A 🡒 (B 🡒 D) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have hB : ({B, A} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind);
  have hA : ({B, A} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
  have hBC : ({B, A} : FormulaSet α) ⊢ʰ B 🡒 C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h) hA;
  have hC : ({B, A} : FormulaSet α) ⊢ʰ C := DeducibleHilbert.mdp hBC hB;
  exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h2) hC;

/-- Contraposition-under-implication: `(A 🡒 ∼B) 🡒 (B 🡒 ∼A)`. -/
lemma imp_contra : ⊢ʰ (A 🡒 ∼B) 🡒 (B 🡒 ∼A) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have hA : ({A, B, A 🡒 ∼B} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
  have hAB : ({A, B, A 🡒 ∼B} : FormulaSet α) ⊢ʰ A 🡒 ∼B := DeducibleHilbert.ofContext (by grind);
  have hnB : ({A, B, A 🡒 ∼B} : FormulaSet α) ⊢ʰ ∼B := DeducibleHilbert.mdp hAB hA;
  have hB : ({A, B, A 🡒 ∼B} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnB hB;

/-- Commutativity of conjunction: `(A ⋏ B) 🡒 (B ⋏ A)`. -/
lemma conj_comm : ⊢ʰ (A ⋏ B) 🡒 (B ⋏ A) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hAB : ({A ⋏ B} : FormulaSet α) ⊢ʰ A ⋏ B := DeducibleHilbert.ofContext (by grind);
  have hA : ({A ⋏ B} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hAB;
  have hB : ({A ⋏ B} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hAB;
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hB) hA;

/-- Monotonicity of disjunction in the left disjunct: from `A 🡒 B` derive
`(A ⋎ C) 🡒 (B ⋎ C)`. -/
lemma or_imp_left {C : Formula α} (h : ⊢ʰ A 🡒 B) : ⊢ʰ (A ⋎ C) 🡒 (B ⋎ C) :=
  orElim' (impTrans h orL) orR

/-- Inserting a disjunct in the middle: `(A ⋎ C) 🡒 ((A ⋎ B) ⋎ C)`. -/
lemma or_insert_middle {C : Formula α} : ⊢ʰ (A ⋎ C) 🡒 ((A ⋎ B) ⋎ C) :=
  orElim' (impTrans orL orL) orR

/-! ### J3: the conditional `LogicGLPoint3` dichotomy -/

/-- `((⊡∼A) 🡒 ∼B) 🡒 (A ⋎ ◇A)`, obtained by unfolding `⊡∼A = ∼A ⋏ □∼A` and taking
the De Morgan dual. -/
lemma notBoxdot_imp_dia : ⊢ʰ ∼(⊡(∼A)) 🡒 (A ⋎ ◇A) :=
  impTrans not_or_of_not_and (or_imp_left dne)

/-- The propositional core of the `LogicGLPoint3` dichotomy: `((⊡∼A) 🡒 ∼B) 🡒 (B 🡒 (A ⋎ ◇A))`. -/
lemma boxdotNeg_imp : ⊢ʰ ((⊡(∼A)) 🡒 ∼B) 🡒 (B 🡒 (A ⋎ ◇A)) :=
  imp_postcompose imp_contra notBoxdot_imp_dia

/-- The diamond half of the `LogicGLPoint3` dichotomy, boxed and combined with `◇B`. -/
lemma dia_disj_split :
    ⊢ʰ (□(B 🡒 (A ⋎ ◇A)) ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) := by
  have h1 : ⊢ʰ (□(B 🡒 (A ⋎ ◇A)) ⋏ ◇B) 🡒 ◇(B ⋏ (A ⋎ ◇A)) := dia_box_imp;
  have h2 : ⊢ʰ ◇(B ⋏ (A ⋎ ◇A)) 🡒 (◇(B ⋏ A) ⋎ ◇(B ⋏ ◇A)) :=
    impTrans (diaImp distrib_and_or) dia_or;
  have h3 : ⊢ʰ (◇(B ⋏ A) ⋎ ◇(B ⋏ ◇A)) 🡒 (◇(A ⋏ B) ⋎ ◇(B ⋏ ◇A)) :=
    or_imp_left (diaImp conj_comm);
  have h4 : ⊢ʰ (◇(A ⋏ B) ⋎ ◇(B ⋏ ◇A)) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) :=
    or_insert_middle;
  exact impTrans (impTrans (impTrans h1 h2) h3) h4;

/-- One half of **(J3)**: `□((⊡∼A) 🡒 ∼B)` derives the `LogicGLPoint3` dichotomy conclusion. -/
lemma weakPoint3_dichotomy_onesided :
    ⊢ʰ □((⊡(∼A)) 🡒 ∼B) 🡒 ((◇A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A))) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have hbox : (insert (◇A ⋏ ◇B) ({□((⊡(∼A)) 🡒 ∼B)} : FormulaSet α)) ⊢ʰ □((⊡(∼A)) 🡒 ∼B) :=
    DeducibleHilbert.ofContext (by grind);
  have hBox2 : (insert (◇A ⋏ ◇B) ({□((⊡(∼A)) 🡒 ∼B)} : FormulaSet α)) ⊢ʰ □(B 🡒 (A ⋎ ◇A)) :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable (boxImp boxdotNeg_imp)) hbox;
  have hAB : (insert (◇A ⋏ ◇B) ({□((⊡(∼A)) 🡒 ∼B)} : FormulaSet α)) ⊢ʰ ◇A ⋏ ◇B :=
    DeducibleHilbert.ofContext (by grind);
  have hDiaB : (insert (◇A ⋏ ◇B) ({□((⊡(∼A)) 🡒 ∼B)} : FormulaSet α)) ⊢ʰ ◇B :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hAB;
  have hAnd : (insert (◇A ⋏ ◇B) ({□((⊡(∼A)) 🡒 ∼B)} : FormulaSet α)) ⊢ʰ □(B 🡒 (A ⋎ ◇A)) ⋏ ◇B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hBox2) hDiaB;
  exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dia_disj_split) hAnd;

/-- Permuting the three disjuncts of the `LogicGLPoint3` dichotomy conclusion after swapping
`A` and `B`. -/
lemma dichotomy_disj_permute :
    ⊢ʰ ((◇(B ⋏ A) ⋎ ◇(B ⋏ ◇A)) ⋎ ◇(A ⋏ ◇B)) 🡒
      ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) := by
  have case1 : ⊢ʰ ◇(B ⋏ A) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) :=
    impTrans (impTrans (diaImp conj_comm) orL) orL;
  have case2 : ⊢ʰ ◇(B ⋏ ◇A) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) := orR;
  have case3 : ⊢ʰ ◇(A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) :=
    impTrans orR orL;
  exact orElim' (orElim' case1 case2) case3;

/-- The other half of **(J3)**: `□((⊡∼B) 🡒 ∼A)` derives the same `LogicGLPoint3` dichotomy
conclusion (obtained from `weakPoint3_dichotomy_onesided` by swapping `A` and `B`,
then permuting the resulting disjuncts back into place). -/
lemma weakPoint3_dichotomy_onesided' :
    ⊢ʰ □((⊡(∼B)) 🡒 ∼A) 🡒 ((◇A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A))) := by
  have base : ⊢ʰ □((⊡(∼B)) 🡒 ∼A) 🡒 ((◇B ⋏ ◇A) 🡒 ((◇(B ⋏ A) ⋎ ◇(B ⋏ ◇A)) ⋎ ◇(A ⋏ ◇B))) :=
    weakPoint3_dichotomy_onesided (A := B) (B := A);
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have hbase : (insert (◇A ⋏ ◇B) ({□((⊡(∼B)) 🡒 ∼A)} : FormulaSet α)) ⊢ʰ
      □((⊡(∼B)) 🡒 ∼A) 🡒 ((◇B ⋏ ◇A) 🡒 ((◇(B ⋏ A) ⋎ ◇(B ⋏ ◇A)) ⋎ ◇(A ⋏ ◇B))) :=
    DeducibleHilbert.ofProvable base;
  have hbox : (insert (◇A ⋏ ◇B) ({□((⊡(∼B)) 🡒 ∼A)} : FormulaSet α)) ⊢ʰ □((⊡(∼B)) 🡒 ∼A) :=
    DeducibleHilbert.ofContext (by grind);
  have hinner : (insert (◇A ⋏ ◇B) ({□((⊡(∼B)) 🡒 ∼A)} : FormulaSet α)) ⊢ʰ
      (◇B ⋏ ◇A) 🡒 ((◇(B ⋏ A) ⋎ ◇(B ⋏ ◇A)) ⋎ ◇(A ⋏ ◇B)) :=
    DeducibleHilbert.mdp hbase hbox;
  have hAB : (insert (◇A ⋏ ◇B) ({□((⊡(∼B)) 🡒 ∼A)} : FormulaSet α)) ⊢ʰ ◇A ⋏ ◇B :=
    DeducibleHilbert.ofContext (by grind);
  have hBA : (insert (◇A ⋏ ◇B) ({□((⊡(∼B)) 🡒 ∼A)} : FormulaSet α)) ⊢ʰ ◇B ⋏ ◇A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable conj_comm) hAB;
  have hres : (insert (◇A ⋏ ◇B) ({□((⊡(∼B)) 🡒 ∼A)} : FormulaSet α)) ⊢ʰ
      (◇(B ⋏ A) ⋎ ◇(B ⋏ ◇A)) ⋎ ◇(A ⋏ ◇B) :=
    DeducibleHilbert.mdp hinner hBA;
  exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dichotomy_disj_permute) hres;

/-- **(J3)** The conditional `LogicGLPoint3` dichotomy: from `□((⊡∼A) 🡒 ∼B) ⋎ □((⊡∼B) 🡒 ∼A)`
(the `LogicGLPoint3` axiom, with `A` and `B` substituted for its negations), derive that
`◇A ⋏ ◇B` implies one of `◇(A ⋏ B)`, `◇(A ⋏ ◇B)`, or `◇(B ⋏ ◇A)`. -/
lemma weakPoint3_dichotomy :
    ⊢ʰ ((□((⊡(∼A)) 🡒 ∼B)) ⋎ (□((⊡(∼B)) 🡒 ∼A))) 🡒
      ((◇A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A))) :=
  orElim' weakPoint3_dichotomy_onesided weakPoint3_dichotomy_onesided'

end ProvableHilbert
