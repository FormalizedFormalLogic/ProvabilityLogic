module

public import ProvabilityLogic.Logic.GL.Theorems
public import ProvabilityLogic.Logic.SumNormal
public import ProvabilityLogic.Kripke.Linearity

/-!
# `LogicGLPoint3`: definition, combinators, the Hilbert-level witness lemma, and rule soundness

This file bundles: the definition of `LogicGLPoint3` and its `subst`-free induction principle
(`LogicGLPoint3.substlessInduction`) together with the basic propositional combinators; the
Hilbert-level witness lemma `LogicGLPoint3.witness` (Step K), the Hilbert-calculus counterpart of
`Model.exists_linear_witness`; and the Hilbert soundness of the `boxGLPoint3` Gentzen rule
`LogicGLPoint3.boxGLPoint3` (Step L), the counterpart of `Model.validate_gentzen_boxGLPoint3`
(both in `ProvabilityLogic/Gentzen/GLPoint3/Kripke.lean`).
-/

@[expose]
public section

open LogicGL

/--
The normal extension of `GL` by the weak linearity axiom `.3`, i.e. `□(⊡A 🡒 B) ⋎ □(⊡B 🡒 A)`.
Also known as `GLLin` or `K4.3W`.

- [SV82]
-/
abbrev LogicGLPoint3 {α} : Logic α := LogicGL ⊕ᴸ { (□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A)) | (A) (B) }

namespace LogicGLPoint3

lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicGLPoint3 :=
  Logic.sumNormal.mem₁ h

lemma provable_axiomWeakPoint3 {A B : Formula α} :
    ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A))) ∈ LogicGLPoint3 :=
  Logic.sumNormal.mem₂ ⟨A, B, rfl⟩

section

/-- Intrinsic definition of `LogicGLPoint3` avoiding `subst` (for `LogicGLPoint3.substlessInduction`). -/
protected inductive substless : Logic α
  | provable_GL {A} : A ∈ LogicGL → LogicGLPoint3.substless A
  | axiomWeakPoint3 (A B : Formula α) : LogicGLPoint3.substless ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A)))
  | mdp {A B} : LogicGLPoint3.substless (A 🡒 B) → LogicGLPoint3.substless A → LogicGLPoint3.substless B
  | nec {A} : LogicGLPoint3.substless A → LogicGLPoint3.substless (□A)

private lemma substless.eq_LogicGLPoint3 : LogicGLPoint3.substless (α := α) = LogicGLPoint3 := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | provable_GL h => exact provable_of_provable_GL h;
    | axiomWeakPoint3 A B => exact provable_axiomWeakPoint3;
    | mdp _ _ ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA;
    | nec _ ih => exact Logic.sumNormal.nec ih;
  . intro h;
    induction h with
    | mem₁ h => exact LogicGLPoint3.substless.provable_GL h;
    | mem₂ h =>
      obtain ⟨B, C, rfl⟩ := h;
      exact LogicGLPoint3.substless.axiomWeakPoint3 B C;
    | mdp _ _ ihAB ihA => exact LogicGLPoint3.substless.mdp ihAB ihA;
    | nec _ ih => exact LogicGLPoint3.substless.nec ih;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | provable_GL h => exact LogicGLPoint3.substless.provable_GL (ProvableHilbert.subst h);
      | axiomWeakPoint3 B C => exact LogicGLPoint3.substless.axiomWeakPoint3 _ _;
      | mdp _ _ ihAB ihA => exact LogicGLPoint3.substless.mdp ihAB ihA;
      | nec _ ih => exact LogicGLPoint3.substless.nec ih;

variable {A : Formula α}

private lemma substless.toLogicGLPoint3 (h : LogicGLPoint3.substless A) : A ∈ LogicGLPoint3 :=
  substless.eq_LogicGLPoint3 ▸ h

private lemma substless.ofLogicGLPoint3 (h : A ∈ LogicGLPoint3) : LogicGLPoint3.substless A :=
  substless.eq_LogicGLPoint3.symm ▸ h

/-- Induction principle for `LogicGLPoint3` avoiding `subst`: it suffices to cover the
GL part, the axiom `.3` instances, modus ponens, and necessitation. -/
protected lemma substlessInduction
  {motive : (A : Formula α) → A ∈ LogicGLPoint3 → Prop}
  (provable_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (axiomWeakPoint3 : ∀ {A B}, motive ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A))) provable_axiomWeakPoint3)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicGLPoint3} → {hA : A ∈ LogicGLPoint3} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumNormal.mdp hAB hA))
    (nec : ∀ {A}, {hA : A ∈ LogicGLPoint3} → motive A hA → motive (□A) (Logic.sumNormal.nec hA)) :
    ∀ {A}, (h : A ∈ LogicGLPoint3) → motive A h := by
  intro A h;
  induction substless.ofLogicGLPoint3 h with
  | provable_GL hg => exact provable_GL hg;
  | axiomWeakPoint3 A B => exact axiomWeakPoint3;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := substless.toLogicGLPoint3 hAB) (hA := substless.toLogicGLPoint3 hA) (ihAB _) (ihA _);
  | nec hA ihA =>
    exact nec (hA := substless.toLogicGLPoint3 hA) (ihA _);

end

public section combinators

variable {A B C : Formula α}

lemma of_GL (h : ⊢ʰ[GL] A) : A ∈ LogicGLPoint3 := provable_of_provable_GL h

lemma mdp' (h : ⊢ʰ[GL] (A 🡒 B)) (hA : A ∈ LogicGLPoint3) : B ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (of_GL h) hA

/-- Chained implication, at the `⊢ʰ[GL]` level, used to prove `LogicGLPoint3.impTrans`. -/
private lemma imp_chain : ⊢ʰ[GL] (A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{B 🡒 C, A 🡒 B}`, goal `A 🡒 C`
  have hAB : ({B 🡒 C, A 🡒 B} : FormulaSet α) ⊢ʰ[GL] A 🡒 B := DeducibleHilbert.ofContext (by grind);
  have hBC : ({B 🡒 C, A 🡒 B} : FormulaSet α) ⊢ʰ[GL] B 🡒 C := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.impTrans hAB hBC;

lemma impTrans
    (hAB : (A 🡒 B) ∈ LogicGLPoint3) (hBC : (B 🡒 C) ∈ LogicGLPoint3) :
    (A 🡒 C) ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (mdp' imp_chain hAB) hBC

lemma andIntro' (hA : A ∈ LogicGLPoint3) (hB : B ∈ LogicGLPoint3) : (A ⋏ B) ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (mdp' ProvableHilbert.andIntro hA) hB

lemma andElimL' (h : (A ⋏ B) ∈ LogicGLPoint3) : A ∈ LogicGLPoint3 := mdp' ProvableHilbert.andElimL h

lemma andElimR' (h : (A ⋏ B) ∈ LogicGLPoint3) : B ∈ LogicGLPoint3 := mdp' ProvableHilbert.andElimR h

lemma orIntroL' (B : Formula α) (hA : A ∈ LogicGLPoint3) :
    (A ⋎ B) ∈ LogicGLPoint3 :=
  mdp' ProvableHilbert.orIntroL hA

lemma orIntroR' (A : Formula α) (hB : B ∈ LogicGLPoint3) :
    (A ⋎ B) ∈ LogicGLPoint3 :=
  mdp' ProvableHilbert.orIntroR hB

lemma orElim'
    (hAC : (A 🡒 C) ∈ LogicGLPoint3) (hBC : (B 🡒 C) ∈ LogicGLPoint3)
    (hAB : (A ⋎ B) ∈ LogicGLPoint3) : C ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (Logic.sumNormal.mdp (mdp' ProvableHilbert.orElim hAC) hBC) hAB

lemma box' (h : (A 🡒 B) ∈ LogicGLPoint3) : (□A 🡒 □B) ∈ LogicGLPoint3 :=
  mdp' ProvableHilbert.modalK (Logic.sumNormal.nec h)

end combinators

end LogicGLPoint3

/-!
# Step K: the Hilbert-level witness lemma for `GL.3`

This is the Hilbert-calculus counterpart of `Model.exists_linear_witness`
(`ProvabilityLogic/Gentzen/GLPoint3/Kripke.lean`). For a nonempty finite `Δ`, `LogicGLPoint3` proves

`(⋀_{A∈Δ} ∼□A) 🡒 ⋁_{∅≠S⊆Δ} ◇θ_S`,

where `θ_S := ⋀_{A∈S}(∼A ⋏ □A) ⋏ ⋀_{A∈Δ\S} ∼□A`. This is the key combinatorial fact
driving the Hilbert-level soundness of the `boxGLPoint3` Gentzen rule.
-/

namespace LogicGLPoint3

universe u
variable {α : Type u} [DecidableEq α]

/-- `theta S T := ⋀_{A∈S}(∼A ⋏ □A) ⋏ ⋀_{A∈T} ∼□A`, the "witness formula" attached to a
pair of disjoint finite sets: `S` collects the formulas terminally refuted (and forever
afterwards forced), `T` collects the formulas whose refutation is still postponed. -/
noncomputable def theta (S T : FormulaFinset α) : Formula α :=
  (⋀ (S.image (fun A => ∼A ⋏ □A))) ⋏ (⋀ (T.image (fun A => ∼□A)))

/-- The disjunction of `◇θ_S` over all nonempty `S ⊆ Δ`, with complement taken in `Δ`. -/
noncomputable def witnessDisj (Δ : FormulaFinset α) : Formula α :=
  ⋁ ((Δ.powerset.erase ∅).image (fun S => ◇ (theta S (Δ \ S))))

end LogicGLPoint3

namespace LogicGL.ProvableHilbert

public section diamondCombinators

variable {α : Type u} {A : Formula α}

/-- Right-conjunction congruence, at the plain `⊢ʰ[GL]` level: from `B 🡒 C` derive
`(A ⋏ B) 🡒 (A ⋏ C)`. -/
lemma and_congr_right {B C : Formula α} (h : ⊢ʰ[GL] B 🡒 C) : ⊢ʰ[GL] (A ⋏ B) 🡒 (A ⋏ C) :=
  ctxAndIntroRule andL (impTrans andR h)

/-- `◇∼A` derives `∼□A` (the direct half of the `◇`/`□` De Morgan bridge). -/
lemma dia_neg_imp_not_box : ⊢ʰ[GL] ◇(∼A) 🡒 ∼□A := LogicGL.contra (boxImp dni)

/-- `∼□A` derives `◇∼A` (the converse half of the `◇`/`□` De Morgan bridge). -/
lemma not_box_imp_dia_neg : ⊢ʰ[GL] ∼□A 🡒 ◇(∼A) := LogicGL.contra (boxImp dne)

/-- Transporting `∼□A` one `◇`-step deeper still derives `∼□A`. -/
lemma dia_of_not_box_imp_not_box : ⊢ʰ[GL] ◇(∼□A) 🡒 ∼□A :=
  impTrans (LogicGL.diaImp not_box_imp_dia_neg) (impTrans LogicGL.dia4 dia_neg_imp_not_box)

section
variable [DecidableEq α]
variable {S T : FormulaFinset α} {D : Formula α}

/-- `theta S (insert D T)` (`D ∉ T`) is derivable from `theta S T ⋏ ∼□D`: joining `D` to
the "postponed" side `T` of the witness formula. -/
lemma theta_join_complement :
    ⊢ʰ[GL] (LogicGLPoint3.theta S T ⋏ ∼□D) 🡒 LogicGLPoint3.theta S (insert D T) := by
  unfold LogicGLPoint3.theta;
  rw [Finset.image_insert];
  exact ctxAndIntroRule (impTrans andL andL)
    (impTrans (ctxAndIntroRule andR (impTrans andL andR)) imp_fconj_insert);

/-- `theta (insert D S) T` (`D ∉ S`) is derivable from `theta S T ⋏ (∼D ⋏ □D)`: joining `D`
to the "terminally refuted" side `S` of the witness formula. -/
lemma theta_join_S :
    ⊢ʰ[GL] (LogicGLPoint3.theta S T ⋏ (∼D ⋏ □D)) 🡒 LogicGLPoint3.theta (insert D S) T := by
  unfold LogicGLPoint3.theta;
  rw [Finset.image_insert];
  exact ctxAndIntroRule
    (impTrans (ctxAndIntroRule andR (impTrans andL andL)) imp_fconj_insert)
    (impTrans andL andR);

end

end diamondCombinators

end LogicGL.ProvableHilbert

namespace LogicGLPoint3

variable {α : Type u}

public section combinators3

variable {A B C : Formula α} {Q : FormulaFinset α}

/-- Implicational disjunction elimination for `LogicGLPoint3`: from `(A 🡒 C) ∈ L` and
`(B 🡒 C) ∈ L` derive `((A ⋎ B) 🡒 C) ∈ L`, without needing `(A ⋎ B) ∈ L` itself
(unlike `orElim'`, which discharges the disjunction as a hypothesis). -/
lemma orElim_imp'
    (hAC : (A 🡒 C) ∈ LogicGLPoint3) (hBC : (B 🡒 C) ∈ LogicGLPoint3) :
    ((A ⋎ B) 🡒 C) ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (mdp' ProvableHilbert.orElim hAC) hBC

/-- Membership in the disjunction, at the `LogicGLPoint3` level: from `A ∈ Q`, `A 🡒 ⋁Q`
holds in `LogicGLPoint3` (lifted from the `⊢ʰ[GL]`-level `imp_mem_fdisj`). -/
lemma mem_imp_fdisj' (h : A ∈ Q) :
    (A 🡒 (⋁ Q)) ∈ LogicGLPoint3 :=
  of_GL (ProvableHilbert.imp_mem_fdisj h)

lemma imp_and_intro'
    (hCA : (C 🡒 A) ∈ LogicGLPoint3) (hCB : (C 🡒 B) ∈ LogicGLPoint3) :
    (C 🡒 (A ⋏ B)) ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (mdp' ProvableHilbert.ctxAndIntro hCA) hCB

section
variable [DecidableEq α]

/-- Disjunction elimination for `LogicGLPoint3`, generalized from a single disjunction to a
finset of disjuncts: if every member of `Q` implies `C`, so does `⋁Q`. -/
lemma imp_fdisj_elim'
    (h : ∀ B ∈ Q, (B 🡒 C) ∈ LogicGLPoint3) : ((⋁ Q) 🡒 C) ∈ LogicGLPoint3 := by
  induction Q using Finset.induction with
  | empty => exact of_GL (by simp only [FormulaFinset.disj_empty]; exact ProvableHilbert.efq)
  | insert a s ha ih =>
    have h1 : (a 🡒 C) ∈ LogicGLPoint3 := h a (Finset.mem_insert_self _ _)
    have h2 : ((⋁ s) 🡒 C) ∈ LogicGLPoint3 :=
      ih (fun B hB => h B (Finset.mem_insert_of_mem hB))
    have hins : (⋁ (insert a s) 🡒 (a ⋎ ⋁ s)) ∈ LogicGLPoint3 :=
      of_GL ProvableHilbert.imp_fdisj_insert
    exact impTrans hins (orElim_imp' h1 h2)

end

lemma imp_and_congr_right' (h : (B 🡒 C) ∈ LogicGLPoint3) :
    ((A ⋏ B) 🡒 (A ⋏ C)) ∈ LogicGLPoint3 :=
  imp_and_intro' (of_GL ProvableHilbert.andL) (impTrans (of_GL ProvableHilbert.andR) h)

section
variable [DecidableEq α]

/-- Distributing a fixed conjunct `A` over a finset disjunction: if `(A ⋏ B) 🡒 C` holds in
`LogicGLPoint3` for every `B ∈ Q`, so does `(A ⋏ ⋁Q) 🡒 C`. -/
lemma imp_and_fdisj_elim'
    (h : ∀ B ∈ Q, ((A ⋏ B) 🡒 C) ∈ LogicGLPoint3) : ((A ⋏ (⋁ Q)) 🡒 C) ∈ LogicGLPoint3 := by
  induction Q using Finset.induction with
  | empty =>
    apply of_GL;
    simp only [FormulaFinset.disj_empty];
    exact ProvableHilbert.impTrans ProvableHilbert.andR ProvableHilbert.efq;
  | insert a s ha ih =>
    have h1 : ((A ⋏ a) 🡒 C) ∈ LogicGLPoint3 := h a (Finset.mem_insert_self _ _)
    have h2 : ((A ⋏ (⋁ s)) 🡒 C) ∈ LogicGLPoint3 :=
      ih (fun B hB => h B (Finset.mem_insert_of_mem hB))
    have hins : ((A ⋏ (⋁ (insert a s))) 🡒 ((A ⋏ a) ⋎ (A ⋏ (⋁ s)))) ∈ LogicGLPoint3 :=
      of_GL (ProvableHilbert.impTrans (ProvableHilbert.and_congr_right ProvableHilbert.imp_fdisj_insert)
        LogicGL.distrib_and_or)
    exact impTrans hins (orElim_imp' h1 h2)

end

end combinators3

section
variable [DecidableEq α]
variable {Δ S : FormulaFinset α}

/-- Raw `⊢ʰ[GL]`-level version of `mem_imp_witnessDisj`: `S ⊆ Δ` nonempty puts
`◇θ(S, Δ \ S)` among the disjuncts of `witnessDisj Δ`, at the plain `GL` level. -/
lemma dia_theta_imp_witnessDisj (hS : S ⊆ Δ) (hSne : S.Nonempty) :
    ⊢ʰ[GL] (◇ (theta S (Δ \ S))) 🡒 witnessDisj Δ :=
  ProvableHilbert.imp_mem_fdisj (Finset.mem_image_of_mem _
    (Finset.mem_erase.mpr ⟨hSne.ne_empty, Finset.mem_powerset.mpr hS⟩))

/-- `S ⊆ Δ` nonempty puts `◇θ(S, Δ \ S)` among the disjuncts of `witnessDisj Δ`. -/
lemma mem_imp_witnessDisj (hS : S ⊆ Δ) (hSne : S.Nonempty) :
    ((◇ (theta S (Δ \ S))) 🡒 witnessDisj Δ) ∈ LogicGLPoint3 :=
  of_GL (dia_theta_imp_witnessDisj hS hSne)

/-- The deep/linearity branch of the Step K induction: from `∼□D` and the terminal content
`(θ(S', Δ' \ S') ⋏ □D) ⋏ D`, derive `◇θ({D}, Δ')`. Hilbert counterpart of the `hzw'` case of
`Model.exists_linear_witness`. -/
lemma witness_deep_step {Δ' S' : FormulaFinset α} {D : Formula α} :
    ((∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ D)) 🡒 ◇ (theta {D} Δ')) ∈ LogicGLPoint3 := by
  set θ' := theta S' (Δ' \ S') with hθ'def;
  set A : Formula α := ∼D ⋏ □D with hAdef;
  set B : Formula α := θ' ⋏ ⊡D with hBdef;
  -- `∼□D` derives `◇A`, and the branch content derives `◇B`.
  have hA : ⊢ʰ[GL] (∼□D : Formula α) 🡒 ◇A :=
    ProvableHilbert.impTrans LogicGL.dia_boxRefuter
      (LogicGL.diaImp LogicGL.conj_comm);
  have hreorder : ⊢ʰ[GL] ((θ' ⋏ □D) ⋏ D) 🡒 B := by
    apply ProvableHilbert.ctxAndIntroRule;
    · exact ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andL;
    · exact ProvableHilbert.ctxAndIntroRule ProvableHilbert.andR
        (ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andR);
  have hB : ⊢ʰ[GL] (◇ ((θ' ⋏ □D) ⋏ D)) 🡒 ◇B := LogicGL.diaImp hreorder;
  have hAandB : ⊢ʰ[GL] (∼□D ⋏ ◇ ((θ' ⋏ □D) ⋏ D)) 🡒 (◇A ⋏ ◇B) :=
    ProvableHilbert.ctxAndIntroRule
      (ProvableHilbert.impTrans ProvableHilbert.andL hA)
      (ProvableHilbert.impTrans ProvableHilbert.andR hB);
  -- The `.3` dichotomy, instantiated at `A, B`.
  have hdich :
      ((◇A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A))) ∈ LogicGLPoint3 :=
    mdp' (LogicGL.weakPoint3_dichotomy (A := A) (B := B))
      (provable_axiomWeakPoint3 (A := ∼A) (B := ∼B));
  have hmain :
      ((∼□D ⋏ ◇ ((θ' ⋏ □D) ⋏ D)) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A))) ∈
        LogicGLPoint3 :=
    impTrans (of_GL hAandB) hdich;
  -- The first two disjuncts are refuted by the shape of `A` and `B`.
  have hAB_bot : ⊢ʰ[GL] (A ⋏ B) 🡒 (⊥ : Formula α) := by
    have hnD : ⊢ʰ[GL] (A ⋏ B) 🡒 (D 🡒 (⊥ : Formula α)) :=
      ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andL;
    have hD' : ⊢ʰ[GL] (A ⋏ B) 🡒 D :=
      ProvableHilbert.impTrans ProvableHilbert.andR
        (ProvableHilbert.impTrans ProvableHilbert.andR ProvableHilbert.andL);
    exact ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.implyS hnD) hD';
  have hBdiaA_bot : ⊢ʰ[GL] (B ⋏ ◇A) 🡒 (⊥ : Formula α) := by
    have hboxD : ⊢ʰ[GL] (B ⋏ ◇A) 🡒 □D :=
      ProvableHilbert.impTrans ProvableHilbert.andL
        (ProvableHilbert.impTrans ProvableHilbert.andR ProvableHilbert.andR);
    have hdianD : ⊢ʰ[GL] (B ⋏ ◇A) 🡒 ◇(∼D) :=
      ProvableHilbert.impTrans ProvableHilbert.andR (LogicGL.diaImp ProvableHilbert.andL);
    have hdiaDD : ⊢ʰ[GL] (B ⋏ ◇A) 🡒 ◇(D ⋏ ∼D) :=
      ProvableHilbert.impTrans (ProvableHilbert.ctxAndIntroRule hboxD hdianD)
        LogicGL.imp_dia_and;
    have hDD_bot : ⊢ʰ[GL] (D ⋏ ∼D) 🡒 (⊥ : Formula α) :=
      ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.implyS ProvableHilbert.andR)
        ProvableHilbert.andL;
    exact ProvableHilbert.impTrans hdiaDD
      (ProvableHilbert.impTrans (LogicGL.diaImp hDD_bot) LogicGL.dia_bot);
  -- The surviving disjunct assembles `theta {D} Δ'`.
  have hSpart : ∀ E ∈ S', ⊢ʰ[GL] ◇B 🡒 ∼□E := by
    intro E hE;
    have hBE : ⊢ʰ[GL] B 🡒 ∼E :=
      ProvableHilbert.impTrans ProvableHilbert.andL
        (ProvableHilbert.impTrans ProvableHilbert.andL
          (ProvableHilbert.impTrans (ProvableHilbert.imp_fconj_of_mem (Finset.mem_image_of_mem _ hE))
            ProvableHilbert.andL));
    exact ProvableHilbert.impTrans (LogicGL.diaImp hBE) ProvableHilbert.dia_neg_imp_not_box;
  have hTpart : ∀ E ∈ Δ' \ S', ⊢ʰ[GL] ◇B 🡒 ∼□E := by
    intro E hE;
    have hBE : ⊢ʰ[GL] B 🡒 ∼□E :=
      ProvableHilbert.impTrans ProvableHilbert.andL
        (ProvableHilbert.impTrans ProvableHilbert.andR
          (ProvableHilbert.imp_fconj_of_mem (Finset.mem_image_of_mem _ hE)));
    exact ProvableHilbert.impTrans (LogicGL.diaImp hBE)
      ProvableHilbert.dia_of_not_box_imp_not_box;
  have hall : ∀ E ∈ Δ', ⊢ʰ[GL] ◇B 🡒 ∼□E := by
    intro E hE;
    by_cases h : E ∈ S';
    · exact hSpart E h;
    · exact hTpart E (Finset.mem_sdiff.mpr ⟨hE, h⟩);
  have hconjΔ' : ⊢ʰ[GL] ◇B 🡒 ⋀ (Δ'.image (fun E => ∼□E)) := by
    apply ProvableHilbert.imp_fconj_of_forall;
    intro C hC;
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hC;
    exact hall E hE;
  have hfinal : ⊢ʰ[GL] (A ⋏ ◇B) 🡒 theta {D} Δ' := by
    unfold theta;
    simp only [Finset.image_singleton, FormulaFinset.conj_singleton];
    exact ProvableHilbert.ctxAndIntroRule ProvableHilbert.andL
      (ProvableHilbert.impTrans ProvableHilbert.andR hconjΔ');
  have hcases :
      ⊢ʰ[GL] ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) 🡒 ◇ (theta {D} Δ') := by
    apply ProvableHilbert.orElim';
    · apply ProvableHilbert.orElim';
      · exact ProvableHilbert.impTrans (ProvableHilbert.impTrans (LogicGL.diaImp hAB_bot)
          LogicGL.dia_bot) ProvableHilbert.efq;
      · exact LogicGL.diaImp hfinal;
    · exact ProvableHilbert.impTrans (ProvableHilbert.impTrans (LogicGL.diaImp hBdiaA_bot)
        LogicGL.dia_bot) ProvableHilbert.efq;
  exact impTrans hmain (of_GL hcases);

/-- **(W)**, the Hilbert-level witness lemma: for nonempty `Δ`, `LogicGLPoint3` proves
`(⋀_{A∈Δ} ∼□A) 🡒 ⋁_{∅≠S⊆Δ} ◇θ_S`. -/
theorem witness : ∀ {Δ : FormulaFinset α}, Δ.Nonempty →
    ((⋀ (Δ.image (fun A => ∼□A))) 🡒 witnessDisj Δ) ∈ LogicGLPoint3 := by
  intro Δ;
  induction Δ using Finset.strongInductionOn with
  | _ Δ ih =>
  intro hΔ;
  obtain ⟨D, hD⟩ := hΔ;
  by_cases hΔ' : (Δ.erase D).Nonempty;
  · -- Inductive step: `Δ = insert D Δ'`, `Δ' := Δ.erase D` nonempty.
    set Δ' := Δ.erase D with hΔ'def;
    have hDnotΔ' : D ∉ Δ' := Finset.notMem_erase D Δ;
    have hΔins : insert D Δ' = Δ := Finset.insert_erase hD;
    have IH := ih Δ' (Finset.erase_ssubset hD) hΔ';
    -- Split the antecedent: `⋀Δ.image∼□· 🡒 (∼□D ⋏ ⋀Δ'.image∼□·)`.
    have himp1 : (⋀ (Δ.image (fun A => ∼□A)) 🡒 ∼□D) ∈ LogicGLPoint3 :=
      of_GL (ProvableHilbert.imp_fconj_of_mem (Finset.mem_image_of_mem _ hD));
    have himp2 : (⋀ (Δ.image (fun A => ∼□A)) 🡒 ⋀ (Δ'.image (fun A => ∼□A))) ∈ LogicGLPoint3 :=
      of_GL (ProvableHilbert.imp_fconj_fconj_of_subset
        (Finset.image_subset_image (hΔ'def ▸ Finset.erase_subset D Δ)));
    have hstep1 :
        (⋀ (Δ.image (fun A => ∼□A)) 🡒 (∼□D ⋏ ⋀ (Δ'.image (fun A => ∼□A)))) ∈ LogicGLPoint3 :=
      imp_and_intro' himp1 himp2;
    have hstep2 :
        ((∼□D ⋏ ⋀ (Δ'.image (fun A => ∼□A))) 🡒 (∼□D ⋏ witnessDisj Δ')) ∈ LogicGLPoint3 :=
      imp_and_congr_right' IH;
    -- Dispose of every witness `◇θ(S', Δ' \ S')` of `witnessDisj Δ'` via the three-way
    -- diamond case split on `□D`/`D` (`Model.exists_linear_witness`'s `hD1`/`hD2`/`hzw'`).
    have hstep3 : ((∼□D ⋏ witnessDisj Δ') 🡒 witnessDisj Δ) ∈ LogicGLPoint3 := by
      apply imp_and_fdisj_elim';
      intro B hB;
      obtain ⟨S', hS'mem, rfl⟩ := Finset.mem_image.mp hB;
      obtain ⟨hS'ne, hS'sub'⟩ := Finset.mem_erase.mp hS'mem;
      rw [Finset.mem_powerset] at hS'sub';
      have hS'ne' : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS'ne;
      have hS'sub : S' ⊆ Δ := hΔins ▸ (hS'sub'.trans (Finset.subset_insert D Δ'));
      have hDnotS' : D ∉ S' := fun h => hDnotΔ' (hS'sub' h);
      -- The three-way `⊢ʰ[GL]`-level split of `◇θ(S', Δ' \ S')`.
      have hsplit :
          ⊢ʰ[GL] ◇ (theta S' (Δ' \ S')) 🡒
            ((◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ D) ⋎ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ ∼D)) ⋎
              ◇ (theta S' (Δ' \ S') ⋏ ∼□D)) :=
        ProvableHilbert.impTrans (LogicGL.dia_cases (A := theta S' (Δ' \ S')) (B := □D))
          (LogicGL.or_imp_left
            (LogicGL.dia_cases (A := theta S' (Δ' \ S') ⋏ □D) (B := D)));
      -- Deep branch: needs the `.3` axiom, via `witness_deep_step`.
      have hDeep :
          ((∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ D)) 🡒 witnessDisj Δ) ∈ LogicGLPoint3 := by
        refine impTrans (witness_deep_step (S' := S') (Δ' := Δ') (D := D)) ?_;
        have heqD : Δ \ ({D} : FormulaFinset α) = Δ' := by
          rw [← hΔins, Finset.sdiff_singleton_eq_erase, Finset.erase_insert hDnotΔ'];
        rw [← heqD];
        exact mem_imp_witnessDisj
          (hΔins ▸ Finset.singleton_subset_iff.mpr (Finset.mem_insert_self D Δ'))
          ⟨D, Finset.mem_singleton_self _⟩;
      -- Join-`S'` branch: pure GL, `D` joins the terminally-refuted side.
      have hJoinS :
          ((∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ ∼D)) 🡒 witnessDisj Δ) ∈ LogicGLPoint3 := by
        apply of_GL;
        refine ProvableHilbert.impTrans ProvableHilbert.andR ?_;
        have hreorder :
            ⊢ʰ[GL] ((theta S' (Δ' \ S') ⋏ □D) ⋏ ∼D) 🡒 (theta S' (Δ' \ S') ⋏ (∼D ⋏ □D)) :=
          ProvableHilbert.ctxAndIntroRule
            (ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andL)
            (ProvableHilbert.ctxAndIntroRule ProvableHilbert.andR
              (ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andR));
        refine ProvableHilbert.impTrans
          (LogicGL.diaImp (ProvableHilbert.impTrans hreorder ProvableHilbert.theta_join_S)) ?_;
        have heqS : Δ \ (insert D S') = Δ' \ S' := by
          rw [← hΔins, Finset.insert_sdiff_insert, Finset.sdiff_insert,
            Finset.erase_eq_of_notMem (fun h => hDnotΔ' (Finset.mem_sdiff.mp h).1)];
        rw [← heqS];
        exact dia_theta_imp_witnessDisj (Finset.insert_subset hD hS'sub)
          ⟨D, Finset.mem_insert_self _ _⟩;
      -- Complement branch: pure GL, `D`'s refutation is postponed further.
      have hComplement :
          ((∼□D ⋏ ◇ (theta S' (Δ' \ S') ⋏ ∼□D)) 🡒 witnessDisj Δ) ∈ LogicGLPoint3 := by
        apply of_GL;
        refine ProvableHilbert.impTrans ProvableHilbert.andR ?_;
        refine ProvableHilbert.impTrans
          (LogicGL.diaImp ProvableHilbert.theta_join_complement) ?_;
        have heqC : Δ \ S' = insert D (Δ' \ S') := by
          rw [← hΔins, Finset.insert_sdiff_of_notMem _ hDnotS'];
        rw [← heqC];
        exact dia_theta_imp_witnessDisj hS'sub hS'ne';
      have hsplit2 :
          ⊢ʰ[GL] (∼□D ⋏ ◇ (theta S' (Δ' \ S'))) 🡒
            (((∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ D)) ⋎
                (∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ ∼D))) ⋎
              (∼□D ⋏ ◇ (theta S' (Δ' \ S') ⋏ ∼□D))) :=
        ProvableHilbert.impTrans (ProvableHilbert.and_congr_right hsplit)
          (ProvableHilbert.impTrans LogicGL.distrib_and_or
            (LogicGL.or_imp_left LogicGL.distrib_and_or));
      exact impTrans (of_GL hsplit2) (orElim_imp' (orElim_imp' hDeep hJoinS) hComplement);
    exact impTrans hstep1 (impTrans hstep2 hstep3);
  · -- Base case: `Δ = {D}`.
    have hΔeq : Δ = {D} := by
      rw [Finset.not_nonempty_iff_eq_empty] at hΔ';
      ext A;
      simp only [Finset.mem_singleton];
      constructor;
      · intro hA;
        by_contra hAD;
        exact absurd (Finset.mem_erase.mpr ⟨hAD, hA⟩) (hΔ' ▸ Finset.notMem_empty A);
      · rintro rfl; exact hD;
    subst hΔeq;
    have hL : ({D} : FormulaFinset α).image (fun A => ∼□A) = {∼□D} := by simp;
    rw [hL, FormulaFinset.conj_singleton];
    have hstep : ((◇ (theta {D} (({D} : FormulaFinset α) \ {D}))) 🡒 witnessDisj {D}) ∈
        LogicGLPoint3 :=
      mem_imp_witnessDisj subset_rfl ⟨D, Finset.mem_singleton_self _⟩;
    rw [show (({D} : FormulaFinset α) \ {D}) = ∅ by simp] at hstep;
    apply impTrans _ hstep;
    apply of_GL;
    have hcore : ⊢ʰ[GL] ((□D ⋏ ∼D) 🡒 theta {D} (∅ : FormulaFinset α)) := by
      simp only [theta, Finset.image_singleton, FormulaFinset.conj_singleton,
        Finset.image_empty, FormulaFinset.conj_empty];
      apply LogicGL.iff_forces.mpr;
      grind;
    exact ProvableHilbert.impTrans LogicGL.dia_boxRefuter (LogicGL.diaImp hcore);

end

end LogicGLPoint3

/-!
# Step L: Hilbert soundness of the `boxGLPoint3` Gentzen rule

This is the Hilbert-calculus counterpart of `Model.validate_gentzen_boxGLPoint3`
(`ProvabilityLogic/Gentzen/GLPoint3/Kripke.lean`): from the Step K witness lemma
(`LogicGLPoint3.witness`) and the family of Hilbert-level premises for `boxGLPoint3`,
derive the rule's conclusion inside `LogicGLPoint3`.
-/

namespace LogicGL.ProvableHilbert

universe u
variable {α : Type u}

section boxUnionToolbox
variable [DecidableEq α]

/-- `⋀Γ.box` derives `⋀Γ.box.box` (each `□B ∈ Γ.box` derives `□□B` via axiom `4`). -/
lemma imp_fconj_box_box {Γ : FormulaFinset α} : ⊢ʰ[GL] ⋀Γ.box 🡒 ⋀Γ.box.box := by
  apply imp_fconj_of_forall;
  intro C hC;
  obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hC;
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB';
  exact impTrans (imp_fconj_of_mem (Finset.mem_image_of_mem _ hB)) modal4;

/-- `⋀Γ.box` derives `□⋀Γ.box` (i.e. `Γ.box` is itself "closed under `□`" up to `⊢ʰ[GL]`). -/
lemma imp_box_conj_box {Γ : FormulaFinset α} : ⊢ʰ[GL] ⋀Γ.box 🡒 □⋀Γ.box :=
  impTrans imp_fconj_box_box imp_conj_box

/-- **(box-union)** `⋀Γ.box` derives `□(⋀(Γ.box ∪ Γ))`: the Hilbert-level counterpart of
axiom `4`'s semantic content used in `Model.validate_gentzen_boxGLPoint3`. -/
lemma imp_box_union {Γ : FormulaFinset α} : ⊢ʰ[GL] ⋀Γ.box 🡒 □(⋀(Γ.box ∪ Γ)) :=
  impTrans (impTrans (ctxAndIntroRule imp_box_conj_box imp_conj_box) imp_box_and)
    (boxImp (imp_fconj_union Γ.box Γ))

end boxUnionToolbox

section notDisjToolbox

variable {Q : FormulaFinset α}

/-- From `B 🡒 ∼A` for every `A ∈ Q`, derive `B 🡒 ∼⋁Q`. -/
lemma imp_not_fdisj_of_forall {B : Formula α}
    (h : ∀ A ∈ Q, ⊢ʰ[GL] B 🡒 ∼A) : ⊢ʰ[GL] B 🡒 ∼(⋁ Q) :=
  impTrans dni (LogicGL.contra (imp_fdisj_elim (fun A hA => impTrans dni (LogicGL.contra (h A hA)))))

section
variable [DecidableEq α]

/-- De Morgan for finset disjunctions: `∼⋁Q` derives `⋀(Q.image (fun A => ∼A))`. -/
lemma imp_not_fdisj_fconj_not :
    ⊢ʰ[GL] ∼(⋁ Q) 🡒 ⋀ (Q.image (fun A => ∼A)) := by
  apply imp_fconj_of_forall;
  intro C hC;
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC;
  exact LogicGL.contra (imp_mem_fdisj hA);

end

end notDisjToolbox

end LogicGL.ProvableHilbert

namespace LogicGLPoint3

universe u
variable {α : Type u}

public section combinators2

variable {A B : Formula α}

lemma contra' (h : (A 🡒 B) ∈ LogicGLPoint3) : (∼B 🡒 ∼A) ∈ LogicGLPoint3 :=
  mdp' (ProvableHilbert.elimContra (A := ∼A) (B := ∼B))
    (impTrans (of_GL ProvableHilbert.dne) (impTrans h (of_GL ProvableHilbert.dni)))

lemma diaImp' (h : (A 🡒 B) ∈ LogicGLPoint3) : (◇A 🡒 ◇B) ∈ LogicGLPoint3 :=
  contra' (box' (contra' h))

/-- From `(A 🡒 B) ∈ L` derive `((A ⋏ ∼B) 🡒 ⊥) ∈ L`: the propositional core used to
turn a `boxGLPoint3` premise `h S` into a contradiction against `∼B`. -/
lemma imp_and_not_bot' (h : (A 🡒 B) ∈ LogicGLPoint3) :
    ((A ⋏ ∼B) 🡒 (⊥ : Formula α)) ∈ LogicGLPoint3 := by
  have hB : ((A ⋏ ∼B) 🡒 B) ∈ LogicGLPoint3 := impTrans (of_GL ProvableHilbert.andL) h;
  have hnB : ((A ⋏ ∼B) 🡒 ∼B) ∈ LogicGLPoint3 := of_GL ProvableHilbert.andR;
  have hand : ((A ⋏ ∼B) 🡒 (B ⋏ ∼B)) ∈ LogicGLPoint3 := imp_and_intro' hB hnB;
  have hbot : ⊢ʰ[GL] (B ⋏ ∼B) 🡒 (⊥ : Formula α) :=
    ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.implyS ProvableHilbert.andR) ProvableHilbert.andL;
  exact impTrans hand (of_GL hbot)

end combinators2

end LogicGLPoint3

namespace LogicGL.ProvableHilbert

universe u
variable {α : Type u} [DecidableEq α]

section thetaToolbox

variable {S T : FormulaFinset α}

/-- `theta S T` derives `⋀S.box` (the "terminally refuted" side always yields `□A`). -/
lemma imp_theta_box :
    ⊢ʰ[GL] (LogicGLPoint3.theta S T) 🡒 ⋀ S.box := by
  unfold LogicGLPoint3.theta;
  refine impTrans andL ?_;
  apply imp_fconj_of_forall;
  intro C hC;
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC;
  exact impTrans (imp_fconj_of_mem (Finset.mem_image_of_mem _ hA)) andR;

/-- `theta S T` derives `∼⋁(S ∪ T.box)`: every disjunct of `S ∪ T.box` is refuted by
`theta S T` (`S`'s members via `∼A`, `T.box`'s members via `∼□A`). -/
lemma imp_theta_not_fdisj :
    ⊢ʰ[GL] (LogicGLPoint3.theta S T) 🡒 ∼(⋁ (S ∪ T.box)) := by
  apply imp_not_fdisj_of_forall;
  intro A hA;
  unfold LogicGLPoint3.theta;
  rcases Finset.mem_union.mp hA with hAS | hATbox;
  · exact impTrans andL (impTrans (imp_fconj_of_mem (Finset.mem_image_of_mem _ hAS)) andL);
  · obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hATbox;
    exact impTrans andR (imp_fconj_of_mem (Finset.mem_image_of_mem _ hA'));

end thetaToolbox

end LogicGL.ProvableHilbert

namespace LogicGLPoint3

universe u
variable {α : Type u} [DecidableEq α]
variable {Γ Δ : FormulaFinset α}

/-- The per-`S` step of the `boxGLPoint3` soundness proof: from the premise `h S` for a
fixed nonempty `S ⊆ Δ`, derive that `⋀Γ.box ⋏ ◇θ(S, Δ \ S)` is contradictory. Hilbert
counterpart of the contradiction assembled at the witness world in
`Model.validate_gentzen_boxGLPoint3`. -/
private lemma boxGLPoint3_step {S : FormulaFinset α}
    (h : ∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty →
      ((⋀(Γ.box ∪ Γ ∪ S.box)) 🡒 (⋁(S ∪ (Δ \ S).box))) ∈ LogicGLPoint3)
    (hSsub : S ⊆ Δ) (hSne : S.Nonempty) :
    ((⋀Γ.box ⋏ ◇ (theta S (Δ \ S))) 🡒 (⊥ : Formula α)) ∈ LogicGLPoint3 := by
  set T := Δ \ S with hTdef;
  -- The premise `h S`, turned into a contradiction against its own negated consequent.
  have hbotProp : ((⋀(Γ.box ∪ Γ ∪ S.box)) ⋏ ∼(⋁ (S ∪ T.box))) 🡒 (⊥ : Formula α) ∈ LogicGLPoint3 :=
    imp_and_not_bot' (h S hSsub hSne)
  -- `theta S T` supplies exactly the antecedent's `S.box` part and the consequent's negation.
  have hglue : ⊢ʰ[GL] (⋀(Γ.box ∪ Γ) ⋏ theta S T) 🡒
      ((⋀(Γ.box ∪ Γ ∪ S.box)) ⋏ ∼(⋁ (S ∪ T.box))) := by
    apply ProvableHilbert.ctxAndIntroRule;
    · have h1 : ⊢ʰ[GL] (⋀(Γ.box ∪ Γ) ⋏ theta S T) 🡒 (⋀(Γ.box ∪ Γ) ⋏ ⋀ S.box) :=
        ProvableHilbert.ctxAndIntroRule ProvableHilbert.andL
          (ProvableHilbert.impTrans ProvableHilbert.andR ProvableHilbert.imp_theta_box);
      exact ProvableHilbert.impTrans h1 (ProvableHilbert.imp_fconj_union (Γ.box ∪ Γ) S.box);
    · exact ProvableHilbert.impTrans ProvableHilbert.andR ProvableHilbert.imp_theta_not_fdisj;
  have hpropbot : ((⋀(Γ.box ∪ Γ) ⋏ theta S T) 🡒 (⊥ : Formula α)) ∈ LogicGLPoint3 :=
    impTrans (of_GL hglue) hbotProp
  -- Push the contradiction inside the `◇`, using `dia_bot`.
  have hdiabot : ((◇ (⋀(Γ.box ∪ Γ) ⋏ theta S T)) 🡒 (⊥ : Formula α)) ∈ LogicGLPoint3 :=
    impTrans (diaImp' hpropbot) (of_GL LogicGL.dia_bot)
  -- Transport `□(⋀(Γ.box ∪ Γ))` (from `⋀Γ.box`) into the `◇θ(S, T)` witness.
  have hcombine : ⊢ʰ[GL] (⋀Γ.box ⋏ ◇ (theta S T)) 🡒 ◇ (⋀(Γ.box ∪ Γ) ⋏ theta S T) :=
    ProvableHilbert.impTrans
      (ProvableHilbert.ctxAndIntroRule
        (ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.imp_box_union)
        ProvableHilbert.andR)
      LogicGL.imp_dia_and
  exact impTrans (of_GL hcombine) hdiabot

/-- **Step L**, the Hilbert soundness of the `boxGLPoint3` rule: from the Step K witness
lemma and a family of `LogicGLPoint3`-membership premises indexed by the nonempty subsets
`S ⊆ Δ`, derive the rule's conclusion. This is the Hilbert-calculus counterpart of
`Model.validate_gentzen_boxGLPoint3`. -/
theorem boxGLPoint3 (hΔ : Δ.Nonempty)
    (h : ∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty →
      ((⋀(Γ.box ∪ Γ ∪ S.box)) 🡒 (⋁(S ∪ (Δ \ S).box))) ∈ LogicGLPoint3) :
    ((⋀Γ.box) 🡒 (⋁Δ.box)) ∈ LogicGLPoint3 := by
  -- Assemble the per-`S` contradictions into a single contradiction against `witnessDisj Δ`.
  have hall : ((⋀Γ.box) ⋏ witnessDisj Δ) 🡒 (⊥ : Formula α) ∈ LogicGLPoint3 := by
    unfold witnessDisj;
    apply imp_and_fdisj_elim';
    intro B hB;
    obtain ⟨S, hSmem, rfl⟩ := Finset.mem_image.mp hB;
    obtain ⟨hSne, hSsub'⟩ := Finset.mem_erase.mp hSmem;
    rw [Finset.mem_powerset] at hSsub';
    exact boxGLPoint3_step h hSsub' (Finset.nonempty_iff_ne_empty.mpr hSne);
  -- Feed in the Step K witness lemma to reduce `witnessDisj Δ` to `⋀(Δ.image ∼□·)`.
  have hantecedent : ((⋀Γ.box) ⋏ ⋀ (Δ.image (fun A => ∼□A))) 🡒 (⊥ : Formula α) ∈ LogicGLPoint3 :=
    impTrans (imp_and_congr_right' (witness hΔ)) hall
  -- De Morgan: `∼⋁Δ.box` derives `⋀(Δ.image ∼□·)`.
  have himg : (Δ.box).image (fun A => ∼A) = Δ.image (fun A => ∼□A) := by
    simp only [FormulaFinset.box, Finset.image_image, Function.comp_def];
  have hdemorgan : ⊢ʰ[GL] ∼(⋁ Δ.box) 🡒 ⋀ (Δ.image (fun A => ∼□A)) := by
    have h0 := ProvableHilbert.imp_not_fdisj_fconj_not (Q := Δ.box);
    rwa [himg] at h0;
  have hstep : ((⋀Γ.box) ⋏ ∼(⋁ Δ.box)) 🡒 (⊥ : Formula α) ∈ LogicGLPoint3 :=
    impTrans (imp_and_congr_right' (of_GL hdemorgan)) hantecedent
  -- The classical propositional wrap-up: `∼(A ⋏ ∼B) 🡒 (A 🡒 B)`.
  exact mdp' LogicGL.imp_of_not_and_not hstep

end LogicGLPoint3

end
