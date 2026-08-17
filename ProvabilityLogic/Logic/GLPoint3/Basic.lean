module

public import ProvabilityLogic.Gentzen.GLPoint3.Kripke
public import ProvabilityLogic.Kripke.Reindex
public import ProvabilityLogic.Logic.GL.Theorems
public import ProvabilityLogic.Logic.SumNormal
public import ProvabilityLogic.Kripke.Linearity

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

lemma of_GL (h : A ∈ LogicGL) : A ∈ LogicGLPoint3 := provable_of_provable_GL h

lemma mdp' (h : (A 🡒 B) ∈ LogicGL) (hA : A ∈ LogicGLPoint3) : B ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (of_GL h) hA

lemma impTrans
  (hAB : (A 🡒 B) ∈ LogicGLPoint3) (hBC : (B 🡒 C) ∈ LogicGLPoint3) :
  (A 🡒 C) ∈ LogicGLPoint3 :=
  Logic.sumNormal.mdp (mdp' LogicGL.imp_trans hAB) hBC

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
## The Hilbert-level witness lemma for `GL.3`

This is the Hilbert-calculus counterpart of `Model.exists_linear_witness`
(`ProvabilityLogic/Gentzen/GLPoint3/Kripke.lean`). For a nonempty finite `Δ`, `LogicGLPoint3` proves

`(⋀_{A∈Δ} ∼□A) 🡒 ⋁_{∅≠S⊆Δ} ◇θ_S`,

where `θ_S := ⋀_{A∈S}(∼A ⋏ □A) ⋏ ⋀_{A∈Δ\S} ∼□A`.
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

namespace LogicGL

open ProvableHilbert

public section thetaCombinators

variable {α : Type u} [DecidableEq α] {S T : FormulaFinset α} {D : Formula α}

lemma theta_join_complement :
  ((LogicGLPoint3.theta S T ⋏ ∼□D) 🡒 LogicGLPoint3.theta S (insert D T)) ∈ LogicGL := by
  unfold LogicGLPoint3.theta;
  rw [Finset.image_insert];
  exact ctxAndIntroRule (impTrans andL andL)
    (impTrans (ctxAndIntroRule andR (impTrans andL andR)) imp_fconj_insert);

lemma theta_join_S :
  ((LogicGLPoint3.theta S T ⋏ (∼D ⋏ □D)) 🡒 LogicGLPoint3.theta (insert D S) T) ∈ LogicGL := by
  unfold LogicGLPoint3.theta;
  rw [Finset.image_insert];
  exact ctxAndIntroRule
    (impTrans (ctxAndIntroRule andR (impTrans andL andL)) imp_fconj_insert)
    (impTrans andL andR);

end thetaCombinators

end LogicGL

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
      of_GL (ProvableHilbert.impTrans (LogicGL.and_congr_right ProvableHilbert.imp_fdisj_insert)
        LogicGL.distrib_and_or)
    exact impTrans hins (orElim_imp' h1 h2)

end

end combinators3

section
variable [DecidableEq α]
variable {Δ S : FormulaFinset α}

lemma dia_theta_imp_witnessDisj (hS : S ⊆ Δ) (hSne : S.Nonempty) :
  ((◇ (theta S (Δ \ S))) 🡒 witnessDisj Δ) ∈ LogicGL :=
  ProvableHilbert.imp_mem_fdisj (Finset.mem_image_of_mem _
    (Finset.mem_erase.mpr ⟨hSne.ne_empty, Finset.mem_powerset.mpr hS⟩))

/-- `S ⊆ Δ` nonempty puts `◇θ(S, Δ \ S)` among the disjuncts of `witnessDisj Δ`. -/
lemma mem_imp_witnessDisj (hS : S ⊆ Δ) (hSne : S.Nonempty) :
  ((◇ (theta S (Δ \ S))) 🡒 witnessDisj Δ) ∈ LogicGLPoint3 :=
  of_GL (dia_theta_imp_witnessDisj hS hSne)

/-- The deep/linearity branch of the `witness` induction, the Hilbert counterpart of the
`hzw'` case of `Model.exists_linear_witness`. -/
lemma witness_deep_step {Δ' S' : FormulaFinset α} {D : Formula α} :
  ((∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ D)) 🡒 ◇ (theta {D} Δ')) ∈ LogicGLPoint3 := by
  set θ' := theta S' (Δ' \ S') with hθ'def;
  set A : Formula α := ∼D ⋏ □D with hAdef;
  set B : Formula α := θ' ⋏ ⊡D with hBdef;
  have hA : ((∼□D) 🡒 ◇A) ∈ LogicGL :=
    ProvableHilbert.impTrans LogicGL.dia_boxRefuter
      (LogicGL.diaImp LogicGL.conj_comm);
  have hreorder : (((θ' ⋏ □D) ⋏ D) 🡒 B) ∈ LogicGL := by
    apply ProvableHilbert.ctxAndIntroRule;
    · exact ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andL;
    · exact ProvableHilbert.ctxAndIntroRule ProvableHilbert.andR
        (ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andR);
  have hB : ((◇ ((θ' ⋏ □D) ⋏ D)) 🡒 ◇B) ∈ LogicGL := LogicGL.diaImp hreorder;
  have hAandB : ((∼□D ⋏ ◇ ((θ' ⋏ □D) ⋏ D)) 🡒 (◇A ⋏ ◇B)) ∈ LogicGL :=
    ProvableHilbert.ctxAndIntroRule
      (ProvableHilbert.impTrans ProvableHilbert.andL hA)
      (ProvableHilbert.impTrans ProvableHilbert.andR hB);
  have hdich :
      ((◇A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A))) ∈ LogicGLPoint3 :=
    mdp' (LogicGL.weakPoint3_dichotomy (A := A) (B := B))
      (provable_axiomWeakPoint3 (A := ∼A) (B := ∼B));
  have hmain :
      ((∼□D ⋏ ◇ ((θ' ⋏ □D) ⋏ D)) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A))) ∈
        LogicGLPoint3 :=
    impTrans (of_GL hAandB) hdich;
  have hAB_bot : ((A ⋏ B) 🡒 (⊥ : Formula α)) ∈ LogicGL := by
    have hnD : ((A ⋏ B) 🡒 (D 🡒 (⊥ : Formula α))) ∈ LogicGL :=
      ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andL;
    have hD' : ((A ⋏ B) 🡒 D) ∈ LogicGL :=
      ProvableHilbert.impTrans ProvableHilbert.andR
        (ProvableHilbert.impTrans ProvableHilbert.andR ProvableHilbert.andL);
    exact ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.implyS hnD) hD';
  have hBdiaA_bot : ((B ⋏ ◇A) 🡒 (⊥ : Formula α)) ∈ LogicGL := by
    have hboxD : ((B ⋏ ◇A) 🡒 □D) ∈ LogicGL :=
      ProvableHilbert.impTrans ProvableHilbert.andL
        (ProvableHilbert.impTrans ProvableHilbert.andR ProvableHilbert.andR);
    have hdianD : ((B ⋏ ◇A) 🡒 ◇(∼D)) ∈ LogicGL :=
      ProvableHilbert.impTrans ProvableHilbert.andR (LogicGL.diaImp ProvableHilbert.andL);
    have hdiaDD : ((B ⋏ ◇A) 🡒 ◇(D ⋏ ∼D)) ∈ LogicGL :=
      ProvableHilbert.impTrans (ProvableHilbert.ctxAndIntroRule hboxD hdianD)
        LogicGL.imp_dia_and;
    have hDD_bot : ((D ⋏ ∼D) 🡒 (⊥ : Formula α)) ∈ LogicGL :=
      ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.implyS ProvableHilbert.andR)
        ProvableHilbert.andL;
    exact ProvableHilbert.impTrans hdiaDD
      (ProvableHilbert.impTrans (LogicGL.diaImp hDD_bot) LogicGL.dia_bot);
  have hSpart : ∀ E ∈ S', (◇B 🡒 ∼□E) ∈ LogicGL := by
    intro E hE;
    have hBE : (B 🡒 ∼E) ∈ LogicGL :=
      ProvableHilbert.impTrans ProvableHilbert.andL
        (ProvableHilbert.impTrans ProvableHilbert.andL
          (ProvableHilbert.impTrans (ProvableHilbert.imp_fconj_of_mem (Finset.mem_image_of_mem _ hE))
            ProvableHilbert.andL));
    exact ProvableHilbert.impTrans (LogicGL.diaImp hBE) LogicGL.dia_neg_imp_not_box;
  have hTpart : ∀ E ∈ Δ' \ S', (◇B 🡒 ∼□E) ∈ LogicGL := by
    intro E hE;
    have hBE : (B 🡒 ∼□E) ∈ LogicGL :=
      ProvableHilbert.impTrans ProvableHilbert.andL
        (ProvableHilbert.impTrans ProvableHilbert.andR
          (ProvableHilbert.imp_fconj_of_mem (Finset.mem_image_of_mem _ hE)));
    exact ProvableHilbert.impTrans (LogicGL.diaImp hBE)
      LogicGL.dia_of_not_box_imp_not_box;
  have hall : ∀ E ∈ Δ', (◇B 🡒 ∼□E) ∈ LogicGL := by
    intro E hE;
    by_cases h : E ∈ S';
    · exact hSpart E h;
    · exact hTpart E (Finset.mem_sdiff.mpr ⟨hE, h⟩);
  have hconjΔ' : (◇B 🡒 ⋀ (Δ'.image (fun E => ∼□E))) ∈ LogicGL := by
    apply ProvableHilbert.imp_fconj_of_forall;
    intro C hC;
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hC;
    exact hall E hE;
  have hfinal : ((A ⋏ ◇B) 🡒 theta {D} Δ') ∈ LogicGL := by
    unfold theta;
    simp only [Finset.image_singleton, FormulaFinset.conj_singleton];
    exact ProvableHilbert.ctxAndIntroRule ProvableHilbert.andL
      (ProvableHilbert.impTrans ProvableHilbert.andR hconjΔ');
  have hcases : (((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)) 🡒 ◇ (theta {D} Δ')) ∈ LogicGL := by
    apply ProvableHilbert.orElim';
    · apply ProvableHilbert.orElim';
      · exact ProvableHilbert.impTrans (ProvableHilbert.impTrans (LogicGL.diaImp hAB_bot)
          LogicGL.dia_bot) ProvableHilbert.efq;
      · exact LogicGL.diaImp hfinal;
    · exact ProvableHilbert.impTrans (ProvableHilbert.impTrans (LogicGL.diaImp hBdiaA_bot)
        LogicGL.dia_bot) ProvableHilbert.efq;
  exact impTrans hmain (of_GL hcases);

/-- The Hilbert-level witness lemma: for nonempty `Δ`, `LogicGLPoint3` proves
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
      have hsplit :
        ((◇ (theta S' (Δ' \ S'))) 🡒
          ((◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ D) ⋎ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ ∼D)) ⋎
            ◇ (theta S' (Δ' \ S') ⋏ ∼□D))) ∈ LogicGL :=
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
          (((theta S' (Δ' \ S') ⋏ □D) ⋏ ∼D) 🡒 (theta S' (Δ' \ S') ⋏ (∼D ⋏ □D))) ∈ LogicGL :=
          ProvableHilbert.ctxAndIntroRule
            (ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andL)
            (ProvableHilbert.ctxAndIntroRule ProvableHilbert.andR
              (ProvableHilbert.impTrans ProvableHilbert.andL ProvableHilbert.andR));
        refine ProvableHilbert.impTrans
          (LogicGL.diaImp (ProvableHilbert.impTrans hreorder LogicGL.theta_join_S)) ?_;
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
          (LogicGL.diaImp LogicGL.theta_join_complement) ?_;
        have heqC : Δ \ S' = insert D (Δ' \ S') := by
          rw [← hΔins, Finset.insert_sdiff_of_notMem _ hDnotS'];
        rw [← heqC];
        exact dia_theta_imp_witnessDisj hS'sub hS'ne';
      have hsplit2 :
        ((∼□D ⋏ ◇ (theta S' (Δ' \ S'))) 🡒
          (((∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ D)) ⋎
              (∼□D ⋏ ◇ ((theta S' (Δ' \ S') ⋏ □D) ⋏ ∼D))) ⋎
            (∼□D ⋏ ◇ (theta S' (Δ' \ S') ⋏ ∼□D)))) ∈ LogicGL :=
        ProvableHilbert.impTrans (LogicGL.and_congr_right hsplit)
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
    have hcore : ((□D ⋏ ∼D) 🡒 theta {D} (∅ : FormulaFinset α)) ∈ LogicGL := by
      simp only [theta, Finset.image_singleton, FormulaFinset.conj_singleton,
        Finset.image_empty, FormulaFinset.conj_empty];
      apply LogicGL.iff_forces.mpr;
      grind;
    exact ProvableHilbert.impTrans LogicGL.dia_boxRefuter (LogicGL.diaImp hcore);

end

end LogicGLPoint3

/-!
## Hilbert soundness of the `boxGLPoint3` Gentzen rule

This is the Hilbert-calculus counterpart of `Model.validate_gentzen_boxGLPoint3`
(`ProvabilityLogic/Gentzen/GLPoint3/Kripke.lean`): from `LogicGLPoint3.witness` and the
family of Hilbert-level premises for `boxGLPoint3`, derive the rule's conclusion inside
`LogicGLPoint3`.
-/

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
  have hbot : ((B ⋏ ∼B) 🡒 (⊥ : Formula α)) ∈ LogicGL :=
    ProvableHilbert.mdp (ProvableHilbert.mdp ProvableHilbert.implyS ProvableHilbert.andR)
      ProvableHilbert.andL;
  exact impTrans hand (of_GL hbot)

end combinators2

end LogicGLPoint3

namespace LogicGL

open ProvableHilbert

universe u
variable {α : Type u} [DecidableEq α]

section thetaToolbox

variable {S T : FormulaFinset α}

lemma imp_theta_box : ((LogicGLPoint3.theta S T) 🡒 ⋀ S.box) ∈ LogicGL := by
  unfold LogicGLPoint3.theta;
  refine impTrans andL ?_;
  apply imp_fconj_of_forall;
  intro C hC;
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC;
  exact impTrans (imp_fconj_of_mem (Finset.mem_image_of_mem _ hA)) andR;

lemma imp_theta_not_fdisj : ((LogicGLPoint3.theta S T) 🡒 ∼(⋁ (S ∪ T.box))) ∈ LogicGL := by
  apply imp_not_fdisj_of_forall;
  intro A hA;
  unfold LogicGLPoint3.theta;
  rcases Finset.mem_union.mp hA with hAS | hATbox;
  · exact impTrans andL (impTrans (imp_fconj_of_mem (Finset.mem_image_of_mem _ hAS)) andL);
  · obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hATbox;
    exact impTrans andR (imp_fconj_of_mem (Finset.mem_image_of_mem _ hA'));

end thetaToolbox

end LogicGL

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
  have hglue :
    ((⋀(Γ.box ∪ Γ) ⋏ theta S T) 🡒 ((⋀(Γ.box ∪ Γ ∪ S.box)) ⋏ ∼(⋁ (S ∪ T.box)))) ∈ LogicGL := by
    apply ProvableHilbert.ctxAndIntroRule;
    · have h1 : ((⋀(Γ.box ∪ Γ) ⋏ theta S T) 🡒 (⋀(Γ.box ∪ Γ) ⋏ ⋀ S.box)) ∈ LogicGL :=
        ProvableHilbert.ctxAndIntroRule ProvableHilbert.andL
          (ProvableHilbert.impTrans ProvableHilbert.andR LogicGL.imp_theta_box);
      exact ProvableHilbert.impTrans h1 (ProvableHilbert.imp_fconj_union (Γ.box ∪ Γ) S.box);
    · exact ProvableHilbert.impTrans ProvableHilbert.andR LogicGL.imp_theta_not_fdisj;
  have hpropbot : ((⋀(Γ.box ∪ Γ) ⋏ theta S T) 🡒 (⊥ : Formula α)) ∈ LogicGLPoint3 :=
    impTrans (of_GL hglue) hbotProp
  -- Push the contradiction inside the `◇`, using `dia_bot`.
  have hdiabot : ((◇ (⋀(Γ.box ∪ Γ) ⋏ theta S T)) 🡒 (⊥ : Formula α)) ∈ LogicGLPoint3 :=
    impTrans (diaImp' hpropbot) (of_GL LogicGL.dia_bot)
  -- Transport `□(⋀(Γ.box ∪ Γ))` (from `⋀Γ.box`) into the `◇θ(S, T)` witness.
  have hcombine : ((⋀Γ.box ⋏ ◇ (theta S T)) 🡒 ◇ (⋀(Γ.box ∪ Γ) ⋏ theta S T)) ∈ LogicGL :=
    ProvableHilbert.impTrans
      (ProvableHilbert.ctxAndIntroRule
        (ProvableHilbert.impTrans ProvableHilbert.andL LogicGL.imp_box_union)
        ProvableHilbert.andR)
      LogicGL.imp_dia_and
  exact impTrans (of_GL hcombine) hdiabot

/-- The Hilbert soundness of the `boxGLPoint3` rule, the Hilbert-calculus counterpart of
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
  -- Feed in `witness` to reduce `witnessDisj Δ` to `⋀(Δ.image ∼□·)`.
  have hantecedent : ((⋀Γ.box) ⋏ ⋀ (Δ.image (fun A => ∼□A))) 🡒 (⊥ : Formula α) ∈ LogicGLPoint3 :=
    impTrans (imp_and_congr_right' (witness hΔ)) hall
  -- De Morgan: `∼⋁Δ.box` derives `⋀(Δ.image ∼□·)`.
  have himg : (Δ.box).image (fun A => ∼A) = Δ.image (fun A => ∼□A) := by
    simp only [FormulaFinset.box, Finset.image_image, Function.comp_def];
  have hdemorgan : (∼(⋁ Δ.box) 🡒 ⋀ (Δ.image (fun A => ∼□A))) ∈ LogicGL := by
    have h0 := LogicGL.imp_not_fdisj_fconj_not (Δ := Δ.box);
    rwa [himg] at h0;
  have hstep : ((⋀Γ.box) ⋏ ∼(⋁ Δ.box)) 🡒 (⊥ : Formula α) ∈ LogicGLPoint3 :=
    impTrans (imp_and_congr_right' (of_GL hdemorgan)) hantecedent
  -- The classical propositional wrap-up: `∼(A ⋏ ∼B) 🡒 (A 🡒 B)`.
  exact mdp' LogicGL.imp_of_not_and_not hstep

end LogicGLPoint3

namespace LogicGLPoint3

universe u
variable {α : Type u} [DecidableEq α]

theorem of_provableGentzen {S : Sequent α} (h : ⊢ᵍ[GLPoint3] S) :
    ((⋀S.ant) 🡒 (⋁S.suc)) ∈ LogicGLPoint3 := by
  induction h with
  | axm A => simp; exact LogicGLPoint3.of_GL ProvableHilbert.impId
  | botL => simp; exact LogicGLPoint3.of_GL ProvableHilbert.efq
  | wkL _ hΓ ih =>
    exact LogicGLPoint3.impTrans (LogicGLPoint3.of_GL (ProvableHilbert.imp_fconj_fconj_of_subset (by grind))) ih
  | wkR _ hΔ ih =>
    exact LogicGLPoint3.impTrans ih (LogicGLPoint3.of_GL (ProvableHilbert.imp_fdisj_fdisj_of_subset (by grind)))
  | impL h₁ h₂ ih₁ ih₂ =>
    have e₁ := LogicGLPoint3.impTrans ih₁ (LogicGLPoint3.of_GL ProvableHilbert.imp_fdisj_insert)
    have e₂ := LogicGLPoint3.impTrans (LogicGLPoint3.of_GL ProvableHilbert.imp_fconj_insert) ih₂
    have ebridge := LogicGLPoint3.mdp' bridge_impL_imp (LogicGLPoint3.andIntro' e₁ e₂)
    exact LogicGLPoint3.impTrans (LogicGLPoint3.of_GL ProvableHilbert.imp_insert_fconj) ebridge
  | impR h ih =>
    have e := LogicGLPoint3.impTrans (LogicGLPoint3.of_GL ProvableHilbert.imp_fconj_insert)
      (LogicGLPoint3.impTrans ih (LogicGLPoint3.of_GL ProvableHilbert.imp_fdisj_insert))
    have ebridge := LogicGLPoint3.mdp' bridge_impR_imp e
    exact LogicGLPoint3.impTrans ebridge (LogicGLPoint3.of_GL ProvableHilbert.imp_insert_fdisj)
  | boxGLPoint3 hΔ h ih =>
    exact LogicGLPoint3.boxGLPoint3 hΔ ih

theorem of_provableGentzen_formula {A : Formula α} (h : ⊢ᵍ[GLPoint3] (∅ ⟹ {A})) :
    A ∈ LogicGLPoint3 := by
  have h' := of_provableGentzen h
  simp at h'
  exact Logic.sumNormal.mdp h' (LogicGLPoint3.of_GL ProvableHilbert.top)

end LogicGLPoint3

variable {α : Type u}

namespace LogicGLPoint3

open Model Model.World

lemma sound [DecidableEq α] {κ : Type u} [Nonempty κ] {M : Model κ α}
    [M.IsFiniteGLPoint3] {A : Formula α} (h : A ∈ LogicGLPoint3) : M ⊧ A := by
  induction h using LogicGLPoint3.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.finite_soundness h M;
  | axiomWeakPoint3 => exact Model.validate_axiomWeakPoint3;
  | mdp ihAB ihA => exact fun x => (ihAB x) (ihA x);
  | nec ih => exact fun x y _ => ih y;

variable [DecidableEq α] {A : Formula α}

/-- Kripke completeness for `LogicGLPoint3`.

- [VS83, Theorem 10, Theorem 11(b), Theorem 11(c)]
-/
theorem provability_TFAE : [
  A ∈ LogicGLPoint3,
  ⊢ᵍ[GLPoint3] (∅ ⟹ {A}),
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A,
  ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGLPoint3] → M ⊧ A,
  ∀ (n : ℕ) [NeZero n] (M : RootedModel (Fin n) α), [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A
].TFAE := by
  tfae_have 2 → 1 := LogicGLPoint3.of_provableGentzen_formula;
  tfae_have 1 → 3 := fun h {κ} _ M _ => LogicGLPoint3.sound h;
  tfae_have 5 → 2 := by
    intro h;
    apply LogicGLPoint3.ProvableGentzen.Kripke.completeness;
    intro n _ M _;
    exact Model.validateSequent_singleton_iff.mpr (h n M);
  tfae_have 3 → 4 := fun h {κ} _ M _ => h M.toModel M.root.1;
  tfae_have 4 → 3 := by
    intro h κ _ M _ x;
    exact Model.toRootedModel.forces_same_at_root.mp (h (M.toRootedModel x));
  tfae_have 3 → 5 := by
    intro h n _ M _;
    exact Model.validate_reindex_iff.mp <| h (M.reindex (Equiv.ulift (α := Fin n)).symm);
  tfae_have 5 → 3 := by
    intro h κ _ M _;
    haveI : Finite κ := (inferInstance : Finite M.World);
    exact Model.validate_toConcrete_iff.mp <| h M.card M.toConcrete;
  tfae_have 4 → 6 := by
    intro h n _ M _;
    exact RootedModel.forces_reindex_root_iff.mp <| h (M.reindex (Equiv.ulift (α := Fin n)).symm);
  tfae_have 6 → 4 := by
    intro h κ _ M _;
    haveI : Finite κ := (inferInstance : Finite M.World);
    exact RootedModel.forces_toConcrete_root_iff.mp <| h M.card M.toConcrete;
  tfae_finish;

theorem iff_forces : A ∈ LogicGLPoint3 ↔
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ A :=
  provability_TFAE.out 0 2

theorem iff_forces_root : A ∈ LogicGLPoint3 ↔
  ∀ {κ : Type u}, [Nonempty κ] → ∀ M : RootedModel κ α, [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A :=
  provability_TFAE.out 0 3

theorem iff_forces_concrete : A ∈ LogicGLPoint3 ↔
  ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGLPoint3] → M ⊧ A :=
  provability_TFAE.out 0 4

theorem iff_forces_root_concrete : A ∈ LogicGLPoint3 ↔
  ∀ (n : ℕ) [NeZero n] (M : RootedModel (Fin n) α), [M.IsFiniteGLPoint3] → M.root.1 ⊩[_] A :=
  provability_TFAE.out 0 5

variable {n : ℕ} [NeZero n]

theorem not_mem_of_concrete_root_not_forces (M : RootedModel (Fin n) α) [M.IsFiniteGLPoint3]
  (h : M.root.1 ⊮[_] A) : A ∉ LogicGLPoint3 :=
  fun hA => h <| iff_forces_root_concrete.mp hA n M

theorem concrete_root_forces_of_mem (M : RootedModel (Fin n) α) [M.IsFiniteGLPoint3]
  (h : A ∈ LogicGLPoint3) : M.root.1 ⊩[_] A :=
  iff_forces_root_concrete.mp h n M

theorem not_mem_of_concrete_not_forces (M : Model (Fin n) α) [M.IsFiniteGLPoint3] {x : M.World}
  (h : x ⊮[M] A) : A ∉ LogicGLPoint3 :=
  fun hA => h <| iff_forces_concrete.mp hA n M x

theorem concrete_forces_of_mem (M : Model (Fin n) α) [M.IsFiniteGLPoint3] (h : A ∈ LogicGLPoint3)
  (x : M.World) : x ⊩[M] A :=
  iff_forces_concrete.mp h n M x

end LogicGLPoint3

end
