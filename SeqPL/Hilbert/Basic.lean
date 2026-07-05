module

public import SeqPL.Gentzen.WithCut
public import SeqPL.Formula.Map

@[expose]
public section

variable {α : Type u}

/--
Hilbert-style proof system for `GL`, over a `Minimal + DNE` propositional base.

The propositional primitives (`implyK`, `implyS`, `dne`, `andElimL`, `andElimR`,
`andIntro`, `orIntroL`, `orIntroR`, `orElim`) mirror `Foundation`'s minimal Hilbert
calculus (`Foundation.Propositional.Hilbert.Minimal`), extended with double negation
elimination (`dne`) to make the propositional fragment classical. The Łukasiewicz-style
axiom `elimContra : (∼A 🡒 ∼B) 🡒 (B 🡒 A)` is recovered as a derived lemma.
-/
inductive ProofHilbert : Formula α → Type u
| implyK   {A B}   : ProofHilbert $ A 🡒 B 🡒 A
| implyS   {A B C} : ProofHilbert $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| dne      {A}     : ProofHilbert $ ∼∼A 🡒 A
| andElimL {A B}   : ProofHilbert $ (A ⋏ B) 🡒 A
| andElimR {A B}   : ProofHilbert $ (A ⋏ B) 🡒 B
| andIntro {A B}   : ProofHilbert $ A 🡒 B 🡒 (A ⋏ B)
| orIntroL {A B}   : ProofHilbert $ A 🡒 (A ⋎ B)
| orIntroR {A B}   : ProofHilbert $ B 🡒 (A ⋎ B)
| orElim   {A B C} : ProofHilbert $ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)
| modalK   {A B}   : ProofHilbert $ □(A 🡒 B) 🡒 (□A 🡒 □B)
| modal4   {A}     : ProofHilbert $ □A 🡒 □□A
| modalL   {A}     : ProofHilbert $ □(□A 🡒 A) 🡒 □A
| mdp      {A B}   : ProofHilbert (A 🡒 B) → ProofHilbert A → ProofHilbert B
| nec      {A}     : ProofHilbert A → ProofHilbert (□A)
prefix:50 "⊢ʰ! " => ProofHilbert

abbrev ProvableHilbert (A : Formula α) := Nonempty (⊢ʰ! A)
prefix:50 "⊢ʰ " => ProvableHilbert


namespace ProvableHilbert

variable {A B C : Formula α}

@[grind <=] lemma nec : ⊢ʰ A → ⊢ʰ □A := λ ⟨h⟩ => ⟨ProofHilbert.nec h⟩
@[grind =>] lemma mdp : ⊢ʰ (A 🡒 B) → ⊢ʰ A → ⊢ʰ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[simp, grind .] lemma implyK : ⊢ʰ A 🡒 B 🡒 A := ⟨ProofHilbert.implyK⟩
@[simp, grind .] lemma implyS : ⊢ʰ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofHilbert.implyS⟩
@[simp, grind .] lemma dne : ⊢ʰ ∼∼A 🡒 A := ⟨ProofHilbert.dne⟩
@[simp, grind .] lemma andElimL : ⊢ʰ (A ⋏ B) 🡒 A := ⟨ProofHilbert.andElimL⟩
@[simp, grind .] lemma andElimR : ⊢ʰ (A ⋏ B) 🡒 B := ⟨ProofHilbert.andElimR⟩
@[simp, grind .] lemma andIntro : ⊢ʰ A 🡒 B 🡒 (A ⋏ B) := ⟨ProofHilbert.andIntro⟩
@[simp, grind .] lemma orIntroL : ⊢ʰ A 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroL⟩
@[simp, grind .] lemma orIntroR : ⊢ʰ B 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroR⟩
@[simp, grind .] lemma orElim : ⊢ʰ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C) := ⟨ProofHilbert.orElim⟩
@[simp, grind .] lemma modalK : ⊢ʰ □(A 🡒 B) 🡒 (□A 🡒 □B) := ⟨ProofHilbert.modalK⟩
@[simp, grind .] lemma modal4 : ⊢ʰ □A 🡒 □□A := ⟨ProofHilbert.modal4⟩
@[simp, grind .] lemma modalL : ⊢ʰ □(□A 🡒 A) 🡒 □A := ⟨ProofHilbert.modalL⟩

/-- Compatibility alias for the Łukasiewicz-style axiom `implyK`. -/
@[simp, grind .] lemma prop1 : ⊢ʰ A 🡒 B 🡒 A := implyK
/-- Compatibility alias for the Łukasiewicz-style axiom `implyS`. -/
@[simp, grind .] lemma prop2 : ⊢ʰ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := implyS

@[grind <=] lemma af :  ⊢ʰ A → ⊢ʰ B 🡒 A := λ h => mdp implyK h

@[simp, grind .]
lemma impId : ⊢ʰ A 🡒 A := mdp (mdp (implyS (B := A 🡒 A)) implyK) implyK

set_option linter.unusedVariables false in
@[induction_eliminator]
lemma rec
  {motive : (A : Formula α) → ⊢ʰ A → Prop}
  (implyK   : ∀ {A B} (h : ⊢ʰ A 🡒 B 🡒 A), motive _ h)
  (implyS   : ∀ {A B C} (h : ⊢ʰ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)), motive _ h)
  (dne      : ∀ {A} (h : ⊢ʰ ∼∼A 🡒 A), motive _ h)
  (andElimL : ∀ {A B} (h : ⊢ʰ (A ⋏ B) 🡒 A), motive _ h)
  (andElimR : ∀ {A B} (h : ⊢ʰ (A ⋏ B) 🡒 B), motive _ h)
  (andIntro : ∀ {A B} (h : ⊢ʰ A 🡒 B 🡒 (A ⋏ B)), motive _ h)
  (orIntroL : ∀ {A B} (h : ⊢ʰ A 🡒 (A ⋎ B)), motive _ h)
  (orIntroR : ∀ {A B} (h : ⊢ʰ B 🡒 (A ⋎ B)), motive _ h)
  (orElim   : ∀ {A B C} (h : ⊢ʰ (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)), motive _ h)
  (modalK   : ∀ {A B} (h : ⊢ʰ □(A 🡒 B) 🡒 (□A 🡒 □B)), motive _ h)
  (modal4   : ∀ {A} (h : ⊢ʰ □A 🡒 □□A), motive _ h)
  (modalL   : ∀ {A} (h : ⊢ʰ □(□A 🡒 A) 🡒 □A), motive _ h)
  (mdp      : ∀ {A B} (h₁ : ⊢ʰ A 🡒 B) (h₂ : ⊢ʰ A), motive _ h₁ → motive _ h₂ → motive _ (mdp h₁ h₂))
  (nec      : ∀ {A} (h : ⊢ʰ A), motive A h → motive _ (nec h))
  : ∀ {A} (h : ⊢ʰ A), motive _ h := by
  rintro A ⟨h⟩;
  induction h <;> grind;

end ProvableHilbert


inductive DeductionHilbert : FormulaSet α → Formula α → Type _
| ofProof {X A} : ⊢ʰ! A → DeductionHilbert X A
| ofContext {X A} : A ∈ X → DeductionHilbert X A
| mdp {X A B} : (DeductionHilbert X (A 🡒 B)) → (DeductionHilbert X A) → (DeductionHilbert X B)
infix:50 " ⊢ʰ! " => DeductionHilbert

abbrev DeducibleHilbert (X : FormulaSet α) (A : Formula α) := Nonempty (X ⊢ʰ! A)
infix:50 " ⊢ʰ " => DeducibleHilbert

namespace DeducibleHilbert

variable {X Y : FormulaSet α} {A B C : Formula α}

@[grind <=] lemma ofProvable : (⊢ʰ A) → (X ⊢ʰ A) := λ ⟨h⟩ => ⟨.ofProof h⟩
@[grind <=] lemma ofContext : A ∈ X → (X ⊢ʰ A) := λ h => ⟨.ofContext h⟩
@[grind =>] lemma mdp : X ⊢ʰ A 🡒 B → X ⊢ʰ A → X ⊢ʰ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨.mdp h₁ h₂⟩

@[induction_eliminator]
protected lemma rec
  {motive : (X : FormulaSet α) → (A : Formula α) → (X ⊢ʰ A) → Prop}
  (ofProvable : ∀ {X A}, (h : ⊢ʰ A) → motive X A (ofProvable h))
  (ofContext : ∀ {X A}, (h : A ∈ X) → motive X A (ofContext h))
  (mdp : ∀ {X A B}, (hAB : X ⊢ʰ A 🡒 B) → (hA : X ⊢ʰ A) → (motive X (A 🡒 B) hAB) → (motive X A hA) → (motive X B (mdp hAB hA)))
  : ∀ {X A}, (h : X ⊢ʰ A) → motive X A h := by
  rintro X A ⟨h⟩;
  induction h with
  | ofProof h => apply ofProvable ⟨h⟩;
  | _ => grind;

lemma of_subset_ctx (hXY : X ⊆ Y) : (X ⊢ʰ A) → (Y ⊢ʰ A) := λ h => by induction h <;> grind;

lemma to_ctx : (X ⊢ʰ A 🡒 B) → (insert A X ⊢ʰ B) := λ h => by
  apply mdp;
  . show insert A X ⊢ʰ A 🡒 B;
    exact of_subset_ctx (by simp) h;
  . exact ofContext (by simp);

lemma drop_ctx (h : insert A X ⊢ʰ B) : (X ⊢ʰ A 🡒 B) := by
  generalize e : insert A X = Y at h;
  induction h with
  | ofProvable h =>
    subst e;
    exact ofProvable $ .af h;
  | ofContext h =>
    subst e;
    rcases Set.mem_insert_iff.mp h with (rfl | h);
    . exact ofProvable .impId;
    . apply mdp;
      . exact ofProvable (.prop1);
      . exact ofContext h;
  | mdp _ _ ihAB ihA =>
    subst e;
    replace ihAB := ihAB rfl;
    replace ihA := ihA rfl;
    exact mdp (mdp (ofProvable (.prop2)) ihAB) ihA;

theorem deduction_theorem : (insert A X ⊢ʰ B) ↔ (X ⊢ʰ A 🡒 B) := ⟨drop_ctx, to_ctx⟩

lemma iff_empty_ctx : (∅ ⊢ʰ A) ↔ (⊢ʰ A) := by
  constructor
  . intro h;
    generalize e : (∅ : FormulaSet α) = X at h;
    induction h <;> grind;
  . apply ofProvable;

lemma iff_singleton_deducible_provable : ({A} ⊢ʰ B) ↔ (⊢ʰ A 🡒 B) := by
  rw [show ({A} : FormulaSet α) = insert A ∅ by simp];
  apply Iff.trans deduction_theorem iff_empty_ctx;

/-- Context-level transitivity of implication. -/
lemma impTrans (p : X ⊢ʰ A 🡒 B) (q : X ⊢ʰ B 🡒 C) : X ⊢ʰ A 🡒 C :=
  mdp (mdp (ofProvable ProvableHilbert.prop2) (mdp (ofProvable ProvableHilbert.prop1) q)) p

end DeducibleHilbert




namespace ProvableGentzen

theorem of_provableHilbert [DecidableEq α] : ⊢ʰ A → ⊢ᵍ (∅ ⟹ {A} : Sequent α) := by
  intro h;
  induction h with
  | implyK => exact .implyK;
  | implyS => exact .implyS;
  | dne => exact .dne;
  | andElimL => exact .andElimL;
  | andElimR => exact .andElimR;
  | andIntro => exact .andIntro;
  | orIntroL => exact .orIntroL;
  | orIntroR => exact .orIntroR;
  | orElim => exact .orElim;
  | modalK => exact .modalK;
  | modal4 => exact .modal4;
  | modalL => exact .modalL;
  | nec _ h => exact .nec h;
  | mdp _ _ ih₁ ih₂ => exact .mdp ih₁ ih₂;

end ProvableGentzen


namespace ProvableHilbert

variable {A B C D : Formula α}

@[simp, grind .] lemma top : ⊢ʰ (⊤ : Formula α) := by simp [Formula.top];

lemma impTrans : ⊢ʰ A 🡒 B → ⊢ʰ B 🡒 C → ⊢ʰ A 🡒 C := by
  intro h₁ h₂;
  replace h₁ := DeducibleHilbert.iff_singleton_deducible_provable.mpr h₁;
  replace h₂ : {A} ⊢ʰ B 🡒 C := DeducibleHilbert.ofProvable h₂;
  exact DeducibleHilbert.iff_singleton_deducible_provable.mp $ DeducibleHilbert.mdp h₂ h₁;

/-- Double negation introduction: `A 🡒 ∼∼A`. -/
@[grind =>] lemma dni : ⊢ʰ A 🡒 ∼∼A := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼A, A}`, goal `⊥`
  have hA  : ({∼A, A}) ⊢ʰ A     := DeducibleHilbert.ofContext (by grind);
  have hnA : ({∼A, A}) ⊢ʰ A 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnA hA;

/-- The Łukasiewicz-style contraposition axiom: `(∼A 🡒 ∼B) 🡒 (B 🡒 A)`. -/
@[simp, grind .] lemma elimContra : ⊢ʰ (∼A 🡒 ∼B) 🡒 (B 🡒 A) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{B, ∼A 🡒 ∼B}`, goal `A`
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  -- goal `∼∼A`, i.e. `∼A 🡒 ⊥`
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼A, B, ∼A 🡒 ∼B}`, goal `⊥`
  have hnA  : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ ∼A      := DeducibleHilbert.ofContext (by grind);
  have himp : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ ∼A 🡒 ∼B := DeducibleHilbert.ofContext (by grind);
  have hnB  : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ ∼B      := DeducibleHilbert.mdp himp hnA;
  have hB   : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ B       := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnB hB;

@[simp, grind .] lemma efq : ⊢ʰ ⊥ 🡒 A := mdp elimContra (af top)
@[grind <=] lemma efqRule : ⊢ʰ (⊥ : Formula α) → ⊢ʰ A := mdp efq

/-- Left conjunction elimination (alias for the primitive `andElimL`). -/
@[simp, grind .] lemma andL : ⊢ʰ (A ⋏ B) 🡒 A := andElimL
/-- Right conjunction elimination (alias for the primitive `andElimR`). -/
@[simp, grind .] lemma andR : ⊢ʰ (A ⋏ B) 🡒 B := andElimR

@[grind =>] lemma andLRule : ⊢ʰ (A ⋏ B) → ⊢ʰ A := mdp andL
@[grind =>] lemma andRRule : ⊢ʰ (A ⋏ B) → ⊢ʰ B := mdp andR

/-- Left disjunction introduction (alias for the primitive `orIntroL`). -/
@[simp, grind .] lemma orL : ⊢ʰ A 🡒 (A ⋎ B) := orIntroL
/-- Right disjunction introduction (alias for the primitive `orIntroR`). -/
@[simp, grind .] lemma orR : ⊢ʰ B 🡒 (A ⋎ B) := orIntroR

@[grind =>] lemma orLRule : ⊢ʰ A → ⊢ʰ (A ⋎ B) := mdp orL
@[grind =>] lemma orRRule : ⊢ʰ B → ⊢ʰ (A ⋎ B) := mdp orR

attribute [grind <=] DeducibleHilbert.ofContext
attribute [grind =>] DeducibleHilbert.mdp

lemma mdp₂ : ⊢ʰ A 🡒 B 🡒 C → ⊢ʰ A → ⊢ʰ B → ⊢ʰ C := λ h₁ h₂ h₃ => mdp (mdp h₁ h₂) h₃

@[grind <=]
lemma andIntroRule : ⊢ʰ A → ⊢ʰ B → ⊢ʰ (A ⋏ B) := mdp₂ andIntro

@[simp, grind .]
lemma ctxAndIntro : ⊢ʰ (A 🡒 B) 🡒 (A 🡒 C) 🡒 (A 🡒 (B ⋏ C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have h₁ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ B 🡒 (∼C) := by grind;
  have h₂ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ A 🡒 B := by grind;
  have h₃ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ A 🡒 C := by grind;
  have h₄ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ A := by grind;
  grind;

lemma ctxAndIntroRule : ⊢ʰ (A 🡒 B) → ⊢ʰ (A 🡒 C) → ⊢ʰ (A 🡒 (B ⋏ C)) := mdp₂ ctxAndIntro


lemma imp_lconj_of_mem {Γ : FormulaList α} (h : A ∈ Γ) : ⊢ʰ ⋀Γ 🡒 A := by
  match Γ with
  | [] | [B] => simp_all;
  | B :: C :: Γ =>
    simp only [List.mem_cons] at h;
    rcases h with (rfl | rfl | h);
    . simp [FormulaList.conj];
    . exact impTrans andR $ imp_lconj_of_mem (Γ := A :: Γ) (by simp);
    . exact impTrans andR $ imp_lconj_of_mem (Γ := C :: Γ) (by grind);


lemma imp_lconj_lconj_of_subset {Γ Γ' : FormulaList α} (h : Γ' ⊆ Γ) : ⊢ʰ ⋀Γ 🡒 ⋀Γ' := by
  match Γ' with
  | [] => apply af; simp;
  | [B] => apply imp_lconj_of_mem; grind;
  | B :: C :: Γ' =>
    have h₁ := imp_lconj_of_mem (Γ := Γ) (A := B) (by grind);
    have h₂ := imp_lconj_lconj_of_subset (Γ := Γ) (Γ' := C :: Γ') (by grind);
    exact ctxAndIntroRule h₁ h₂;

@[grind <=]
lemma imp_fconj_fconj_of_subset {Γ Γ' : FormulaFinset α} (h : Γ' ⊆ Γ) : ⊢ʰ ⋀Γ 🡒 ⋀Γ' := by
  apply imp_lconj_lconj_of_subset;
  intro A;
  simpa using @h A;

/-- Combinatory reassociation of a conjunction: `(A ⋏ B) 🡒 (C 🡒 D)` derives `(A ⋏ C) 🡒 (B 🡒 D)`. -/
@[simp, grind .]
lemma imp_reassoc : ⊢ʰ ((A ⋏ B) 🡒 (C 🡒 D)) 🡒 ((A ⋏ C) 🡒 (B 🡒 D)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hAC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ A ⋏ C := DeducibleHilbert.ofContext (by grind)
  have hA : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andL) hAC
  have hC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andR) hAC
  have hB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ (A ⋏ B) 🡒 (C 🡒 D) :=
    DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hAB) hC

/-- Elimination of a conjunction: `(A ⋏ B) 🡒 C` derives `A 🡒 (B 🡒 C)`. -/
@[simp, grind .]
lemma imp_uncurry_and : ⊢ʰ ((A ⋏ B) 🡒 C) 🡒 (A 🡒 (B 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ A := DeducibleHilbert.ofContext (by grind)
  have hB : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ (A ⋏ B) 🡒 C := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp himp hAB

/-- Swapping antecedents: `A 🡒 (B 🡒 C)` derives `B 🡒 (A 🡒 C)`. -/
@[simp, grind .]
lemma imp_swap : ⊢ʰ (A 🡒 (B 🡒 C)) 🡒 (B 🡒 (A 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({A, B, A 🡒 (B 🡒 C)}) ⊢ʰ A := DeducibleHilbert.ofContext (by grind)
  have hB : ({A, B, A 🡒 (B 🡒 C)}) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have himp : ({A, B, A 🡒 (B 🡒 C)}) ⊢ʰ A 🡒 (B 🡒 C) := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hA) hB


/-- Disjunction elimination (Minimal-style `orElim`), recovered classically:
from `A 🡒 C` and `B 🡒 C` derive `(A ⋎ B) 🡒 C`. -/
lemma orElim' (h₁ : ⊢ʰ A 🡒 C) (h₂ : ⊢ʰ B 🡒 C) : ⊢ʰ (A ⋎ B) 🡒 C := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼C, A ⋎ B}`, goal `⊥`
  have key : ({∼C, A ⋎ B}) ⊢ʰ A 🡒 ⊥ := by
    apply DeducibleHilbert.deduction_theorem.mp;
    -- context `{A, ∼C, A ⋎ B}`, goal `⊥`
    have hA  : ({A, ∼C, A ⋎ B}) ⊢ʰ A     := DeducibleHilbert.ofContext (by grind);
    have hnC : ({A, ∼C, A ⋎ B}) ⊢ʰ C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
    exact DeducibleHilbert.mdp hnC (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h₁) hA);
  have hAB : ({∼C, A ⋎ B}) ⊢ʰ (A 🡒 ⊥) 🡒 B := DeducibleHilbert.ofContext (by grind);
  have hB  : ({∼C, A ⋎ B}) ⊢ʰ B := DeducibleHilbert.mdp hAB key;
  have hC  : ({∼C, A ⋎ B}) ⊢ʰ C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h₂) hB;
  have hnC : ({∼C, A ⋎ B}) ⊢ʰ C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnC hC;

lemma imp_ldisj_of_mem {Γ : FormulaList α} (h : A ∈ Γ) : ⊢ʰ A 🡒 ⋁Γ := by
  match Γ with
  | [] | [B] => simp_all;
  | B :: C :: Γ =>
    simp only [List.mem_cons] at h;
    rcases h with (rfl | rfl | h);
    . simp [FormulaList.disj];
    . exact impTrans (imp_ldisj_of_mem (Γ := A :: Γ) (by simp)) orR;
    . exact impTrans (imp_ldisj_of_mem (Γ := C :: Γ) (by grind)) orR;

@[grind <=]
lemma imp_ldisj_ldisj_of_subset {Γ Γ' : FormulaList α} (h : Γ ⊆ Γ') : ⊢ʰ ⋁Γ 🡒 ⋁Γ' := by
  match Γ with
  | [] => simp;
  | [B] => apply imp_ldisj_of_mem; grind;
  | B :: C :: Γ =>
    have h₁ := imp_ldisj_of_mem (Γ := Γ') (A := B) (by grind);
    have h₂ := imp_ldisj_ldisj_of_subset (Γ := C :: Γ) (Γ' := Γ') (by grind);
    exact orElim' h₁ h₂;

@[grind <=]
lemma imp_fdisj_fdisj_of_subset {Γ Γ' : FormulaFinset α} (h : Γ ⊆ Γ') : ⊢ʰ ⋁Γ 🡒 ⋁Γ' := by
  apply imp_ldisj_ldisj_of_subset;
  intro A;
  simpa using @h A;

/-! ### Introduction/elimination for list and finset conjunctions/disjunctions -/

/-- If `B` implies every member of `Γ`, it implies their conjunction. -/
lemma imp_lconj_of_forall {Γ : FormulaList α} (h : ∀ A ∈ Γ, ⊢ʰ B 🡒 A) : ⊢ʰ B 🡒 ⋀Γ := by
  match Γ with
  | [] => exact af top;
  | [C] => exact h C (by simp);
  | C :: D :: Γ =>
    exact ctxAndIntroRule (h C (by simp)) (imp_lconj_of_forall (fun A hA => h A (List.mem_cons_of_mem _ hA)));

/-- If every member of `Γ` implies `D`, their disjunction implies `D`. -/
lemma imp_ldisj_elim {Γ : FormulaList α} (h : ∀ A ∈ Γ, ⊢ʰ A 🡒 D) : ⊢ʰ ⋁Γ 🡒 D := by
  match Γ with
  | [] => exact (efq : ⊢ʰ ⊥ 🡒 D);
  | [B] => exact h B (by simp);
  | B :: C :: Γ =>
    exact orElim' (h B (by simp)) (imp_ldisj_elim (fun A hA => h A (List.mem_cons_of_mem _ hA)));

lemma imp_fconj_of_mem {Δ : FormulaFinset α} (h : A ∈ Δ) : ⊢ʰ ⋀Δ 🡒 A :=
  imp_lconj_of_mem (Finset.mem_toList.mpr h)

lemma imp_mem_fdisj {Δ : FormulaFinset α} (h : A ∈ Δ) : ⊢ʰ A 🡒 ⋁Δ :=
  imp_ldisj_of_mem (Finset.mem_toList.mpr h)

lemma imp_fconj_of_forall {Δ : FormulaFinset α} (h : ∀ A ∈ Δ, ⊢ʰ B 🡒 A) : ⊢ʰ B 🡒 ⋀Δ :=
  imp_lconj_of_forall (fun A hA => h A (Finset.mem_toList.mp hA))

lemma imp_fdisj_elim {Δ : FormulaFinset α} (h : ∀ A ∈ Δ, ⊢ʰ A 🡒 D) : ⊢ʰ ⋁Δ 🡒 D :=
  imp_ldisj_elim (fun A hA => h A (Finset.mem_toList.mp hA))

/-- `B ⋏ ⋀Δ` implies `⋀(insert B Δ)`. -/
lemma imp_fconj_insert [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ (B ⋏ ⋀Δ) 🡒 ⋀(insert B Δ) := by
  apply imp_fconj_of_forall;
  intro A hA;
  rcases Finset.mem_insert.mp hA with rfl | hA;
  · exact andL;
  · exact impTrans andR (imp_fconj_of_mem hA);

/-- `⋁(insert B Δ)` implies `B ⋎ ⋁Δ`. -/
lemma imp_fdisj_insert [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ ⋁(insert B Δ) 🡒 (B ⋎ ⋁Δ) := by
  apply imp_fdisj_elim;
  intro A hA;
  rcases Finset.mem_insert.mp hA with rfl | hA;
  · exact orL;
  · exact impTrans (imp_mem_fdisj hA) orR;

/-- `B ⋎ ⋁Δ` implies `⋁(insert B Δ)`. -/
lemma imp_insert_fdisj [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ (B ⋎ ⋁Δ) 🡒 ⋁(insert B Δ) :=
  orElim' (imp_mem_fdisj (by simp)) (imp_fdisj_fdisj_of_subset (by simp))

/-- Classical case split: from `A 🡒 C` and `A ⋎ C` conclude `C`. -/
lemma orCasesImp : ⊢ʰ (A 🡒 C) 🡒 (A ⋎ C) 🡒 C := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼C, A ⋎ C, A 🡒 C}`, goal `⊥`
  have hnC : ({∼C, A ⋎ C, A 🡒 C}) ⊢ʰ C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  have hnA : ({∼C, A ⋎ C, A 🡒 C}) ⊢ʰ A 🡒 ⊥ := by
    apply DeducibleHilbert.deduction_theorem.mp;
    have hA   : ({A, ∼C, A ⋎ C, A 🡒 C}) ⊢ʰ A     := DeducibleHilbert.ofContext (by grind);
    have hAC  : ({A, ∼C, A ⋎ C, A 🡒 C}) ⊢ʰ A 🡒 C := DeducibleHilbert.ofContext (by grind);
    have hnC' : ({A, ∼C, A ⋎ C, A 🡒 C}) ⊢ʰ C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
    exact DeducibleHilbert.mdp hnC' (DeducibleHilbert.mdp hAC hA);
  have hAvC : ({∼C, A ⋎ C, A 🡒 C}) ⊢ʰ (A 🡒 ⊥) 🡒 C := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnC (DeducibleHilbert.mdp hAvC hnA);

/-- From `∼(A 🡒 B)` we recover `A`. -/
lemma neg_imp_left : ⊢ʰ ∼(A 🡒 B) 🡒 A := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼A, ∼(A 🡒 B)}`, goal `⊥`
  have hAB : ({∼A, ∼(A 🡒 B)}) ⊢ʰ A 🡒 B := by
    apply DeducibleHilbert.deduction_theorem.mp;
    apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable efq);
    have hA  : ({A, ∼A, ∼(A 🡒 B)}) ⊢ʰ A     := DeducibleHilbert.ofContext (by grind);
    have hnA : ({A, ∼A, ∼(A 🡒 B)}) ⊢ʰ A 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
    exact DeducibleHilbert.mdp hnA hA;
  have hnAB : ({∼A, ∼(A 🡒 B)}) ⊢ʰ (A 🡒 B) 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnAB hAB;

/-- From `∼(A 🡒 B)` we recover `∼B`. -/
lemma neg_imp_right : ⊢ʰ ∼(A 🡒 B) 🡒 ∼B := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{B, ∼(A 🡒 B)}`, goal `⊥` (since `∼B = B 🡒 ⊥`)
  have hAB : ({B, ∼(A 🡒 B)}) ⊢ʰ A 🡒 B := by
    apply DeducibleHilbert.deduction_theorem.mp;
    exact DeducibleHilbert.ofContext (by grind);
  have hnAB : ({B, ∼(A 🡒 B)}) ⊢ʰ (A 🡒 B) 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnAB hAB;

/-- Context-level disjunction elimination, recovered classically via `dne`. -/
lemma _root_.DeducibleHilbert.orElim {X : FormulaSet α}
    (h₁ : X ⊢ʰ A 🡒 C) (h₂ : X ⊢ʰ B 🡒 C) (h : X ⊢ʰ A ⋎ B) : X ⊢ʰ C := by
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `insert (∼C) X`, goal `⊥`
  have hnC : (insert (∼C) X) ⊢ʰ C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  have h₁' : (insert (∼C) X) ⊢ʰ A 🡒 C := DeducibleHilbert.of_subset_ctx (by grind) h₁;
  have h₂' : (insert (∼C) X) ⊢ʰ B 🡒 C := DeducibleHilbert.of_subset_ctx (by grind) h₂;
  have h'  : (insert (∼C) X) ⊢ʰ (A 🡒 ⊥) 🡒 B := DeducibleHilbert.of_subset_ctx (by grind) h;
  have hnA : (insert (∼C) X) ⊢ʰ A 🡒 ⊥ := DeducibleHilbert.impTrans h₁' hnC;
  have hB  : (insert (∼C) X) ⊢ʰ B := DeducibleHilbert.mdp h' hnA;
  have hC  : (insert (∼C) X) ⊢ʰ C := DeducibleHilbert.mdp h₂' hB;
  exact DeducibleHilbert.mdp hnC hC;

/-- `⋀(insert B Δ)` decomposes into `B ⋏ ⋀Δ`. -/
lemma imp_insert_fconj [DecidableEq α] {Δ : FormulaFinset α} :
    ⊢ʰ ⋀(insert B Δ) 🡒 (B ⋏ ⋀Δ) :=
  ctxAndIntroRule (imp_fconj_of_mem (by simp)) (imp_fconj_fconj_of_subset (by simp))

/-- Classical push of an implication across a disjunction: `A 🡒 (B ⋎ D)` derives `(A 🡒 B) ⋎ D`. -/
lemma imp_push_disj : ⊢ʰ (A 🡒 (B ⋎ D)) 🡒 ((A 🡒 B) ⋎ D) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  -- context `{A 🡒 (B ⋎ D)}`, goal `(A 🡒 B) ⋎ D`
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context now also holds `∼((A 🡒 B) ⋎ D)`, goal `⊥`
  have hn : ({∼(A 🡒 B ⋎ D), A 🡒 (B ⋎ D)}) ⊢ʰ ((A 🡒 B) ⋎ D) 🡒 ⊥ :=
    DeducibleHilbert.ofContext (by grind);
  have hmain : ({∼(A 🡒 B ⋎ D), A 🡒 (B ⋎ D)}) ⊢ʰ A 🡒 (B ⋎ D) :=
    DeducibleHilbert.ofContext (by grind);
  have hnAB : ({∼(A 🡒 B ⋎ D), A 🡒 (B ⋎ D)}) ⊢ʰ (A 🡒 B) 🡒 ⊥ :=
    DeducibleHilbert.impTrans (DeducibleHilbert.ofProvable orL) hn;
  refine DeducibleHilbert.orElim (A := B) (B := D) (C := ⊥) ?_ ?_ ?_;
  · exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable neg_imp_right) hnAB;
  · exact DeducibleHilbert.impTrans (DeducibleHilbert.ofProvable orR) hn;
  · exact DeducibleHilbert.mdp hmain (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable neg_imp_left) hnAB);

/-- Bridge lemma for the `(→L)` rule: from `⋀Γ 🡒 (A ⋎ ⋁Δ)` and `(B ⋏ ⋀Γ) 🡒 ⋁Δ`
conclude `((A 🡒 B) ⋏ ⋀Γ) 🡒 ⋁Δ`. -/
lemma bridge_impL (ha : ⊢ʰ C 🡒 (A ⋎ D)) (hb : ⊢ʰ (B ⋏ C) 🡒 D) :
    ⊢ʰ ((A 🡒 B) ⋏ C) 🡒 D := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  -- context `X = {(A 🡒 B) ⋏ C}`, goal `D`
  have hmem : ({(A 🡒 B) ⋏ C}) ⊢ʰ (A 🡒 B) ⋏ C := DeducibleHilbert.ofContext (by grind);
  have hC  : ({(A 🡒 B) ⋏ C}) ⊢ʰ C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem;
  have hAD : ({(A 🡒 B) ⋏ C}) ⊢ʰ A ⋎ D := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ha) hC;
  have hAtoD : ({(A 🡒 B) ⋏ C}) ⊢ʰ A 🡒 D := by
    apply DeducibleHilbert.deduction_theorem.mp;
    -- context `insert A {(A 🡒 B) ⋏ C}`, goal `D`
    have hmem' : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ (A 🡒 B) ⋏ C := DeducibleHilbert.ofContext (by grind);
    have hAB : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ A 🡒 B := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hmem';
    have hCi : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem';
    have hA  : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
    have hB  : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ B := DeducibleHilbert.mdp hAB hA;
    have hBC : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ B ⋏ C := DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hB) hCi;
    exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable hb) hBC;
  have hDtoD : ({(A 🡒 B) ⋏ C}) ⊢ʰ D 🡒 D := DeducibleHilbert.ofProvable impId;
  exact DeducibleHilbert.orElim hAtoD hDtoD hAD;

/-- Bridge lemma for the `(→R)` rule: from `(A ⋏ C) 🡒 (B ⋎ D)` conclude `C 🡒 ((A 🡒 B) ⋎ D)`. -/
lemma bridge_impR (h : ⊢ʰ (A ⋏ C) 🡒 (B ⋎ D)) : ⊢ʰ C 🡒 ((A 🡒 B) ⋎ D) := by
  have h2 : ⊢ʰ C 🡒 (A 🡒 (B ⋎ D)) := mdp imp_swap (mdp imp_uncurry_and h);
  exact impTrans h2 imp_push_disj;

/-- Necessitation is monotone over implication: `A 🡒 B` yields `□A 🡒 □B`. -/
lemma boxImp (h : ⊢ʰ A 🡒 B) : ⊢ʰ □A 🡒 □B := mdp modalK (nec h)

/-- `□` collects binary conjunctions: `□A ⋏ □B` derives `□(A ⋏ B)`. -/
lemma imp_box_and : ⊢ʰ (□A ⋏ □B) 🡒 □(A ⋏ B) := by
  have h3 : ⊢ʰ □A 🡒 (□B 🡒 □(A ⋏ B)) := impTrans (boxImp andIntro) modalK;
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hmem : ({□A ⋏ □B}) ⊢ʰ □A ⋏ □B := DeducibleHilbert.ofContext (by grind);
  have hA : ({□A ⋏ □B}) ⊢ʰ □A := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hmem;
  have hB : ({□A ⋏ □B}) ⊢ʰ □B := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem;
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h3) hA) hB;

/-- `□` collects a finset conjunction: `⋀(Δ.box)` derives `□(⋀Δ)` (analogue of `collect_box_conj`). -/
lemma imp_conj_box [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ ⋀(Δ.box) 🡒 □(⋀Δ) := by
  induction Δ using Finset.induction with
  | empty => simp only [FormulaFinset.box, Finset.image_empty, FormulaFinset.conj_empty]; exact af (nec top);
  | insert A Δ' _ ih =>
    rw [show FormulaFinset.box (insert A Δ') = insert (□A) (FormulaFinset.box Δ') from Finset.image_insert ..];
    refine impTrans imp_insert_fconj ?_;
    exact impTrans (ctxAndIntroRule andL (impTrans andR ih)) (impTrans imp_box_and (boxImp imp_fconj_insert));

theorem of_provableGentzen [DecidableEq α] {S : Sequent α} : ⊢ᵍ S → ⊢ʰ (⋀S.ant) 🡒 (⋁S.suc) := by
  intro h;
  induction h with
  | axm A => simp;
  | botL => simp;
  | wkL _ hΓ ih =>
    exact ProvableHilbert.impTrans (imp_fconj_fconj_of_subset (by grind)) ih;
  | wkR _ hΔ ih =>
    exact ProvableHilbert.impTrans ih (imp_fdisj_fdisj_of_subset (by grind));
  | impL h₁ h₂ ih₁ ih₂ =>
    -- ih₁ : ⊢ʰ ⋀Γ 🡒 ⋁insert A Δ,  ih₂ : ⊢ʰ ⋀insert B Γ 🡒 ⋁Δ
    -- goal : ⊢ʰ ⋀insert (A 🡒 B) Γ 🡒 ⋁Δ
    have e₁ := impTrans ih₁ imp_fdisj_insert;
    have e₂ := impTrans imp_fconj_insert ih₂;
    exact impTrans imp_insert_fconj (bridge_impL e₁ e₂);
  | impR h ih =>
    -- ih : ⊢ʰ ⋀insert A Γ 🡒 ⋁insert B Δ
    -- goal : ⊢ʰ ⋀Γ 🡒 ⋁insert (A 🡒 B) Δ
    have e := impTrans imp_fconj_insert (impTrans ih imp_fdisj_insert);
    exact impTrans (bridge_impR e) imp_insert_fdisj;
  | @boxGL Γ A h ih =>
    -- ih : ⊢ʰ ⋀insert (□A) (Γ ∪ Γ.box) 🡒 A,  goal : ⊢ʰ ⋀Γ.box 🡒 □A
    simp_all;
    -- `P := ⋀(Γ ∪ Γ.box)`
    have ih' : ⊢ʰ (□A ⋏ ⋀(Γ ∪ Γ.box)) 🡒 A := impTrans imp_fconj_insert ih;
    have step2 : ⊢ʰ ⋀(Γ ∪ Γ.box) 🡒 (□A 🡒 A) := mdp imp_swap (mdp imp_uncurry_and ih');
    have step4 : ⊢ʰ □(⋀(Γ ∪ Γ.box)) 🡒 □A := impTrans (boxImp step2) modalL;
    have step5 : ⊢ʰ ⋀Γ.box 🡒 ⋀((Γ ∪ Γ.box).box) := by
      apply imp_fconj_of_forall;
      intro F hF;
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hF;
      rcases Finset.mem_union.mp hE with hEΓ | hEbox;
      · exact imp_fconj_of_mem (Finset.mem_image.mpr ⟨E, hEΓ, rfl⟩);
      · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hEbox;
        exact impTrans (imp_fconj_of_mem (Finset.mem_image.mpr ⟨C, hC, rfl⟩)) modal4;
    exact impTrans (impTrans step5 imp_conj_box) step4;

theorem of_provableGentzen_singleton [DecidableEq α] : ⊢ᵍ (∅ ⟹ {A}) → ⊢ʰ A := by
  intro h;
  simpa using mdp (of_provableGentzen h) (by simp);


namespace Kripke

theorem soundness [DecidableEq α] (h : ⊢ʰ A) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGL] → M ⊧ A := by
  intro κ _ M _ x;
  have := ProvableGentzen.of_provableHilbert h;
  have := ProvableGentzen.Kripke.soundness this M x;
  exact x.forces_singleton_sequent.mp this;

theorem finite_soundness [DecidableEq α] (h : ⊢ʰ A) : ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A := by
  intro κ _ _ _;
  apply soundness h;

theorem completeness [DecidableEq α] (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A): ⊢ʰ A := by
  apply of_provableGentzen_singleton;
  apply ProvableGentzen.Kripke.completeness;
  intro κ _ M _ x;
  apply x.forces_singleton_sequent.mpr
  apply h;

end Kripke

/-- `⋀Γ ⋏ ⋀Δ` derives `⋀(Γ ∪ Δ)`. -/
@[grind <=]
lemma imp_fconj_union [DecidableEq α] (Γ Δ : FormulaFinset α) : ⊢ʰ ((⋀Γ) ⋏ (⋀Δ)) 🡒 ⋀(Γ ∪ Δ) := by
  apply Kripke.completeness
  intro κ _ M _ x
  grind


end ProvableHilbert

/-- Hilbert provability is preserved under renaming of atoms. -/
lemma ProvableHilbert.map {β : Type*} (f : α → β) {A : Formula α} (h : ⊢ʰ A) : ⊢ʰ (A.map f) := by
  induction h using ProvableHilbert.rec with
  | implyK => exact ProvableHilbert.implyK
  | implyS => exact ProvableHilbert.implyS
  | dne => exact ProvableHilbert.dne
  | andElimL => exact ProvableHilbert.andElimL
  | andElimR => exact ProvableHilbert.andElimR
  | andIntro => exact ProvableHilbert.andIntro
  | orIntroL => exact ProvableHilbert.orIntroL
  | orIntroR => exact ProvableHilbert.orIntroR
  | orElim => exact ProvableHilbert.orElim
  | modalK => exact ProvableHilbert.modalK
  | modal4 => exact ProvableHilbert.modal4
  | modalL => exact ProvableHilbert.modalL
  | mdp h₁ h₂ ih₁ ih₂ => exact ProvableHilbert.mdp ih₁ ih₂
  | nec h ih => exact ProvableHilbert.nec ih

end
