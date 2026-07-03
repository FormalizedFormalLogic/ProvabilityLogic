module

public import SeqPL.Gentzen.WithCut

@[expose]
public section

universe u
variable {α : Type u}

inductive ProofHilbert : Formula α → Type u
| prop1  {A B}   : ProofHilbert $ A 🡒 B 🡒 A
| prop2  {A B C} : ProofHilbert $ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)
| prop3  {A B}   : ProofHilbert $ (∼A 🡒 ∼B) 🡒 (B 🡒 A)
| modalK {A B}   : ProofHilbert $ □(A 🡒 B) 🡒 (□A 🡒 □B)
| modal4 {A}     : ProofHilbert $ □A 🡒 □□A
| modalL {A}     : ProofHilbert $ □(□A 🡒 A) 🡒 □A
| mdp    {A B}   : ProofHilbert (A 🡒 B) → ProofHilbert A → ProofHilbert B
| nec    {A}     : ProofHilbert A → ProofHilbert (□A)
prefix:50 "⊢ʰ! " => ProofHilbert

abbrev ProvableHilbert (A : Formula α) := Nonempty (⊢ʰ! A)
prefix:50 "⊢ʰ " => ProvableHilbert


namespace ProvableHilbert

variable {A B C : Formula α}

@[grind <=] lemma nec : ⊢ʰ A → ⊢ʰ □A := λ ⟨h⟩ => ⟨ProofHilbert.nec h⟩
@[grind =>] lemma mdp : ⊢ʰ (A 🡒 B) → ⊢ʰ A → ⊢ʰ B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[simp, grind .] lemma prop1 : ⊢ʰ A 🡒 B 🡒 A := ⟨ProofHilbert.prop1⟩
@[simp, grind .] lemma prop2 : ⊢ʰ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofHilbert.prop2⟩
@[simp, grind .] lemma prop3 : ⊢ʰ (∼A 🡒 ∼B) 🡒 (B 🡒 A) := ⟨ProofHilbert.prop3⟩
@[simp, grind .] lemma modalK : ⊢ʰ □(A 🡒 B) 🡒 (□A 🡒 □B) := ⟨ProofHilbert.modalK⟩
@[simp, grind .] lemma modal4 : ⊢ʰ □A 🡒 □□A := ⟨ProofHilbert.modal4⟩
@[simp, grind .] lemma modalL : ⊢ʰ □(□A 🡒 A) 🡒 □A := ⟨ProofHilbert.modalL⟩
@[grind <=] lemma af :  ⊢ʰ A → ⊢ʰ B 🡒 A := λ h => mdp prop1 h

@[simp, grind .]
lemma impId : ⊢ʰ A 🡒 A := mdp (mdp (prop2 (B := A 🡒 A)) prop1) prop1

@[induction_eliminator]
lemma rec
  {motive : (A : Formula α) → ⊢ʰ A → Prop}
  (prop1  : ∀ {A B} (h : ⊢ʰ A 🡒 B 🡒 A), motive _ h)
  (prop2  : ∀ {A B C} (h : ⊢ʰ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)), motive _ h)
  (prop3  : ∀ {A B} (h : ⊢ʰ (∼A 🡒 ∼B) 🡒 (B 🡒 A)), motive _ h)
  (modalK : ∀ {A B} (h : ⊢ʰ □(A 🡒 B) 🡒 (□A 🡒 □B)), motive _ h)
  (modal4 : ∀ {A} (h : ⊢ʰ □A 🡒 □□A), motive _ h)
  (modalL : ∀ {A} (h : ⊢ʰ □(□A 🡒 A) 🡒 □A), motive _ h)
  (mdp    : ∀ {A B} (h₁ : ⊢ʰ A 🡒 B) (h₂ : ⊢ʰ A), motive _ h₁ → motive _ h₂ → motive _ (mdp h₁ h₂))
  (nec    : ∀ {A} (h : ⊢ʰ A), motive A h → motive _ (nec h))
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

variable {X Y : FormulaSet α} {A B : Formula α}

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

end DeducibleHilbert




namespace ProvableGentzen

theorem of_provableHilbert [DecidableEq α] : ⊢ʰ A → ⊢ᵍ (∅ ⟹ {A} : Sequent α) := by
  intro h;
  induction h with
  | prop1 => exact .axiomŁ1;
  | prop2 => exact .axiomŁ2;
  | prop3 => exact .axiomŁ3;
  | modalK => exact .axiomK;
  | modal4 => exact .axiom4;
  | modalL => exact .axiomL;
  | nec _ h => exact .ruleNec h;
  | mdp _ _ ih₁ ih₂ => exact .mdp ih₁ ih₂;

end ProvableGentzen


namespace ProvableHilbert

variable {A B C G : Formula α}

@[simp, grind .] lemma top : ⊢ʰ (⊤ : Formula α) := by simp [Formula.top];

lemma impTrans : ⊢ʰ A 🡒 B → ⊢ʰ B 🡒 C → ⊢ʰ A 🡒 C := by
  intro h₁ h₂;
  replace h₁ := DeducibleHilbert.iff_singleton_deducible_provable.mpr h₁;
  replace h₂ : {A} ⊢ʰ B 🡒 C := DeducibleHilbert.ofProvable h₂;
  exact DeducibleHilbert.iff_singleton_deducible_provable.mp $ DeducibleHilbert.mdp h₂ h₁;

@[simp, grind .] lemma efq : ⊢ʰ ⊥ 🡒 A := mdp prop3 (af top)
@[grind <=] lemma efqRule : ⊢ʰ (⊥ : Formula α) → ⊢ʰ A := mdp efq

@[simp, grind .]
lemma andL : ⊢ʰ (A ⋏ B) 🡒 A := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  rw [Formula.and]
  sorry;

@[simp, grind .]
lemma andR : ⊢ʰ (A ⋏ B) 🡒 B := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  rw [Formula.and];
  sorry;

@[grind =>] lemma andLRule : ⊢ʰ (A ⋏ B) → ⊢ʰ A := mdp andL
@[grind =>] lemma andRRule : ⊢ʰ (A ⋏ B) → ⊢ʰ B := mdp andR



@[simp, grind .]
lemma orL : ⊢ʰ A 🡒 (A ⋎ B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;

  have h₁ : {∼A, A} ⊢ʰ ∼A := DeducibleHilbert.ofContext (by grind);
  have h₂ : {∼A, A} ⊢ʰ A := DeducibleHilbert.ofContext (by grind);
  have h₃ : {∼A, A} ⊢ʰ ⊥ 🡒 B := DeducibleHilbert.ofProvable efq;
  have : {∼A, A} ⊢ʰ ⊥ := DeducibleHilbert.mdp h₁ h₂;
  exact DeducibleHilbert.mdp h₃ this;

@[simp, grind .]
lemma orR : ⊢ʰ B 🡒 (A ⋎ B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp
  rw [show {∼A, B} = {B, ∼A} by grind];
  apply DeducibleHilbert.deduction_theorem.mpr;
  apply DeducibleHilbert.ofProvable;
  exact impId;

@[grind =>] lemma orLRule : ⊢ʰ A → ⊢ʰ (A ⋎ B) := mdp orL
@[grind =>] lemma orRRule : ⊢ʰ B → ⊢ʰ (A ⋎ B) := mdp orR

attribute [grind <=] DeducibleHilbert.ofContext
attribute [grind =>] DeducibleHilbert.mdp

lemma mdp₂ : ⊢ʰ A 🡒 B 🡒 C → ⊢ʰ A → ⊢ʰ B → ⊢ʰ C := λ h₁ h₂ h₃ => mdp (mdp h₁ h₂) h₃

@[simp, grind .]
lemma andIntro : ⊢ʰ A 🡒 B 🡒 (A ⋏ B) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have h₁ : {A 🡒 ∼B, B, A} ⊢ʰ A 🡒 (∼B) := by grind;
  have h₂ : {A 🡒 ∼B, B, A} ⊢ʰ A := by grind;
  have h₃ : {A 🡒 ∼B, B, A} ⊢ʰ B := by grind;
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp h₁ h₂) h₃;

@[grind <=]
lemma andIntroRule : ⊢ʰ A → ⊢ʰ B → ⊢ʰ (A ⋏ B) := mdp₂ andIntro

@[simp, grind .]
lemma ctxAndIntro : ⊢ʰ (G 🡒 A) 🡒 (G 🡒 B) 🡒 (G 🡒 (A ⋏ B)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have h₁ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ʰ A 🡒 (∼B) := by grind;
  have h₂ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ʰ G 🡒 A := by grind;
  have h₃ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ʰ G 🡒 B := by grind;
  have h₄ : {A 🡒 ∼B, G, G 🡒 B, G 🡒 A} ⊢ʰ G := by grind;
  grind;

lemma ctxAndIntroRule : ⊢ʰ (G 🡒 A) → ⊢ʰ (G 🡒 B) → ⊢ʰ (G 🡒 (A ⋏ B)) := mdp₂ ctxAndIntro


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
lemma imp_reassoc {A B C D : Formula α} : ⊢ʰ ((A ⋏ B) 🡒 (C 🡒 D)) 🡒 ((A ⋏ C) 🡒 (B 🡒 D)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hAC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ A ⋏ C := DeducibleHilbert.ofContext (by grind)
  have hA : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andL) hAC
  have hC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andR) hAC
  have hB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)} : FormulaSet α) ⊢ʰ (A ⋏ B) 🡒 (C 🡒 D) :=
    DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hAB) hC

/-- Elimination of a conjunction: `(A ⋏ B) 🡒 C` derives `A 🡒 (B 🡒 C)`. -/
@[simp, grind .]
lemma imp_uncurry_and {A B C : Formula α} : ⊢ʰ ((A ⋏ B) 🡒 C) 🡒 (A 🡒 (B 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind)
  have hB : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A, (A ⋏ B) 🡒 C} : FormulaSet α) ⊢ʰ (A ⋏ B) 🡒 C := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp himp hAB

/-- Swapping antecedents: `A 🡒 (B 🡒 C)` derives `B 🡒 (A 🡒 C)`. -/
@[simp, grind .]
lemma imp_swap {A B C : Formula α} : ⊢ʰ (A 🡒 (B 🡒 C)) 🡒 (B 🡒 (A 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({A, B, A 🡒 (B 🡒 C)} : FormulaSet α) ⊢ʰ A := DeducibleHilbert.ofContext (by grind)
  have hB : ({A, B, A 🡒 (B 🡒 C)} : FormulaSet α) ⊢ʰ B := DeducibleHilbert.ofContext (by grind)
  have himp : ({A, B, A 🡒 (B 🡒 C)} : FormulaSet α) ⊢ʰ A 🡒 (B 🡒 C) := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hA) hB


lemma imp_ldisj_of_mem {Γ : FormulaList α} {A : Formula α} (h : A ∈ Γ) : ⊢ʰ A 🡒 ⋁Γ := by
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
    sorry;

@[grind <=]
lemma imp_fdisj_fdisj_of_subset {Γ Γ' : FormulaFinset α} (h : Γ ⊆ Γ') : ⊢ʰ ⋁Γ 🡒 ⋁Γ' := by
  apply imp_ldisj_ldisj_of_subset;
  intro A;
  simpa using @h A;

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
    simp_all;
    sorry;
  | impR h ih =>
    simp_all;
    sorry;
  | boxGL h ih =>
    simp_all;
    sorry;

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

end
