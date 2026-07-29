module

public import ProvabilityLogic.Gentzen.Grz.WithCut

@[expose]
public section

variable {α : Type u}

namespace LogicGrz

open LogicGL

/--
Hilbert-style proof system for `Grz`, over a `Minimal + DNE` propositional base, mirroring
`LogicGL.ProofHilbert`.

Besides the shared propositional primitives, four modal axioms are needed: `modalK`, `modal4`,
`modalT`, and `modalGrz`. Note that `modalT` (`□A 🡒 A`) is genuinely independent from the other
three here — the Avron-form Grz axiom `□(□(A 🡒 □A) 🡒 A) 🡒 □A` alone is already valid in `GL`
(which lacks `T`), so `K + 4 + Grz` is not enough to derive reflexivity.
- [SS21, §2]
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
| modalT   {A}     : ProofHilbert $ □A 🡒 A
| modalGrz {A}     : ProofHilbert $ □(□(A 🡒 □A) 🡒 A) 🡒 □A
| mdp      {A B}   : ProofHilbert (A 🡒 B) → ProofHilbert A → ProofHilbert B
| nec      {A}     : ProofHilbert A → ProofHilbert (□A)
notation:50 "⊢ʰ[Grz]! " A:51 => ProofHilbert A

abbrev ProvableHilbert (A : Formula α) := Nonempty (⊢ʰ[Grz]! A)
notation:50 "⊢ʰ[Grz] " A:51 => ProvableHilbert A


namespace ProvableHilbert

variable {A B C : Formula α}

@[grind <=] lemma nec : ⊢ʰ[Grz] A → ⊢ʰ[Grz] □A := λ ⟨h⟩ => ⟨ProofHilbert.nec h⟩
@[grind =>] lemma mdp : ⊢ʰ[Grz] (A 🡒 B) → ⊢ʰ[Grz] A → ⊢ʰ[Grz] B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofHilbert.mdp h₁ h₂⟩
@[simp, grind .] lemma implyK : ⊢ʰ[Grz] A 🡒 B 🡒 A := ⟨ProofHilbert.implyK⟩
@[simp, grind .] lemma implyS : ⊢ʰ[Grz] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := ⟨ProofHilbert.implyS⟩
@[simp, grind .] lemma dne : ⊢ʰ[Grz] ∼∼A 🡒 A := ⟨ProofHilbert.dne⟩
@[simp, grind .] lemma andElimL : ⊢ʰ[Grz] (A ⋏ B) 🡒 A := ⟨ProofHilbert.andElimL⟩
@[simp, grind .] lemma andElimR : ⊢ʰ[Grz] (A ⋏ B) 🡒 B := ⟨ProofHilbert.andElimR⟩
@[simp, grind .] lemma andIntro : ⊢ʰ[Grz] A 🡒 B 🡒 (A ⋏ B) := ⟨ProofHilbert.andIntro⟩
@[simp, grind .] lemma orIntroL : ⊢ʰ[Grz] A 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroL⟩
@[simp, grind .] lemma orIntroR : ⊢ʰ[Grz] B 🡒 (A ⋎ B) := ⟨ProofHilbert.orIntroR⟩
@[simp, grind .] lemma orElim : ⊢ʰ[Grz] (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C) := ⟨ProofHilbert.orElim⟩
@[simp, grind .] lemma modalK : ⊢ʰ[Grz] □(A 🡒 B) 🡒 (□A 🡒 □B) := ⟨ProofHilbert.modalK⟩
@[simp, grind .] lemma modal4 : ⊢ʰ[Grz] □A 🡒 □□A := ⟨ProofHilbert.modal4⟩
@[simp, grind .] lemma modalT : ⊢ʰ[Grz] □A 🡒 A := ⟨ProofHilbert.modalT⟩
@[simp, grind .] lemma modalGrz : ⊢ʰ[Grz] □(□(A 🡒 □A) 🡒 A) 🡒 □A := ⟨ProofHilbert.modalGrz⟩

/-- Compatibility alias for the Łukasiewicz-style axiom `implyK`. -/
@[simp, grind .] lemma prop1 : ⊢ʰ[Grz] A 🡒 B 🡒 A := implyK
/-- Compatibility alias for the Łukasiewicz-style axiom `implyS`. -/
@[simp, grind .] lemma prop2 : ⊢ʰ[Grz] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C) := implyS

@[grind <=] lemma af : ⊢ʰ[Grz] A → ⊢ʰ[Grz] B 🡒 A := λ h => mdp implyK h

@[simp, grind .]
lemma impId : ⊢ʰ[Grz] A 🡒 A := mdp (mdp (implyS (B := A 🡒 A)) implyK) implyK

set_option linter.unusedVariables false in
@[induction_eliminator]
lemma rec
  {motive : (A : Formula α) → ⊢ʰ[Grz] A → Prop}
  (implyK   : ∀ {A B} (h : ⊢ʰ[Grz] A 🡒 B 🡒 A), motive _ h)
  (implyS   : ∀ {A B C} (h : ⊢ʰ[Grz] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 (A 🡒 C)), motive _ h)
  (dne      : ∀ {A} (h : ⊢ʰ[Grz] ∼∼A 🡒 A), motive _ h)
  (andElimL : ∀ {A B} (h : ⊢ʰ[Grz] (A ⋏ B) 🡒 A), motive _ h)
  (andElimR : ∀ {A B} (h : ⊢ʰ[Grz] (A ⋏ B) 🡒 B), motive _ h)
  (andIntro : ∀ {A B} (h : ⊢ʰ[Grz] A 🡒 B 🡒 (A ⋏ B)), motive _ h)
  (orIntroL : ∀ {A B} (h : ⊢ʰ[Grz] A 🡒 (A ⋎ B)), motive _ h)
  (orIntroR : ∀ {A B} (h : ⊢ʰ[Grz] B 🡒 (A ⋎ B)), motive _ h)
  (orElim   : ∀ {A B C} (h : ⊢ʰ[Grz] (A 🡒 C) 🡒 (B 🡒 C) 🡒 ((A ⋎ B) 🡒 C)), motive _ h)
  (modalK   : ∀ {A B} (h : ⊢ʰ[Grz] □(A 🡒 B) 🡒 (□A 🡒 □B)), motive _ h)
  (modal4   : ∀ {A} (h : ⊢ʰ[Grz] □A 🡒 □□A), motive _ h)
  (modalT   : ∀ {A} (h : ⊢ʰ[Grz] □A 🡒 A), motive _ h)
  (modalGrz : ∀ {A} (h : ⊢ʰ[Grz] □(□(A 🡒 □A) 🡒 A) 🡒 □A), motive _ h)
  (mdp      : ∀ {A B} (h₁ : ⊢ʰ[Grz] A 🡒 B) (h₂ : ⊢ʰ[Grz] A), motive _ h₁ → motive _ h₂ → motive _ (mdp h₁ h₂))
  (nec      : ∀ {A} (h : ⊢ʰ[Grz] A), motive A h → motive _ (nec h))
  : ∀ {A} (h : ⊢ʰ[Grz] A), motive _ h := by
  rintro A ⟨h⟩;
  induction h <;> grind;

end ProvableHilbert


inductive DeductionHilbert : FormulaSet α → Formula α → Type _
| ofProof {X A} : ⊢ʰ[Grz]! A → DeductionHilbert X A
| ofContext {X A} : A ∈ X → DeductionHilbert X A
| mdp {X A B} : (DeductionHilbert X (A 🡒 B)) → (DeductionHilbert X A) → (DeductionHilbert X B)
notation:50 X:51 " ⊢ʰ[Grz]! " A:51 => DeductionHilbert X A

abbrev DeducibleHilbert (X : FormulaSet α) (A : Formula α) := Nonempty (X ⊢ʰ[Grz]! A)
notation:50 X:51 " ⊢ʰ[Grz] " A:51 => DeducibleHilbert X A

namespace DeducibleHilbert

variable {X Y : FormulaSet α} {A B C : Formula α}

@[grind <=] lemma ofProvable : (⊢ʰ[Grz] A) → (X ⊢ʰ[Grz] A) := λ ⟨h⟩ => ⟨.ofProof h⟩
@[grind <=] lemma ofContext : A ∈ X → (X ⊢ʰ[Grz] A) := λ h => ⟨.ofContext h⟩
@[grind =>] lemma mdp : X ⊢ʰ[Grz] A 🡒 B → X ⊢ʰ[Grz] A → X ⊢ʰ[Grz] B := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨.mdp h₁ h₂⟩

@[induction_eliminator]
protected lemma rec
  {motive : (X : FormulaSet α) → (A : Formula α) → (X ⊢ʰ[Grz] A) → Prop}
  (ofProvable : ∀ {X A}, (h : ⊢ʰ[Grz] A) → motive X A (ofProvable h))
  (ofContext : ∀ {X A}, (h : A ∈ X) → motive X A (ofContext h))
  (mdp : ∀ {X A B}, (hAB : X ⊢ʰ[Grz] A 🡒 B) → (hA : X ⊢ʰ[Grz] A) → (motive X (A 🡒 B) hAB) → (motive X A hA) → (motive X B (mdp hAB hA)))
  : ∀ {X A}, (h : X ⊢ʰ[Grz] A) → motive X A h := by
  rintro X A ⟨h⟩;
  induction h with
  | ofProof h => apply ofProvable ⟨h⟩;
  | _ => grind;

lemma of_subset_ctx (hXY : X ⊆ Y) : (X ⊢ʰ[Grz] A) → (Y ⊢ʰ[Grz] A) := λ h => by induction h <;> grind;

lemma to_ctx : (X ⊢ʰ[Grz] A 🡒 B) → (insert A X ⊢ʰ[Grz] B) := λ h => by
  apply mdp;
  . show insert A X ⊢ʰ[Grz] A 🡒 B;
    exact of_subset_ctx (by simp) h;
  . exact ofContext (by simp);

lemma drop_ctx (h : insert A X ⊢ʰ[Grz] B) : (X ⊢ʰ[Grz] A 🡒 B) := by
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

theorem deduction_theorem : (insert A X ⊢ʰ[Grz] B) ↔ (X ⊢ʰ[Grz] A 🡒 B) := ⟨drop_ctx, to_ctx⟩

lemma iff_empty_ctx : (∅ ⊢ʰ[Grz] A) ↔ (⊢ʰ[Grz] A) := by
  constructor
  . intro h;
    generalize e : (∅ : FormulaSet α) = X at h;
    induction h <;> grind;
  . apply ofProvable;

lemma iff_singleton_deducible_provable : ({A} ⊢ʰ[Grz] B) ↔ (⊢ʰ[Grz] A 🡒 B) := by
  rw [show ({A} : FormulaSet α) = insert A ∅ by simp];
  apply Iff.trans deduction_theorem iff_empty_ctx;

/-- Context-level transitivity of implication. -/
lemma impTrans (p : X ⊢ʰ[Grz] A 🡒 B) (q : X ⊢ʰ[Grz] B 🡒 C) : X ⊢ʰ[Grz] A 🡒 C :=
  mdp (mdp (ofProvable ProvableHilbert.prop2) (mdp (ofProvable ProvableHilbert.prop1) q)) p

end DeducibleHilbert


namespace ProvableGentzen

variable {A : Formula α}

/-- Every Hilbert-provable `Grz` formula is Gentzen-provable as a singleton sequent, by
induction on the Hilbert derivation, translating each axiom/rule to its `LogicGrz.ProofGentzen`
counterpart. -/
theorem of_provableHilbert [DecidableEq α] : ⊢ʰ[Grz] A → ⊢ᵍ[Grz] (∅ ⟹ {A} : Sequent α) := by
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
  | modalT => exact .modalT;
  | modalGrz => exact .modalGrz;
  | nec _ h => exact .nec h;
  | mdp _ _ ih₁ ih₂ => exact .mdp ih₁ ih₂;

end ProvableGentzen


namespace ProvableHilbert

variable {A B C D : Formula α}

@[simp, grind .] lemma top : ⊢ʰ[Grz] (⊤ : Formula α) := by simp [Formula.top];

lemma impTrans : ⊢ʰ[Grz] A 🡒 B → ⊢ʰ[Grz] B 🡒 C → ⊢ʰ[Grz] A 🡒 C := by
  intro h₁ h₂;
  replace h₁ := DeducibleHilbert.iff_singleton_deducible_provable.mpr h₁;
  replace h₂ : {A} ⊢ʰ[Grz] B 🡒 C := DeducibleHilbert.ofProvable h₂;
  exact DeducibleHilbert.iff_singleton_deducible_provable.mp $ DeducibleHilbert.mdp h₂ h₁;

/-- Double negation introduction: `A 🡒 ∼∼A`. -/
@[grind =>] lemma dni : ⊢ʰ[Grz] A 🡒 ∼∼A := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼A, A}`, goal `⊥`
  have hA  : ({∼A, A}) ⊢ʰ[Grz] A     := DeducibleHilbert.ofContext (by grind);
  have hnA : ({∼A, A}) ⊢ʰ[Grz] A 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnA hA;

/-- The Łukasiewicz-style contraposition axiom: `(∼A 🡒 ∼B) 🡒 (B 🡒 A)`. -/
@[simp, grind .] lemma elimContra : ⊢ʰ[Grz] (∼A 🡒 ∼B) 🡒 (B 🡒 A) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{B, ∼A 🡒 ∼B}`, goal `A`
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  -- goal `∼∼A`, i.e. `∼A 🡒 ⊥`
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼A, B, ∼A 🡒 ∼B}`, goal `⊥`
  have hnA  : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ[Grz] ∼A      := DeducibleHilbert.ofContext (by grind);
  have himp : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ[Grz] ∼A 🡒 ∼B := DeducibleHilbert.ofContext (by grind);
  have hnB  : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ[Grz] ∼B      := DeducibleHilbert.mdp himp hnA;
  have hB   : ({∼A, B, ∼A 🡒 ∼B}) ⊢ʰ[Grz] B       := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnB hB;

@[simp, grind .] lemma efq : ⊢ʰ[Grz] ⊥ 🡒 A := mdp elimContra (af top)
@[grind <=] lemma efqRule : ⊢ʰ[Grz] (⊥ : Formula α) → ⊢ʰ[Grz] A := mdp efq

/-- Left conjunction elimination (alias for the primitive `andElimL`). -/
@[simp, grind .] lemma andL : ⊢ʰ[Grz] (A ⋏ B) 🡒 A := andElimL
/-- Right conjunction elimination (alias for the primitive `andElimR`). -/
@[simp, grind .] lemma andR : ⊢ʰ[Grz] (A ⋏ B) 🡒 B := andElimR

@[grind =>] lemma andLRule : ⊢ʰ[Grz] (A ⋏ B) → ⊢ʰ[Grz] A := mdp andL
@[grind =>] lemma andRRule : ⊢ʰ[Grz] (A ⋏ B) → ⊢ʰ[Grz] B := mdp andR

/-- Left disjunction introduction (alias for the primitive `orIntroL`). -/
@[simp, grind .] lemma orL : ⊢ʰ[Grz] A 🡒 (A ⋎ B) := orIntroL
/-- Right disjunction introduction (alias for the primitive `orIntroR`). -/
@[simp, grind .] lemma orR : ⊢ʰ[Grz] B 🡒 (A ⋎ B) := orIntroR

@[grind =>] lemma orLRule : ⊢ʰ[Grz] A → ⊢ʰ[Grz] (A ⋎ B) := mdp orL
@[grind =>] lemma orRRule : ⊢ʰ[Grz] B → ⊢ʰ[Grz] (A ⋎ B) := mdp orR

attribute [grind <=] DeducibleHilbert.ofContext
attribute [grind =>] DeducibleHilbert.mdp

lemma mdp₂ : ⊢ʰ[Grz] A 🡒 B 🡒 C → ⊢ʰ[Grz] A → ⊢ʰ[Grz] B → ⊢ʰ[Grz] C := λ h₁ h₂ h₃ => mdp (mdp h₁ h₂) h₃

@[grind <=]
lemma andIntroRule : ⊢ʰ[Grz] A → ⊢ʰ[Grz] B → ⊢ʰ[Grz] (A ⋏ B) := mdp₂ andIntro

@[simp, grind .]
lemma ctxAndIntro : ⊢ʰ[Grz] (A 🡒 B) 🡒 (A 🡒 C) 🡒 (A 🡒 (B ⋏ C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  have h₁ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ[Grz] B 🡒 (∼C) := by grind;
  have h₂ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ[Grz] A 🡒 B := by grind;
  have h₃ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ[Grz] A 🡒 C := by grind;
  have h₄ : {B 🡒 ∼C, A, A 🡒 C, A 🡒 B} ⊢ʰ[Grz] A := by grind;
  grind;

lemma ctxAndIntroRule : ⊢ʰ[Grz] (A 🡒 B) → ⊢ʰ[Grz] (A 🡒 C) → ⊢ʰ[Grz] (A 🡒 (B ⋏ C)) := mdp₂ ctxAndIntro


lemma imp_lconj_of_mem {Γ : FormulaList α} (h : A ∈ Γ) : ⊢ʰ[Grz] ⋀Γ 🡒 A := by
  match Γ with
  | [] | [B] => simp_all;
  | B :: C :: Γ =>
    simp only [List.mem_cons] at h;
    rcases h with (rfl | rfl | h);
    . simp [FormulaList.conj];
    . exact impTrans andR $ imp_lconj_of_mem (Γ := A :: Γ) (by simp);
    . exact impTrans andR $ imp_lconj_of_mem (Γ := C :: Γ) (by grind);


lemma imp_lconj_lconj_of_subset {Γ Γ' : FormulaList α} (h : Γ' ⊆ Γ) : ⊢ʰ[Grz] ⋀Γ 🡒 ⋀Γ' := by
  match Γ' with
  | [] => apply af; simp;
  | [B] => apply imp_lconj_of_mem; grind;
  | B :: C :: Γ' =>
    have h₁ := imp_lconj_of_mem (Γ := Γ) (A := B) (by grind);
    have h₂ := imp_lconj_lconj_of_subset (Γ := Γ) (Γ' := C :: Γ') (by grind);
    exact ctxAndIntroRule h₁ h₂;

@[grind <=]
lemma imp_fconj_fconj_of_subset {Γ Γ' : FormulaFinset α} (h : Γ' ⊆ Γ) : ⊢ʰ[Grz] ⋀Γ 🡒 ⋀Γ' := by
  apply imp_lconj_lconj_of_subset;
  intro A;
  simpa using @h A;

/-- Combinatory reassociation of a conjunction: `(A ⋏ B) 🡒 (C 🡒 D)` derives `(A ⋏ C) 🡒 (B 🡒 D)`. -/
@[simp, grind .]
lemma imp_reassoc : ⊢ʰ[Grz] ((A ⋏ B) 🡒 (C 🡒 D)) 🡒 ((A ⋏ C) 🡒 (B 🡒 D)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hAC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ[Grz] A ⋏ C := DeducibleHilbert.ofContext (by grind)
  have hA : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ[Grz] A :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andL) hAC
  have hC : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ[Grz] C :=
    DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andR) hAC
  have hB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ[Grz] B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ[Grz] A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A ⋏ C, (A ⋏ B) 🡒 (C 🡒 D)}) ⊢ʰ[Grz] (A ⋏ B) 🡒 (C 🡒 D) :=
    DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hAB) hC

/-- Elimination of a conjunction: `(A ⋏ B) 🡒 C` derives `A 🡒 (B 🡒 C)`. -/
@[simp, grind .]
lemma imp_uncurry_and : ⊢ʰ[Grz] ((A ⋏ B) 🡒 C) 🡒 (A 🡒 (B 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ[Grz] A := DeducibleHilbert.ofContext (by grind)
  have hB : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ[Grz] B := DeducibleHilbert.ofContext (by grind)
  have hAB : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ[Grz] A ⋏ B :=
    DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ProvableHilbert.andIntro) hA) hB
  have himp : ({B, A, (A ⋏ B) 🡒 C}) ⊢ʰ[Grz] (A ⋏ B) 🡒 C := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp himp hAB

/-- Swapping antecedents: `A 🡒 (B 🡒 C)` derives `B 🡒 (A 🡒 C)`. -/
@[simp, grind .]
lemma imp_swap : ⊢ʰ[Grz] (A 🡒 (B 🡒 C)) 🡒 (B 🡒 (A 🡒 C)) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp
  apply DeducibleHilbert.deduction_theorem.mp
  apply DeducibleHilbert.deduction_theorem.mp
  have hA : ({A, B, A 🡒 (B 🡒 C)}) ⊢ʰ[Grz] A := DeducibleHilbert.ofContext (by grind)
  have hB : ({A, B, A 🡒 (B 🡒 C)}) ⊢ʰ[Grz] B := DeducibleHilbert.ofContext (by grind)
  have himp : ({A, B, A 🡒 (B 🡒 C)}) ⊢ʰ[Grz] A 🡒 (B 🡒 C) := DeducibleHilbert.ofContext (by grind)
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp himp hA) hB


/-- Disjunction elimination (Minimal-style `orElim`), recovered classically:
from `A 🡒 C` and `B 🡒 C` derive `(A ⋎ B) 🡒 C`. -/
lemma orElim' (h₁ : ⊢ʰ[Grz] A 🡒 C) (h₂ : ⊢ʰ[Grz] B 🡒 C) : ⊢ʰ[Grz] (A ⋎ B) 🡒 C := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼C, A ⋎ B}`, goal `⊥`
  have key : ({∼C, A ⋎ B}) ⊢ʰ[Grz] A 🡒 ⊥ := by
    apply DeducibleHilbert.deduction_theorem.mp;
    -- context `{A, ∼C, A ⋎ B}`, goal `⊥`
    have hA  : ({A, ∼C, A ⋎ B}) ⊢ʰ[Grz] A     := DeducibleHilbert.ofContext (by grind);
    have hnC : ({A, ∼C, A ⋎ B}) ⊢ʰ[Grz] C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
    exact DeducibleHilbert.mdp hnC (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h₁) hA);
  have hAB : ({∼C, A ⋎ B}) ⊢ʰ[Grz] (A 🡒 ⊥) 🡒 B := DeducibleHilbert.ofContext (by grind);
  have hB  : ({∼C, A ⋎ B}) ⊢ʰ[Grz] B := DeducibleHilbert.mdp hAB key;
  have hC  : ({∼C, A ⋎ B}) ⊢ʰ[Grz] C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h₂) hB;
  have hnC : ({∼C, A ⋎ B}) ⊢ʰ[Grz] C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnC hC;

lemma imp_ldisj_of_mem {Γ : FormulaList α} (h : A ∈ Γ) : ⊢ʰ[Grz] A 🡒 ⋁Γ := by
  match Γ with
  | [] | [B] => simp_all;
  | B :: C :: Γ =>
    simp only [List.mem_cons] at h;
    rcases h with (rfl | rfl | h);
    . simp [FormulaList.disj];
    . exact impTrans (imp_ldisj_of_mem (Γ := A :: Γ) (by simp)) orR;
    . exact impTrans (imp_ldisj_of_mem (Γ := C :: Γ) (by grind)) orR;

@[grind <=]
lemma imp_ldisj_ldisj_of_subset {Γ Γ' : FormulaList α} (h : Γ ⊆ Γ') : ⊢ʰ[Grz] ⋁Γ 🡒 ⋁Γ' := by
  match Γ with
  | [] => simp;
  | [B] => apply imp_ldisj_of_mem; grind;
  | B :: C :: Γ =>
    have h₁ := imp_ldisj_of_mem (Γ := Γ') (A := B) (by grind);
    have h₂ := imp_ldisj_ldisj_of_subset (Γ := C :: Γ) (Γ' := Γ') (by grind);
    exact orElim' h₁ h₂;

@[grind <=]
lemma imp_fdisj_fdisj_of_subset {Γ Γ' : FormulaFinset α} (h : Γ ⊆ Γ') : ⊢ʰ[Grz] ⋁Γ 🡒 ⋁Γ' := by
  apply imp_ldisj_ldisj_of_subset;
  intro A;
  simpa using @h A;

/-! ### Introduction/elimination for list and finset conjunctions/disjunctions -/

/-- If `B` implies every member of `Γ`, it implies their conjunction. -/
lemma imp_lconj_of_forall {Γ : FormulaList α} (h : ∀ A ∈ Γ, ⊢ʰ[Grz] B 🡒 A) : ⊢ʰ[Grz] B 🡒 ⋀Γ := by
  match Γ with
  | [] => exact af top;
  | [C] => exact h C (by simp);
  | C :: D :: Γ =>
    exact ctxAndIntroRule (h C (by simp)) (imp_lconj_of_forall (fun A hA => h A (List.mem_cons_of_mem _ hA)));

/-- If every member of `Γ` implies `D`, their disjunction implies `D`. -/
lemma imp_ldisj_elim {Γ : FormulaList α} (h : ∀ A ∈ Γ, ⊢ʰ[Grz] A 🡒 D) : ⊢ʰ[Grz] ⋁Γ 🡒 D := by
  match Γ with
  | [] => exact (efq : ⊢ʰ[Grz] ⊥ 🡒 D);
  | [B] => exact h B (by simp);
  | B :: C :: Γ =>
    exact orElim' (h B (by simp)) (imp_ldisj_elim (fun A hA => h A (List.mem_cons_of_mem _ hA)));

lemma imp_fconj_of_mem {Δ : FormulaFinset α} (h : A ∈ Δ) : ⊢ʰ[Grz] ⋀Δ 🡒 A :=
  imp_lconj_of_mem (Finset.mem_toList.mpr h)

lemma imp_mem_fdisj {Δ : FormulaFinset α} (h : A ∈ Δ) : ⊢ʰ[Grz] A 🡒 ⋁Δ :=
  imp_ldisj_of_mem (Finset.mem_toList.mpr h)

lemma imp_fconj_of_forall {Δ : FormulaFinset α} (h : ∀ A ∈ Δ, ⊢ʰ[Grz] B 🡒 A) : ⊢ʰ[Grz] B 🡒 ⋀Δ :=
  imp_lconj_of_forall (fun A hA => h A (Finset.mem_toList.mp hA))

lemma imp_fdisj_elim {Δ : FormulaFinset α} (h : ∀ A ∈ Δ, ⊢ʰ[Grz] A 🡒 D) : ⊢ʰ[Grz] ⋁Δ 🡒 D :=
  imp_ldisj_elim (fun A hA => h A (Finset.mem_toList.mp hA))

/-- `B ⋏ ⋀Δ` implies `⋀(insert B Δ)`. -/
lemma imp_fconj_insert [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ[Grz] (B ⋏ ⋀Δ) 🡒 ⋀(insert B Δ) := by
  apply imp_fconj_of_forall;
  intro A hA;
  rcases Finset.mem_insert.mp hA with rfl | hA;
  · exact andL;
  · exact impTrans andR (imp_fconj_of_mem hA);

/-- `⋁(insert B Δ)` implies `B ⋎ ⋁Δ`. -/
lemma imp_fdisj_insert [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ[Grz] ⋁(insert B Δ) 🡒 (B ⋎ ⋁Δ) := by
  apply imp_fdisj_elim;
  intro A hA;
  rcases Finset.mem_insert.mp hA with rfl | hA;
  · exact orL;
  · exact impTrans (imp_mem_fdisj hA) orR;

/-- `B ⋎ ⋁Δ` implies `⋁(insert B Δ)`. -/
lemma imp_insert_fdisj [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ[Grz] (B ⋎ ⋁Δ) 🡒 ⋁(insert B Δ) :=
  orElim' (imp_mem_fdisj (by simp)) (imp_fdisj_fdisj_of_subset (by simp))

/-- From `∼(A 🡒 B)` we recover `A`. -/
lemma neg_imp_left : ⊢ʰ[Grz] ∼(A 🡒 B) 🡒 A := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{∼A, ∼(A 🡒 B)}`, goal `⊥`
  have hAB : ({∼A, ∼(A 🡒 B)}) ⊢ʰ[Grz] A 🡒 B := by
    apply DeducibleHilbert.deduction_theorem.mp;
    apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable efq);
    have hA  : ({A, ∼A, ∼(A 🡒 B)}) ⊢ʰ[Grz] A     := DeducibleHilbert.ofContext (by grind);
    have hnA : ({A, ∼A, ∼(A 🡒 B)}) ⊢ʰ[Grz] A 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
    exact DeducibleHilbert.mdp hnA hA;
  have hnAB : ({∼A, ∼(A 🡒 B)}) ⊢ʰ[Grz] (A 🡒 B) 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnAB hAB;

/-- From `∼(A 🡒 B)` we recover `∼B`. -/
lemma neg_imp_right : ⊢ʰ[Grz] ∼(A 🡒 B) 🡒 ∼B := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `{B, ∼(A 🡒 B)}`, goal `⊥` (since `∼B = B 🡒 ⊥`)
  have hAB : ({B, ∼(A 🡒 B)}) ⊢ʰ[Grz] A 🡒 B := by
    apply DeducibleHilbert.deduction_theorem.mp;
    exact DeducibleHilbert.ofContext (by grind);
  have hnAB : ({B, ∼(A 🡒 B)}) ⊢ʰ[Grz] (A 🡒 B) 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  exact DeducibleHilbert.mdp hnAB hAB;

/-- Context-level disjunction elimination, recovered classically via `dne`. -/
lemma _root_.LogicGrz.DeducibleHilbert.orElim {X : FormulaSet α}
    (h₁ : X ⊢ʰ[Grz] A 🡒 C) (h₂ : X ⊢ʰ[Grz] B 🡒 C) (h : X ⊢ʰ[Grz] A ⋎ B) : X ⊢ʰ[Grz] C := by
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context `insert (∼C) X`, goal `⊥`
  have hnC : (insert (∼C) X) ⊢ʰ[Grz] C 🡒 ⊥ := DeducibleHilbert.ofContext (by grind);
  have h₁' : (insert (∼C) X) ⊢ʰ[Grz] A 🡒 C := DeducibleHilbert.of_subset_ctx (by grind) h₁;
  have h₂' : (insert (∼C) X) ⊢ʰ[Grz] B 🡒 C := DeducibleHilbert.of_subset_ctx (by grind) h₂;
  have h'  : (insert (∼C) X) ⊢ʰ[Grz] (A 🡒 ⊥) 🡒 B := DeducibleHilbert.of_subset_ctx (by grind) h;
  have hnA : (insert (∼C) X) ⊢ʰ[Grz] A 🡒 ⊥ := DeducibleHilbert.impTrans h₁' hnC;
  have hB  : (insert (∼C) X) ⊢ʰ[Grz] B := DeducibleHilbert.mdp h' hnA;
  have hC  : (insert (∼C) X) ⊢ʰ[Grz] C := DeducibleHilbert.mdp h₂' hB;
  exact DeducibleHilbert.mdp hnC hC;

/-- `⋀(insert B Δ)` decomposes into `B ⋏ ⋀Δ`. -/
lemma imp_insert_fconj [DecidableEq α] {Δ : FormulaFinset α} :
    ⊢ʰ[Grz] ⋀(insert B Δ) 🡒 (B ⋏ ⋀Δ) :=
  ctxAndIntroRule (imp_fconj_of_mem (by simp)) (imp_fconj_fconj_of_subset (by simp))

/-- Classical push of an implication across a disjunction: `A 🡒 (B ⋎ D)` derives `(A 🡒 B) ⋎ D`. -/
lemma imp_push_disj : ⊢ʰ[Grz] (A 🡒 (B ⋎ D)) 🡒 ((A 🡒 B) ⋎ D) := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  -- context `{A 🡒 (B ⋎ D)}`, goal `(A 🡒 B) ⋎ D`
  apply DeducibleHilbert.mdp (DeducibleHilbert.ofProvable dne);
  apply DeducibleHilbert.deduction_theorem.mp;
  -- context now also holds `∼((A 🡒 B) ⋎ D)`, goal `⊥`
  have hn : ({∼(A 🡒 B ⋎ D), A 🡒 (B ⋎ D)}) ⊢ʰ[Grz] ((A 🡒 B) ⋎ D) 🡒 ⊥ :=
    DeducibleHilbert.ofContext (by grind);
  have hmain : ({∼(A 🡒 B ⋎ D), A 🡒 (B ⋎ D)}) ⊢ʰ[Grz] A 🡒 (B ⋎ D) :=
    DeducibleHilbert.ofContext (by grind);
  have hnAB : ({∼(A 🡒 B ⋎ D), A 🡒 (B ⋎ D)}) ⊢ʰ[Grz] (A 🡒 B) 🡒 ⊥ :=
    DeducibleHilbert.impTrans (DeducibleHilbert.ofProvable orL) hn;
  refine DeducibleHilbert.orElim (A := B) (B := D) (C := ⊥) ?_ ?_ ?_;
  · exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable neg_imp_right) hnAB;
  · exact DeducibleHilbert.impTrans (DeducibleHilbert.ofProvable orR) hn;
  · exact DeducibleHilbert.mdp hmain (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable neg_imp_left) hnAB);

/-- Bridge lemma for the `(→L)` rule: from `⋀Γ 🡒 (A ⋎ ⋁Δ)` and `(B ⋏ ⋀Γ) 🡒 ⋁Δ`
conclude `((A 🡒 B) ⋏ ⋀Γ) 🡒 ⋁Δ`. -/
lemma bridge_impL (ha : ⊢ʰ[Grz] C 🡒 (A ⋎ D)) (hb : ⊢ʰ[Grz] (B ⋏ C) 🡒 D) :
    ⊢ʰ[Grz] ((A 🡒 B) ⋏ C) 🡒 D := by
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  -- context `X = {(A 🡒 B) ⋏ C}`, goal `D`
  have hmem : ({(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] (A 🡒 B) ⋏ C := DeducibleHilbert.ofContext (by grind);
  have hC  : ({(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem;
  have hAD : ({(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] A ⋎ D := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable ha) hC;
  have hAtoD : ({(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] A 🡒 D := by
    apply DeducibleHilbert.deduction_theorem.mp;
    -- context `insert A {(A 🡒 B) ⋏ C}`, goal `D`
    have hmem' : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] (A 🡒 B) ⋏ C := DeducibleHilbert.ofContext (by grind);
    have hAB : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] A 🡒 B := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hmem';
    have hCi : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] C := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem';
    have hA  : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] A := DeducibleHilbert.ofContext (by grind);
    have hB  : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] B := DeducibleHilbert.mdp hAB hA;
    have hBC : (insert A {(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] B ⋏ C := DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andIntro) hB) hCi;
    exact DeducibleHilbert.mdp (DeducibleHilbert.ofProvable hb) hBC;
  have hDtoD : ({(A 🡒 B) ⋏ C}) ⊢ʰ[Grz] D 🡒 D := DeducibleHilbert.ofProvable impId;
  exact DeducibleHilbert.orElim hAtoD hDtoD hAD;

/-- Bridge lemma for the `(→R)` rule: from `(A ⋏ C) 🡒 (B ⋎ D)` conclude `C 🡒 ((A 🡒 B) ⋎ D)`. -/
lemma bridge_impR (h : ⊢ʰ[Grz] (A ⋏ C) 🡒 (B ⋎ D)) : ⊢ʰ[Grz] C 🡒 ((A 🡒 B) ⋎ D) := by
  have h2 : ⊢ʰ[Grz] C 🡒 (A 🡒 (B ⋎ D)) := mdp imp_swap (mdp imp_uncurry_and h);
  exact impTrans h2 imp_push_disj;

/-- Necessitation is monotone over implication: `A 🡒 B` yields `□A 🡒 □B`. -/
lemma boxImp (h : ⊢ʰ[Grz] A 🡒 B) : ⊢ʰ[Grz] □A 🡒 □B := mdp modalK (nec h)

/-- `□` collects binary conjunctions: `□A ⋏ □B` derives `□(A ⋏ B)`. -/
lemma imp_box_and : ⊢ʰ[Grz] (□A ⋏ □B) 🡒 □(A ⋏ B) := by
  have h3 : ⊢ʰ[Grz] □A 🡒 (□B 🡒 □(A ⋏ B)) := impTrans (boxImp andIntro) modalK;
  apply DeducibleHilbert.iff_singleton_deducible_provable.mp;
  have hmem : ({□A ⋏ □B}) ⊢ʰ[Grz] □A ⋏ □B := DeducibleHilbert.ofContext (by grind);
  have hA : ({□A ⋏ □B}) ⊢ʰ[Grz] □A := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andL) hmem;
  have hB : ({□A ⋏ □B}) ⊢ʰ[Grz] □B := DeducibleHilbert.mdp (DeducibleHilbert.ofProvable andR) hmem;
  exact DeducibleHilbert.mdp (DeducibleHilbert.mdp (DeducibleHilbert.ofProvable h3) hA) hB;

/-- `□` collects a finset conjunction: `⋀(Δ.box)` derives `□(⋀Δ)` (analogue of `collect_box_conj`). -/
lemma imp_conj_box [DecidableEq α] {Δ : FormulaFinset α} : ⊢ʰ[Grz] ⋀(Δ.box) 🡒 □(⋀Δ) := by
  induction Δ using Finset.induction with
  | empty => simp only [FormulaFinset.box, Finset.image_empty, FormulaFinset.conj_empty]; exact af (nec top);
  | insert A Δ' _ ih =>
    rw [show FormulaFinset.box (insert A Δ') = insert (□A) (FormulaFinset.box Δ') from Finset.image_insert ..];
    refine impTrans imp_insert_fconj ?_;
    exact impTrans (ctxAndIntroRule andL (impTrans andR ih)) (impTrans imp_box_and (boxImp imp_fconj_insert));

theorem of_provableGentzen [DecidableEq α] {S : Sequent α} : ⊢ᵍ[Grz] S → ⊢ʰ[Grz] (⋀S.ant) 🡒 (⋁S.suc) := by
  intro h;
  induction h with
  | axm A => simp;
  | botL => simp;
  | wkL _ hΓ ih =>
    exact ProvableHilbert.impTrans (imp_fconj_fconj_of_subset (by grind)) ih;
  | wkR _ hΔ ih =>
    exact ProvableHilbert.impTrans ih (imp_fdisj_fdisj_of_subset (by grind));
  | impL h₁ h₂ ih₁ ih₂ =>
    have e₁ := impTrans ih₁ imp_fdisj_insert;
    have e₂ := impTrans imp_fconj_insert ih₂;
    exact impTrans imp_insert_fconj (bridge_impL e₁ e₂);
  | impR h ih =>
    have e := impTrans imp_fconj_insert (impTrans ih imp_fdisj_insert);
    exact impTrans (bridge_impR e) imp_insert_fdisj;
  | @boxT Γ Δ B h ih =>
    -- ih : ⊢ʰ[Grz] ⋀(insert B Γ) 🡒 ⋁Δ, goal : ⊢ʰ[Grz] ⋀(insert (□B) Γ) 🡒 ⋁Δ
    have step : ⊢ʰ[Grz] ⋀(insert (□B) Γ) 🡒 ⋀(insert B Γ) :=
      impTrans imp_insert_fconj (impTrans (ctxAndIntroRule (impTrans andL modalT) andR) imp_fconj_insert);
    exact impTrans step ih;
  | @boxGrz Γ A h ih =>
    -- ih : ⊢ʰ[Grz] ⋀(insert (□(A 🡒 □A)) Γ.box) 🡒 A, goal : ⊢ʰ[Grz] ⋀Γ.box 🡒 □A
    simp_all;
    have ih' : ⊢ʰ[Grz] (□(A 🡒 □A) ⋏ ⋀Γ.box) 🡒 A := impTrans imp_fconj_insert ih;
    have step2 : ⊢ʰ[Grz] ⋀Γ.box 🡒 (□(A 🡒 □A) 🡒 A) := mdp imp_swap (mdp imp_uncurry_and ih');
    have step4 : ⊢ʰ[Grz] □(⋀Γ.box) 🡒 □A := impTrans (boxImp step2) modalGrz;
    have step5 : ⊢ʰ[Grz] ⋀Γ.box 🡒 ⋀(Γ.box.box) := by
      apply imp_fconj_of_forall;
      intro F hF;
      obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hF;
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hE;
      exact impTrans (imp_fconj_of_mem (Finset.mem_image.mpr ⟨C, hC, rfl⟩)) modal4;
    exact impTrans (impTrans step5 imp_conj_box) step4;

theorem of_provableGentzen_singleton [DecidableEq α] : ⊢ᵍ[Grz] (∅ ⟹ {A}) → ⊢ʰ[Grz] A := by
  intro h;
  simpa using mdp (of_provableGentzen h) (by simp);

end ProvableHilbert


theorem iff_provableHilbert_provableGentzen [DecidableEq α] {A : Formula α} :
  ⊢ʰ[Grz] A ↔ ⊢ᵍ[Grz] (∅ ⟹ {A} : Sequent α) :=
  ⟨ProvableGentzen.of_provableHilbert, ProvableHilbert.of_provableGentzen_singleton⟩

end LogicGrz

end
