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

variable {A : Formula α}

/-!
Porting `⋀`/`⋁` conjunction/disjunction Hilbert infrastructure (`DeducibleHilbert`, the
deduction theorem, `impTrans`, `imp_fconj_*`, `imp_fdisj_*`, `bridge_impL`, `bridge_impR`,
`imp_conj_box`, …) analogous to `LogicGL.ProvableHilbert` is left to a follow-up task; the two
theorems below depend on it and are stated with `sorry` for now.
-/

theorem of_provableGentzen [DecidableEq α] {S : Sequent α} : ⊢ᵍ[Grz] S → ⊢ʰ[Grz] (⋀S.ant) 🡒 (⋁S.suc) := sorry

theorem of_provableGentzen_singleton [DecidableEq α] : ⊢ᵍ[Grz] (∅ ⟹ {A}) → ⊢ʰ[Grz] A := sorry

end ProvableHilbert


theorem iff_provableHilbert_provableGentzen [DecidableEq α] {A : Formula α} :
  ⊢ʰ[Grz] A ↔ ⊢ᵍ[Grz] (∅ ⟹ {A} : Sequent α) := sorry

end LogicGrz

end
