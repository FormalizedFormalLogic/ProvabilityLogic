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


namespace ProvableGentzen

variable {A : Formula α}

/-- Every Hilbert-provable `Grz` formula is Gentzen-provable as a singleton sequent.
Provable by induction on the Hilbert derivation, translating each axiom/rule to its
`LogicGrz.ProofGentzen` counterpart (`ProofGentzen.modalT`, `.modal4`, `.modalGrz`, `.nec`,
`ProvableGentzen.mdp`); left for the Hilbert-side follow-up task. -/
theorem of_provableHilbert [DecidableEq α] : ⊢ʰ[Grz] A → ⊢ᵍ[Grz] (∅ ⟹ {A} : Sequent α) := sorry

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
