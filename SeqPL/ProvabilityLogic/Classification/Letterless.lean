module

public import SeqPL.Kripke.Rank
public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Vorspiel.Set.Approximate
public import SeqPL.Formula.Countable
public import SeqPL.ProvabilityLogic.Interpret
public import SeqPL.ProvabilityLogic.GL.Uniform
public import Mathlib.Tactic.TautoSet
public import Mathlib.Order.Minimal
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height

@[expose]
public section

noncomputable abbrev TBBMinus [DecidableEq α] (X : Set ℕ) (X_finite : X.Finite := by grind) : Formula α := ∼⋀(X_finite.toFinset.image TBB)

namespace LetterlessFormula

@[grind]
def spectrum (A : LetterlessFormula) : Set ℕ := match A with
  | ⊥ => ∅
  | A 🡒 B => (spectrum A)ᶜ ∪ spectrum B
  | □A => { n | ∀ i < n, i ∈ spectrum A }

variable {A B : LetterlessFormula}

lemma spectrum_bot : spectrum (⊥ : LetterlessFormula) = ∅ := by grind;
lemma spectrum_top : spectrum (⊤ : LetterlessFormula) = Set.univ := by grind;
lemma spectrum_imp : spectrum (A 🡒 B) = (spectrum A)ᶜ ∪ spectrum B := by simp [spectrum]
lemma spectrum_neg : spectrum (∼A) = (spectrum A)ᶜ := by simp [spectrum]
lemma spectrum_or  : spectrum (A ⋎ B) = spectrum A ∪ spectrum B := by simp [spectrum];
lemma spectrum_and : spectrum (A ⋏ B) = spectrum A ∩ spectrum B := by simp [spectrum];
lemma spectrum_box : spectrum (□A) = { n | ∀ i < n, i ∈ A.spectrum } := by simp [spectrum];

attribute [simp, grind .]
  spectrum_bot
  spectrum_top
attribute [grind =]
  spectrum_imp
  spectrum_neg
  spectrum_or
  spectrum_and
  spectrum_box

@[simp, grind =]
lemma spectrum_boxItr {n : ℕ} : spectrum (□^[(n + 1)]A) = { k | ∀ i < k, i ∈ spectrum (□^[n]A) } := by
  induction n <;> grind;

@[grind =]
lemma spectrum_boxdot : spectrum (⊡A) = { n | ∀ i ≤ n, i ∈ spectrum A } := by grind;

@[simp, grind =]
lemma spectrum_boxItr_bot : spectrum (□^[n]⊥) = { i | i < n } := by
  induction n with
  | zero => grind;
  | succ n ih =>
    calc
      _ = { i | ∀ k < i, k ∈ spectrum (□^[n]⊥) } := by grind
      _ = { i | ∀ k < i, k < n }                           := by simp [ih];
      _ = { i | i < n + 1 }                                := by grind;

@[simp, grind =]
lemma spectrum_lconj {Γ : FormulaList Empty} : spectrum (⋀Γ) = ⋂ A ∈ Γ, spectrum A := by
  match Γ with
  | [] | [A] | A :: B :: Γ => simp [FormulaList.conj, spectrum_and, spectrum_lconj]

@[simp, grind =]
lemma spectrum_fconj {Γ : FormulaFinset Empty} : spectrum (⋀Γ) = ⋂ A ∈ Γ, spectrum A := by
  simp [FormulaFinset.conj, spectrum_lconj];

@[simp, grind =]
lemma spectrum_TBB : spectrum (TBB n) = {n}ᶜ := by
  rw [TBB, spectrum_imp, spectrum_boxItr_bot, spectrum_boxItr_bot];
  ext i;
  grind;

@[grind]
def trace (A : Formula Empty) := (spectrum A)ᶜ

lemma trace_bot : trace ⊥ = Set.univ := by grind;
lemma trace_top : trace ⊤ = ∅ := by grind;
lemma trace_and : trace (A ⋏ B) = trace A ∪ trace B := by grind;
lemma trace_or  : trace (A ⋎ B) = trace A ∩ trace B := by grind;
lemma trace_imp : trace (A 🡒 B) = (trace A)ᶜ ∩ trace B := by grind;
lemma trace_neg : trace (∼A) = (trace A)ᶜ := by grind;

attribute [simp, grind .]
  trace_bot
  trace_top
attribute [grind =]
  trace_and
  trace_or
  trace_imp
  trace_neg

@[simp, grind =]
lemma trace_TBB : trace (TBB n) = {n} := by grind;

@[simp, grind =]
lemma trace_lconj {Γ : FormulaList Empty} : trace (⋀Γ) = ⋃ A ∈ Γ, trace A := by
  match Γ with
  | [] | [A] | A :: B :: Γ => simp [FormulaList.conj, trace_and, trace_lconj]

@[simp, grind =]
lemma trace_fconj {Γ : FormulaFinset Empty} : trace (⋀Γ) = ⋃ A ∈ Γ, trace A := by
  simp [FormulaFinset.conj, trace_lconj];

@[simp, grind =]
lemma trace_TBBMinus {s : Set ℕ} (hs : s.Finite) : trace (TBBMinus s) = sᶜ := by simp [trace_neg, trace_fconj];

@[grind .]
lemma spectrum_finite_or_cofinite : A.spectrum.Finite ∨ A.spectrumᶜ.Finite := by
  induction A with
  | atom a => grind;
  | bot => grind;
  | imp A B ihA ihB =>
    simp only [spectrum_imp, Set.finite_union];
    rcases ihA with (hA | hA) <;> rcases ihB with (hB | hB);
    · right; rw [Set.compl_union, compl_compl]; exact hA.inter_of_left _;
    · right; rw [Set.compl_union, compl_compl]; exact hA.inter_of_left _;
    · left; exact ⟨hA, hB⟩;
    · right; rw [Set.compl_union, compl_compl]; exact hB.inter_of_right _;
  | box A ih =>
    by_cases h : spectrum A = Set.univ;
    . grind;
    . left;
      obtain ⟨k, hk₁, hk₂⟩ := exists_minimal_of_wellFoundedLT (λ k => k ∉ spectrum A) $ Set.ne_univ_iff_exists_notMem _ |>.mp h;
      have : {n | ∀ i < n, i ∈ spectrum A} = { n | n ≤ k} := by
        ext i;
        suffices (∀ j < i, j ∈ spectrum A) ↔ i ≤ k by simpa [Set.mem_setOf_eq];
        constructor;
        . intro h;
          contrapose! hk₁;
          exact h k (by omega);
        . intro h j hji;
          contrapose! hk₂;
          use j;
          constructor;
          . assumption;
          . omega;
      rw [spectrum_box, this];
      apply Set.finite_le_nat;

@[grind .]
lemma trace_finite_or_cofinite : (trace A).Finite ∨ (trace A)ᶜ.Finite := by
  simp only [trace, compl_compl];
  exact spectrum_finite_or_cofinite.symm;

@[grind →]
lemma spectrum_finite_of_trace_infinite : (trace A).Infinite → (spectrum A).Finite := by
  rcases spectrum_finite_or_cofinite (A := A) with (h | h);
  . tauto;
  . simp_all [trace];

@[grind →]
lemma trace_finite_of_spectrum_infinite : (spectrum A).Infinite → (trace A).Finite := by
  contrapose!;
  exact spectrum_finite_of_trace_infinite;


end LetterlessFormula


open LetterlessFormula (spectrum trace)


namespace Model

variable
  [Nonempty κ]
  {M : Model κ Empty} [Fintype M.World] [M.IsGL]
  {x : M.World} {A : LetterlessFormula}

lemma iff_forces_rank_mem_spectrum : x ⊩ A ↔ x.rank ∈ (spectrum A) := by
  induction A generalizing x with
  | box A ih =>
    calc
      _ ↔ ∀ y, x ≺ y → y ⊩ A := by grind;
      _ ↔ ∀ y, x ≺ y → y.rank ∈ (LetterlessFormula.spectrum A) := by simp [ih];
      _ ↔ ∀ i < x.rank, i ∈ (spectrum A) := by
        constructor;
        . intro h i hi;
          grind [of_lt_rank hi];
        . grind [rank_lt_of_rel];
      _ ↔ x.rank ∈ spectrum (□A) := by grind;
  | _ => grind;

lemma iff_not_forces_rank_mem_trace : x ⊮ A ↔ x.rank ∈ (trace A) := by
  grind [iff_forces_rank_mem_spectrum];

end Model

abbrev finiteLineModel (n : ℕ) : RootedModel (Fin (n + 1)) Empty where
  Rel' := (· < ·)
  Val' _ _ := False
  root := ⟨0, by
    intro x hx;
    exact Fin.pos_of_ne_zero hx;
  ⟩

namespace finiteLineModel

variable {n : ℕ}

instance : Fintype (finiteLineModel n).World := inferInstance
instance : (finiteLineModel n).IsFiniteGL where
  finite := by infer_instance
instance : (finiteLineModel n).IsGL := Model.instIsGLOfIsFiniteGL

protected abbrev of (i : Fin (n + 1)) : (finiteLineModel n).World := i
instance : Coe (Fin (n + 1)) (finiteLineModel n).World := ⟨finiteLineModel.of⟩

lemma _root_.PNat.exists_eq_succ (n : ℕ+) : ∃ m : ℕ, n = m + 1 := by
  if n = 1 then
    use 0;
    simp_all;
  else
    obtain ⟨m, hm⟩ := PNat.exists_eq_succ_of_ne_one ‹_›;
    use m;
    simp_all;

lemma rank_eq (i : (finiteLineModel n).World) : i.rank = (n - i) := by
  induction i using Fin.reverseInduction with
  | last =>
    rw [show (n - (Fin.last n : ℕ)) = 0 by simp];
    apply Model.iff_rank_eq_zero.mpr;
    intro y;
    exact not_lt.mpr (Fin.le_last y);
  | cast i ih =>
    suffices (finiteLineModel.of i.castSucc).rank = (finiteLineModel.of i.succ).rank + 1 by grind;
    haveI : IsConverseWellFounded (finiteLineModel n).World (finiteLineModel n).Rel :=
      ⟨(inferInstance : (finiteLineModel n).IsGL).cwf⟩;
    apply cwfHeight_eq_succ_cwfHeight (r := (finiteLineModel n).Rel);
    . exact Fin.castSucc_lt_succ;
    . intro c hc;
      simp only [Model.Rel, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hc ⊢;
      omega;

lemma height_eq : (finiteLineModel n).height = n := by apply rank_eq;

end finiteLineModel

section

variable {A B : LetterlessFormula}

lemma spectrum_TFAE : [
  n ∈ spectrum A,
  ∀ {κ : Type 0}, [Nonempty κ] → [Fintype κ] → ∀ M : Model κ Empty, [M.IsGL] → ∀ x : M.World, x.rank = n → x ⊩ A,
  ∃ κ : Type 0, ∃ _ : Nonempty κ, ∃ _ : Fintype κ, ∃ M : Model κ Empty, ∃ _ : M.IsGL, ∃ x : M.World, x.rank = n ∧ x ⊩ A,
].TFAE := by
  tfae_have 1 → 2 := by grind [Model.iff_forces_rank_mem_spectrum];
  tfae_have 3 → 1 := by grind [Model.iff_forces_rank_mem_spectrum];
  tfae_have 2 → 3 := by
    intro h;
    use Fin (n + 1), inferInstance, inferInstance, (finiteLineModel n).toModel, inferInstance, (finiteLineModel n).root.1;
    constructor;
    . exact finiteLineModel.height_eq;
    . apply h;
      exact finiteLineModel.height_eq;
  tfae_finish;

lemma iff_GL_proves_spectrum_univ : A ∈ LogicGL ↔ spectrum A = Set.univ := by
  rw [Set.eq_univ_iff_forall];
  apply Iff.trans $ LogicGL_TFAE.out 0 4;
  constructor;
  . intro h n;
    apply spectrum_TFAE.out 1 0 |>.mp;
    intro κ _ _ M _ x rfl;
    have : Finite M.World := by infer_instance;
    apply @h κ _ M {};
  . intro h κ _ M _ x;
    have : Fintype M.World := Fintype.ofFinite _;
    have := spectrum_TFAE.out 0 1 |>.mp $ h x.rank;
    exact this M x rfl;

lemma iff_GL_proves_imp_GL_subset_spectrum : (A 🡒 B) ∈ LogicGL ↔ spectrum A ⊆ spectrum B := by
  apply Iff.trans iff_GL_proves_spectrum_univ;
  simp only [LetterlessFormula.spectrum_imp, Set.eq_univ_iff_forall, Set.mem_union, Set.mem_compl_iff];
  grind;

lemma iff_GL_proves_iff_GL_subset_spectrum : (A 🡘 B) ∈ LogicGL ↔ spectrum A = spectrum B := by
  suffices (A 🡘 B) ∈ LogicGL ↔ (A 🡒 B) ∈ LogicGL ∧ (B 🡒 A) ∈ LogicGL by
    grind [Set.Subset.antisymm_iff, iff_GL_proves_imp_GL_subset_spectrum];
  constructor;
  . intro h;
    replace h := LogicGL_semantical_TFAE.out 0 2 |>.mp h;
    refine ⟨?_, ?_⟩ <;>
      apply LogicGL_semantical_TFAE.out 2 0 |>.mp <;>
      intro κ _ M _ <;>
      have := @h κ _ M _ <;>
      grind;
  . rintro ⟨h₁, h₂⟩;
    replace h₁ := LogicGL_semantical_TFAE.out 0 2 |>.mp h₁;
    replace h₂ := LogicGL_semantical_TFAE.out 0 2 |>.mp h₂;
    apply LogicGL_semantical_TFAE.out 2 0 |>.mp;
    intro κ _ M _;
    have := @h₁ κ _ M _;
    have := @h₂ κ _ M _;
    grind;

lemma LetterlessFormula.TBB_normalization_of_finite_trace (h : (trace A).Finite) : (A 🡘 ⋀(h.toFinset.image TBB)) ∈ LogicGL := by
  apply iff_GL_proves_iff_GL_subset_spectrum.mpr;
  calc
    _ = ⋂ i ∈ trace A, spectrum (TBB i) := by
      ext i;
      simp [LetterlessFormula.trace];
      grind;
    _ = _ := by
      simp [LetterlessFormula.spectrum_fconj];

lemma LetterlessFormula.TBBMinus_normalization_of_finite_spectrum (h : (spectrum A).Finite) : (A 🡘 TBBMinus _ h) ∈ LogicGL := by
  apply iff_GL_proves_iff_GL_subset_spectrum.mpr;
  exact (compl_inj_iff.mp (LetterlessFormula.trace_TBBMinus (s := A.spectrum) h)).symm;

lemma GL_proves_letterless_axiomWeakPoint3 : ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A))) ∈ LogicGL := by
  apply iff_GL_proves_spectrum_univ.mpr;
  grind;

end

open LO
open LO.FirstOrder.ProvabilityAbstraction

namespace LetterlessFormula

section

variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L} {𝔅 : Provability T₀ T}

@[grind]
def interpret (𝔅 : Provability T₀ T) : LetterlessFormula → FirstOrder.Sentence L
  | ⊥     => ⊥
  | A 🡒 B => (interpret 𝔅 A) 🡒 (interpret 𝔅 B)
  | □A    => 𝔅 (interpret 𝔅 A)

@[grind =]
lemma interpret_boxItr : interpret 𝔅 (□^[n]A) = 𝔅^[n] (interpret 𝔅 A) := by
  induction n with
  | zero => simp [Formula.boxItr];
  | succ n ih => rw [Function.iterate_succ']; grind;

noncomputable abbrev standardInterpret (T : FirstOrder.ArithmeticTheory) [T.Δ₁] := interpret T.standardProvability

lemma interpret_lift {α : Type*} {f : Realization α 𝔅} {A : LetterlessFormula} :
    Formula.interpret f (LetterlessFormula.lift A) = LetterlessFormula.interpret 𝔅 A := by
  induction A with
  | atom a => exact a.elim
  | _ => simp_all [Formula.interpret, LetterlessFormula.interpret, LetterlessFormula.lift]

lemma _root_.Formula.interpret_subst {α : Type*} {f : Realization α 𝔅} {s : Formula.Substitution α} {A : Formula α} :
    Formula.interpret f (A⟦s⟧) = Formula.interpret (⟨fun a => Formula.interpret f (s a)⟩ : Realization α 𝔅) A := by
  induction A with
  | atom a => rfl
  | _ => simp_all [Formula.interpret, Formula.subst_imp, Formula.subst_box]

end


variable {T₀ T U : FirstOrder.ArithmeticTheory} [T.Δ₁] {A B : LetterlessFormula}

@[grind]
def Regular (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (A : LetterlessFormula) := ℕ ⊧ₘ A.interpret T.standardProvability

@[simp, grind .]lemma regular_bot : ¬(Regular T ⊥) := by grind;
@[simp, grind .]lemma regular_top : Regular T ⊤ := by grind;
@[grind =] lemma regular_imp : Regular T (A 🡒 B) ↔ (Regular T A → Regular T B) := by grind;
@[grind =] lemma regular_and : Regular T (A ⋏ B) ↔ (Regular T A ∧ Regular T B) := by grind;
@[grind =] lemma regular_or  : Regular T (A ⋎ B) ↔ (Regular T A ∨ Regular T B) := by grind;
@[grind =] lemma regular_neg : Regular T (∼A) ↔ ¬(Regular T A) := by grind;
@[grind =] lemma regular_iff : Regular T (A 🡘 B) ↔ (Regular T A ↔ Regular T B) := by grind;

@[grind =]
lemma regular_lconj {Γ : LetterlessFormulaList} : Regular T (⋀Γ) ↔ ∀ A ∈ Γ, Regular T A := by
  match Γ with
  | [] | [A] | A :: B :: Γ => simp [FormulaList.conj, regular_and, regular_lconj]

@[grind =]
lemma regular_fconj {Γ : LetterlessFormulaFinset} : Regular T (⋀Γ) ↔ ∀ A ∈ Γ, Regular T A := by
  simp [FormulaFinset.conj, regular_lconj];

@[grind]
def Singular (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (A : LetterlessFormula) := ¬(A.Regular T)

@[simp, grind .] lemma singular_bot : Singular T ⊥ := by grind;
@[simp, grind .] lemma singular_top : ¬(Singular T ⊤) := by grind;
@[grind =] lemma singular_imp : Singular T (A 🡒 B) ↔ (¬Singular T A ∧ Singular T B) := by grind;
@[grind =] lemma singular_and : Singular T (A ⋏ B) ↔ (Singular T A ∨ Singular T B) := by grind;
@[grind =] lemma singular_or  : Singular T (A ⋎ B) ↔ (Singular T A ∧ Singular T B) := by grind;
@[grind =] lemma singular_neg : Singular T (∼A) ↔ ¬(Singular T A) := by grind;

variable [ℕ ⊧ₘ* T]
variable {n : ℕ}

@[grind .]
lemma singular_boxItr_bot : Singular T (□^[n]⊥) := by
  match n with
  | 0 => grind;
  | n + 1 =>
    apply not_imp_not.mpr $ Provability.SoundOn.sound_on;
    rw [interpret_boxItr];
    exact LO.FirstOrder.ProvabilityAbstraction.iIncon_unprovable_of_sigma1_sound n;

@[simp, grind .]
lemma regular_TBB : Regular T (TBB n) := by
  apply regular_imp.mpr;
  contrapose!;
  intro _;
  exact singular_boxItr_bot;

@[simp, grind .]
lemma regular_fconj_TBB_finset {Γ : Finset ℕ} : Regular T (⋀(Γ.image TBB)) := by grind;

@[simp, grind .]
lemma singular_TBBMinus (hs : s.Finite) : Singular T (TBBMinus s) := by grind;

end LetterlessFormula


namespace LetterlessFormulaSet

variable {T₀ T U : FirstOrder.ArithmeticTheory} [T.Δ₁] {A B : LetterlessFormula}
variable {X : LetterlessFormulaSet} {A : LetterlessFormula} {s : Set ℕ}

@[grind] def spectrum (X : LetterlessFormulaSet) : Set ℕ := ⋂ A ∈ X, LetterlessFormula.spectrum A
@[grind] def trace (X : LetterlessFormulaSet) : Set ℕ := X.spectrumᶜ

@[grind] def Regular (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (X : LetterlessFormulaSet) := ∀ A : LetterlessFormula, A ∈ X → LetterlessFormula.Regular T A
@[grind] def Singular (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (X : LetterlessFormulaSet) := ¬(X.Regular T)

lemma eq_spectrum : X.spectrum = (⋂ A ∈ X, LetterlessFormula.spectrum A) := rfl
lemma eq_trace : X.trace = (⋃ A ∈ X, LetterlessFormula.trace A) := by simp [LetterlessFormulaSet.trace, LetterlessFormula.trace, spectrum];

@[grind =]
lemma iff_singular_exists_singular : X.Singular T ↔ ∃ (A : LetterlessFormula), A ∈ X ∧ LetterlessFormula.Singular T A := by grind;

lemma spectrum_subset_of_mem (h : A ∈ X) : X.spectrum ⊆ A.spectrum := by
  intro i hi;
  apply Set.mem_iInter.mp hi A;
  grind;

variable [ℕ ⊧ₘ* T]

@[simp, grind =_]
lemma eq_trace_singleton : trace {A} = LetterlessFormula.trace A := by
  rw [eq_trace];
  simp;

lemma eq_TBB_trace : LetterlessFormulaSet.trace (TBB '' s) = s := by simp [eq_trace]

@[simp, grind =_]
lemma eq_trace_TBB_trace : LetterlessFormulaSet.trace (TBB '' X.trace) = X.trace := eq_TBB_trace

@[simp, grind .]
lemma regular_TBB_set {X : Set ℕ} : LetterlessFormulaSet.Regular T (X.image TBB) := by grind;

@[simp, grind =_]
lemma eq_trace_TBBMinus_singleton (hs : s.Finite) : trace {TBBMinus s} = sᶜ := by grind [eq_trace_singleton];

@[simp, grind .]
lemma singular_TBBMinus_singleton (hs : s.Finite) : LetterlessFormulaSet.Singular T {TBBMinus _ hs} := by
  simp only [Singular, Regular, Set.mem_singleton_iff, forall_eq];
  grind;

end LetterlessFormulaSet


section

open LetterlessFormula (interpret)

variable
  {T₀ T : FirstOrder.ArithmeticTheory} [ℕ ⊧ₘ* T] [T.Δ₁] [𝗜𝚺₁ ⪯ T]
  {A B : LetterlessFormula}

axiom letterless_arithmetical_completeness [𝗜𝚺₁ ⪯ T] : A ∈ LogicGL ↔ T ⊢ A.interpret T.standardProvability

namespace LetterlessFormula

@[grind →]
lemma iff_regular_of_provable_iff (h : A 🡘 B ∈ LogicGL) : A.Regular T ↔ B.Regular T := by
  have : T ⊢  interpret _ (A 🡘 B) := letterless_arithmetical_completeness (T := T) |>.mp h;
  have : ℕ ⊧ₘ interpret _ (A 🡘 B) := FirstOrder.ArithmeticTheory.SoundOn.sound (F := λ _ => True) this $ by simp;
  grind;

@[grind →]
lemma iff_singular_of_provable_iff (h : A 🡘 B ∈ LogicGL) : A.Singular T ↔ B.Singular T := by
  grind [iff_regular_of_provable_iff h];

@[grind =]
lemma iff_regular_trace_finite : A.Regular T ↔ (trace A).Finite := by
  constructor;
  . contrapose!;
    intro h;
    replace h : (spectrum A).Finite := by grind;
    apply iff_singular_of_provable_iff (LetterlessFormula.TBBMinus_normalization_of_finite_spectrum h) |>.mpr;
    grind;
  . intro h;
    apply iff_regular_of_provable_iff (LetterlessFormula.TBB_normalization_of_finite_trace h) |>.mpr;
    grind;

@[grind <=]
lemma finite_spectrum_of_singular : A.Singular T → (A.spectrum).Finite := by grind;

end LetterlessFormula


namespace LetterlessFormulaSet

variable {X : LetterlessFormulaSet} {A : LetterlessFormula}

@[grind <=]
lemma trace_cofinite_of_singular (h : X.Singular T) : X.traceᶜ.Finite := by
  obtain ⟨A, hA, h⟩ := iff_singular_exists_singular.mp h;
  suffices X.spectrum ⊆ A.spectrum by
    simp only [LetterlessFormulaSet.trace, compl_compl];
    apply Set.Finite.subset ?_ this;
    grind;
  grind [spectrum_subset_of_mem];

end LetterlessFormulaSet

section

variable {α} {X Y : LetterlessFormulaSet} {A : LetterlessFormula}

/-- α-原子を ⊥ に潰して Empty 上の論理式へ射影する（letterless の lift の逆向き）． -/
def _root_.Formula.projectEmpty : Formula α → LetterlessFormula
  | .atom _ => ⊥
  | ⊥       => ⊥
  | A 🡒 B   => A.projectEmpty 🡒 B.projectEmpty
  | □A      => □(A.projectEmpty)

@[simp] lemma _root_.Formula.projectEmpty_lift {B : LetterlessFormula} :
    (LetterlessFormula.lift B : Formula α).projectEmpty = B := by
  induction B with
  | atom a => exact a.elim
  | bot => rfl
  | imp A C ihA ihC =>
    show (LetterlessFormula.lift A : Formula α).projectEmpty 🡒 (LetterlessFormula.lift C : Formula α).projectEmpty = _;
    rw [ihA, ihC]
  | box A ih =>
    show □((LetterlessFormula.lift A : Formula α).projectEmpty) = _;
    rw [ih]

lemma ProvableHilbert.project {A : Formula α} (h : ⊢ʰ A) : ⊢ʰ (A.projectEmpty : LetterlessFormula) := by
  induction h using ProvableHilbert.rec with
  | prop1 => exact ProvableHilbert.prop1
  | prop2 => exact ProvableHilbert.prop2
  | prop3 => exact ProvableHilbert.prop3
  | modalK => exact ProvableHilbert.modalK
  | modal4 => exact ProvableHilbert.modal4
  | modalL => exact ProvableHilbert.modalL
  | mdp h₁ h₂ ih₁ ih₂ => exact ProvableHilbert.mdp ih₁ ih₂
  | nec h ih => exact ProvableHilbert.nec ih

lemma ProvableHilbert.lift {B : LetterlessFormula} (h : ⊢ʰ B) : ⊢ʰ (LetterlessFormula.lift B : Formula α) := by
  induction h using ProvableHilbert.rec with
  | prop1 => exact ProvableHilbert.prop1
  | prop2 => exact ProvableHilbert.prop2
  | prop3 => exact ProvableHilbert.prop3
  | modalK => exact ProvableHilbert.modalK
  | modal4 => exact ProvableHilbert.modal4
  | modalL => exact ProvableHilbert.modalL
  | mdp h₁ h₂ ih₁ ih₂ => exact ProvableHilbert.mdp ih₁ ih₂
  | nec h ih => exact ProvableHilbert.nec ih

lemma iff_lift_mem_LogicGL {B : LetterlessFormula} :
    (LetterlessFormula.lift B : Formula α) ∈ LogicGL ↔ B ∈ (LogicGL : Logic Empty) := by
  constructor;
  · intro h;
    have := ProvableHilbert.project (α := α) h;
    rwa [Formula.projectEmpty_lift] at this;
  · exact ProvableHilbert.lift;

/--
  Compactness for quasi-normal extensions of `GL` by (lifted) letterless formula sets:
  a lifted letterless formula is provable iff it follows from a finite subset in `GL`
  (cf. `Logic.sumQuasiNormal.iff_provable_finite_provable` in Foundation).
-/
lemma iff_GL_sumQuasiNormal_provable_finite_provable {X : LetterlessFormulaSet} {A : LetterlessFormula} :
    ↑A ∈ ((@LogicGL α) +ᴸ ↑X) ↔
    ∃ Y : LetterlessFormulaFinset, (∀ ψ ∈ Y, ψ ∈ X) ∧ ((⋀Y) 🡒 A) ∈ LogicGL := by
  sorry;

lemma iff_GL_sumQuasiNormal_proves_subset_spectrum (hSR : X.Singular T ∨ A.Regular T)
  : ↑A ∈ ((@LogicGL α) +ᴸ X) ↔ X.spectrum ⊆ A.spectrum := by calc
  _ ↔ ∃ Y : LetterlessFormulaFinset, (∀ ψ ∈ Y, ψ ∈ X) ∧ (⋀Y) 🡒 A ∈ LogicGL := by
    exact iff_GL_sumQuasiNormal_provable_finite_provable;
  _ ↔ ∃ Y : LetterlessFormulaFinset, (∀ ψ ∈ Y, ψ ∈ X) ∧ (⋂ B ∈ Y, spectrum B) ⊆ A.spectrum := by
    constructor;
    . rintro ⟨Y, hY, h⟩;
      use Y;
      constructor;
      . assumption;
      . replace h := iff_GL_proves_imp_GL_subset_spectrum.mp h;
        simp_all [LetterlessFormula.spectrum_fconj];
    . rintro ⟨Y, hY, h⟩;
      use Y;
      constructor;
      . assumption;
      . apply iff_GL_proves_imp_GL_subset_spectrum.mpr;
        simp_all [LetterlessFormula.spectrum_fconj];
  _ ↔ (⋂ B ∈ X, spectrum B) ⊆ A.spectrum := by
    constructor;
    . rintro ⟨Y, hY, h⟩ i hi;
      apply h;
      simp_all;
    . intro h;
      rcases hSR with X_singualr | A_regular;
      . wlog X_infinite : X.Infinite;
        . replace X_infinite : X.Finite := by simpa using X_infinite;
          use X_infinite.toFinset;
          constructor;
          . simp;
          . intro i hi;
            apply h;
            simp_all;
        obtain ⟨B, hBX, B_singular⟩ := LetterlessFormulaSet.iff_singular_exists_singular.mp X_singualr;
        obtain ⟨f, f0, f_ss, fX, f_inv⟩ := Set.infinitely_finset_approximate X.to_countable X_infinite hBX;
        have f_mono : Monotone f := monotone_nat_of_le_succ (fun i => (f_ss i).1);
        let sf : ℕ → Set ℕ := fun i => ⋂ C ∈ f i, spectrum C;
        have sf_anti : ∀ i j, i ≤ j → sf j ⊆ sf i := by
          intro i j hij n hn;
          simp only [sf, Set.mem_iInter] at hn ⊢;
          intro C hC;
          exact hn C (f_mono hij hC);
        have sf0 : sf 0 = spectrum B := by simp [sf, f0];
        have sf_finite : ∀ i, (sf i).Finite := by
          intro i;
          apply Set.Finite.subset (s := sf 0) ?_ (sf_anti 0 i (Nat.zero_le i));
          rw [sf0];
          exact LetterlessFormula.finite_spectrum_of_singular B_singular;
        have sf_X : ∀ i, (⋂ D ∈ X, spectrum D) ⊆ sf i := by
          intro i n hn;
          simp only [sf, Set.mem_iInter] at hn ⊢;
          intro C hC;
          exact hn C (fX i hC);
        obtain ⟨k, hk⟩ : ∃ k, sf k = ⋂ D ∈ X, spectrum D := by
          by_contra! hne;
          apply Finset.no_ssubset_descending_chain (f := fun i => (sf_finite i).toFinset);
          intro i;
          have hss : (⋂ D ∈ X, spectrum D) ⊂ sf i := Set.ssubset_of_subset_ne (sf_X i) (Ne.symm (hne i));
          obtain ⟨n, hn₁, hn₂⟩ := (Set.ssubset_iff_of_subset hss.subset).mp hss;
          obtain ⟨C, hC₁, hC₂⟩ : ∃ C ∈ X, n ∉ spectrum C := by
            by_contra hcon;
            push Not at hcon;
            exact hn₂ (Set.mem_iInter₂.mpr hcon);
          obtain ⟨j, hj⟩ := f_inv C hC₁;
          have hij : i < j := by
            by_contra hle;
            push Not at hle;
            have hsub : sf i ⊆ spectrum C := by
              intro m hm;
              exact Set.mem_iInter₂.mp (sf_anti j i hle hm) C hj;
            exact hC₂ (hsub hn₁);
          refine ⟨j, hij, ?_⟩;
          rw [Set.Finite.toFinset_ssubset_toFinset];
          apply Set.ssubset_of_subset_ne (sf_anti i j hij.le);
          intro heq;
          have hnj : n ∈ sf j := heq ▸ hn₁;
          exact hC₂ (Set.mem_iInter₂.mp hnj C hj);
        refine ⟨f k, ?_, ?_⟩;
        · intro D hD; exact fX k hD;
        · show (⋂ D ∈ f k, spectrum D) ⊆ A.spectrum;
          rw [(show (⋂ D ∈ f k, spectrum D) = sf k from rfl), hk];
          exact h;
      . have htr : (trace A).Finite := LetterlessFormula.iff_regular_trace_finite.mp A_regular;
        have H : ∀ i ∈ trace A, ∃ B, ∃ _ : B ∈ X, i ∈ trace B := by
          have hcov : trace A ⊆ ⋃ B ∈ X, trace B := by
            apply Set.compl_subset_compl.mp;
            simp only [LetterlessFormula.trace, Set.compl_iUnion, compl_compl];
            exact h;
          simpa [Set.subset_def] using hcov;
        let cf := λ i (hi : i ∈ trace A) => (H i hi).choose;
        have cf_in_X : ∀ {i} {hi : i ∈ trace A}, (cf i hi) ∈ X := by
          intro i hi; exact (H i hi).choose_spec.1;
        have H₂ : ⋂ i ∈ trace A, spectrum (cf i (by assumption)) ⊆ A.spectrum := by
          suffices trace A ⊆ ⋃ i ∈ trace A, trace (cf i (by assumption)) by
            apply Set.compl_subset_compl.mp;
            simpa [LetterlessFormula.trace];
          intro j hj;
          simp only [Set.mem_iUnion, cf];
          exact ⟨j, hj, (H j hj).choose_spec.2⟩;
        haveI : Fintype { i // i ∈ trace A } := htr.fintype;
        use Finset.univ.image (λ i : { i // i ∈ trace A } => cf i.1 i.2);
        refine ⟨?_, ?_⟩;
        . simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, forall_exists_index];
          rintro B i hi rfl;
          exact (H i hi).choose_spec.1;
        . intro n hn;
          apply H₂;
          simp only [Finset.mem_image, Finset.mem_univ, true_and, Subtype.exists, Set.iInter_exists, Set.mem_iInter] at hn ⊢;
          intro j hj;
          exact hn (cf j hj) j hj rfl;

lemma iff_subset_sumQuasiNormal_subset_spectrum (hSR : X.Regular T ∨ Y.Singular T)
  : ((@LogicGL α) +ᴸ X) ⊆ ((@LogicGL α) +ᴸ Y) ↔ Y.spectrum ⊆ X.spectrum := by calc
  -- _ ↔ ∀ A ∈ Y, A ∈ ((LogicGL) +ᴸ Y) → A ∈ ((LogicGL) +ᴸ X) := by grind;
  _ ↔ ∀ (A : LetterlessFormula), A ∈ X → ↑A ∈ ((@LogicGL α) +ᴸ Y) := by
    rw [Logic.sumQuasiNormal.iff_subset];
    constructor;
    . intro h A hA;
      apply @h A (Set.mem_image_of_mem _ hA);
    . intro h;
      rintro B ⟨A, hA, rfl⟩;
      exact h A hA;
  _ ↔ ∀ (A : LetterlessFormula), A ∈ X → Y.spectrum ⊆ A.spectrum := by
    constructor;
    . intro h A hA;
      apply iff_GL_sumQuasiNormal_proves_subset_spectrum (α := α) (T := T) (by grind) |>.mp
      grind;
    . intro h A hA;
      apply iff_GL_sumQuasiNormal_proves_subset_spectrum (α := α) (T := T) (by grind) |>.mpr;
      grind;
  _ ↔ Y.spectrum ⊆ (⋂ A ∈ X, spectrum A) := by
    simp;

lemma iff_subset_sumQuasiNormal_subset_trace (hSR : X.Regular T ∨ Y.Singular T)
  : ((@LogicGL α) +ᴸ X) ⊆ ((@LogicGL α) +ᴸ Y) ↔ X.trace ⊆ Y.trace := by
  apply Iff.trans $ iff_subset_sumQuasiNormal_subset_spectrum (α := α) hSR;
  simp [LetterlessFormulaSet.trace];

lemma iff_eq_sumQuasiNormal_eq_spectrum (hSR : (X.Singular T ∧ Y.Singular T) ∨ (X.Regular T ∧ Y.Regular T))
  : ((@LogicGL α) +ᴸ X) = ((@LogicGL α) +ᴸ Y) ↔ X.spectrum = Y.spectrum := by
  grind [
    Set.Subset.antisymm_iff,
    iff_subset_sumQuasiNormal_subset_spectrum (α := α) (T := T) (X := X) (Y := Y) (by tauto),
    iff_subset_sumQuasiNormal_subset_spectrum (α := α) (T := T) (X := Y) (Y := X) (by tauto)
  ];

lemma iff_eq_sumQuasiNormal_eq_trace (hSR : (X.Singular T ∧ Y.Singular T) ∨ (X.Regular T ∧ Y.Regular T))
  : ((@LogicGL α) +ᴸ X) = ((@LogicGL α) +ᴸ Y) ↔ X.trace = Y.trace := by
  apply Iff.trans $ iff_eq_sumQuasiNormal_eq_spectrum (α := α) hSR;
  simp [LetterlessFormulaSet.trace];

abbrev LogicGLAlpha {α} (Alpha : Set ℕ) : Logic α := (@LogicGL α) +ᴸ ↑(Alpha.image $ TBB (α := Empty))
abbrev LogicGLAlphaOmega {α} : Logic α := LogicGLAlpha Set.univ
abbrev LogicGLBetaMinus {α} [DecidableEq α] (Beta : Set ℕ) (Beta_cofinite : Betaᶜ.Finite := by grind) : Logic α := (@LogicGL α) +ᴸ (LetterlessFormulaSet.lift { TBBMinus _ Beta_cofinite })



namespace FormulaSet

def Letterless {α} (X : FormulaSet α) : Prop := ∀ A ∈ X, A.Letterless

end FormulaSet


namespace LetterlessFormula

@[simp, grind =] lemma eq_lift_bot : lift (α := α) ⊥ = ⊥ := by grind;
@[simp, grind =] lemma eq_lift_box_bot : lift (α := α) (□⊥) = □⊥ := by grind;
@[simp, grind =] lemma eq_lift_boxItr_bot {n : ℕ} : lift (α := α) (□^[n]⊥) = □^[n]⊥ := by induction n <;> grind;
@[simp, grind =] lemma eq_lift_and : lift (α := α) (A ⋏ B) = (lift A) ⋏ (lift B) := by grind;

@[simp, grind =]
lemma eq_lift_lconj {Γ : LetterlessFormulaList} : lift (α := α) (⋀Γ) = ⋀(Γ.map lift) := by
  match Γ with
  | [] | [A] => grind;
  | A :: B :: Γ => simp [FormulaList.conj, eq_lift_and, eq_lift_lconj];

@[simp, grind =] lemma eq_lift_TBB {n : ℕ} : lift (α := α) (TBB n) = TBB n := by grind;

end LetterlessFormula


namespace LetterlessFormulaSet

@[simp, grind =]
lemma eq_lift_singleton {A : LetterlessFormula} {B : Formula α} : lift (α := α) {A} = {B} ↔ A.lift = B := by simp [lift];

@[simp, grind =]
lemma eq_lift_TBB_set {X : Set ℕ} : lift (α := α) (TBB '' X) = TBB '' X := by
  ext A;
  constructor;
  . rintro ⟨A, hA, rfl⟩; grind;
  . rintro ⟨i, hi, rfl⟩; grind [LetterlessFormulaSet.lift];

end LetterlessFormulaSet


lemma eq_letterless_GL_quasiNormal_extension_GLAlpha_of_regular (X_regular : X.Regular T)
  : LogicGLAlpha X.trace = ((@LogicGL α) +ᴸ ↑X) := by
  apply iff_eq_sumQuasiNormal_eq_trace (T := T) (by grind) |>.mpr;
  grind;

lemma eq_letterless_GL_quasiNormal_extension_GLBetaMinus_of_singular [DecidableEq α] (X_singular : X.Singular T)
  : LogicGLBetaMinus X.trace = ((@LogicGL α) +ᴸ ↑X) := by
  apply iff_eq_sumQuasiNormal_eq_trace (T := T) (by grind) |>.mpr;
  rw [LetterlessFormulaSet.eq_trace_TBBMinus_singleton (by grind)];
  grind;

/--
  Quasi-normal `GL` extension by letterless formula set `X` is
  either `LogicGLAlpha X.trace` (when `X` is regular, so `X.trace` is finite) or `LogicGLBetaMinus X.trace` (when `X` is singular, so `X.trace` is cofinite)
-/
theorem classification_letterless_quasiNormal_GL_extension [DecidableEq α] :
  (∃ _ : X.Regular T, ((@LogicGL α) +ᴸ ↑X) = LogicGLAlpha X.trace) ∨
  (∃ _ : X.Singular T, ((@LogicGL α) +ᴸ ↑X) = LogicGLBetaMinus X.trace) := by
  by_cases h : X.Regular T;
  . left;
    exact ⟨h, eq_letterless_GL_quasiNormal_extension_GLAlpha_of_regular h |>.symm⟩;
  . right;
    exact ⟨h, eq_letterless_GL_quasiNormal_extension_GLBetaMinus_of_singular h |>.symm⟩;

end

section

variable {T : FirstOrder.ArithmeticTheory} [𝗜𝚺₁ ⪯ T] [T.Δ₁] [ℕ ⊧ₘ* T]

namespace LO.FirstOrder.Theory

open LO.Entailment

variable
  {L : Language} [L.DecidableEq]
  {T U : Theory L} [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)]
  {φ : Sentence L}

lemma compact_add_right (h : (T + U) ⊢ φ) : ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ U }), T ⊢ s.1.conj 🡒 φ := by
  obtain ⟨⟨s, hsTU⟩, hs⟩ := Theory.compact' h;
  let sT := { ψ ∈ s | ψ ∈ T };
  let sU := { ψ ∈ s | ψ ∈ U };

  use ⟨sU, λ _ => by simp [sU]⟩;

  have : (∅ : Theory _) ⊢ sT.conj 🡒 sU.conj 🡒 φ := CK!_iff_CC!.mp $ C!_trans CKFconjFconjUnion! $ by
    have : sT ∪ sU = s:= by
      ext ψ;
      constructor;
      . grind;
      . intro hψ; rcases hsTU hψ with (hψT | hψU) <;> grind;
    rwa [this];
  apply Entailment.mdp! $ Axiomatized.weakening! (λ _ => by simp) this;
  apply Entailment.FConj!_iff_forall_provable.mpr;
  intro ψ hψ;
  apply Axiomatized.provable_axm;
  simp_all [sT];

lemma compact_add_left (h : (T + U) ⊢ φ) : ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ T }), U ⊢ s.1.conj 🡒 φ := by
  rw [show (T + U = U + T) by simp [add_def, Set.union_comm]] at h
  simpa using compact_add_right h;

end LO.FirstOrder.Theory

lemma _root_.finite_preimage_choice (s : Finset α) (X : Set β) (f : β → α) (hs : ∀ a ∈ s, ∃ b ∈ X, f b = a) :
  ∃ t : Finset β, ↑t ⊆ X ∧ ∀ a ∈ s, ∃ b ∈ t, f b = a := by
  classical
  choose g hga hgb using hs;
  use Finset.univ.image (λ (a : { b // b ∈ s}) => g a.1 (by simp));
  constructor;
  . intro b hb;
    grind;
  . intro h b;
    simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, ↓existsAndEq];
    grind;

lemma lconj_mem_sumQuasiNormal {α : Type*} {Z : Logic α} {Γ : FormulaList α}
    (h : ∀ B ∈ Γ, B ∈ (LogicGL +ᴸ Z)) : (⋀Γ) ∈ (LogicGL +ᴸ Z) := by
  match Γ with
  | [] => exact Logic.sumQuasiNormal.mem₁ ProvableHilbert.top
  | [B] => simpa using h B (by simp)
  | B :: C :: Γ =>
    have hB := h B (by simp)
    have hrest := lconj_mem_sumQuasiNormal (Γ := C :: Γ) (fun D hD => h D (by simp only [List.mem_cons] at hD ⊢; tauto))
    show (B ⋏ ⋀(C :: Γ)) ∈ (LogicGL +ᴸ Z)
    exact Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ ProvableHilbert.andIntro) hB) hrest

lemma fconj_mem_sumQuasiNormal {α : Type*} {Z : Logic α} {Γ : FormulaFinset α}
    (h : ∀ B ∈ Γ, B ∈ (LogicGL +ᴸ Z)) : (⋀Γ) ∈ (LogicGL +ᴸ Z) := by
  show (FormulaList.conj Γ.toList) ∈ (LogicGL +ᴸ Z)
  apply lconj_mem_sumQuasiNormal
  intro B hB
  exact h B (Finset.mem_toList.mp hB)

omit [ℕ ⊧ₘ* T] in
open Classical in
theorem letterless_provabilityLogic (X : LetterlessFormulaSet) :
  ((@LogicGL α) +ᴸ ↑X) = T.provabilityLogicRelativeTo (T + (X.image (LetterlessFormula.standardInterpret T))) := by
  ext A;
  simp [FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo];
  constructor;
  . intro h;
    induction h with
    | mem₁ hA => intro f; exact Entailment.WeakerThan.pbl (LogicGL.arithmetical_soundness hA)
    | @mem₂ B hB =>
      intro f;
      obtain ⟨C, hC, rfl⟩ := hB;
      rw [LetterlessFormula.interpret_lift];
      apply Entailment.by_axm;
      simp only [FirstOrder.Theory.add_def];
      exact Or.inr ⟨C, hC, rfl⟩;
    | @mdp B C _ _ ihBC ihB => intro f; exact (ihBC f) ⨀ (ihB f)
    | @subst B s _ ihB => intro f; rw [Formula.interpret_subst]; exact ihB _
  . intro h;
    let f₀ := LogicGL.uniformRealization (α := α) T;
    obtain ⟨⟨s, hs_sub⟩, hs⟩ := LO.FirstOrder.Theory.compact_add_right (h f₀);
    obtain ⟨Δ, hΔ_sub, hΔ_cov⟩ := finite_preimage_choice s X (LetterlessFormula.standardInterpret T) (by
      intro σ hσ;
      obtain ⟨B, hB, hσ'⟩ := hs_sub hσ;
      exact ⟨B, hB, hσ'⟩);
    set C : Formula α := ⋀ (Δ.image LetterlessFormula.lift) with hC;
    have ha : (C 🡒 A) ∈ LogicGL := by
      apply (LogicGL.uniformRealization_spec (T := T) (C 🡒 A)).mp;
      show T ⊢ Formula.interpret f₀ C 🡒 Formula.interpret f₀ A;
      apply Entailment.C!_trans ?_ hs;
      apply Entailment.right_Fconj!_intro;
      intro σ hσ;
      obtain ⟨B, hBΔ, rfl⟩ := hΔ_cov σ hσ;
      rw [show (LetterlessFormula.standardInterpret T B) = Formula.interpret f₀ (LetterlessFormula.lift B) from
        (LetterlessFormula.interpret_lift (f := f₀)).symm];
      have hmem : (C 🡒 LetterlessFormula.lift B) ∈ LogicGL := by
        show ⊢ʰ (C 🡒 LetterlessFormula.lift B);
        have hsub : ({LetterlessFormula.lift B} : FormulaFinset α) ⊆ Δ.image LetterlessFormula.lift :=
          Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem _ hBΔ);
        simpa using ProvableHilbert.imp_fconj_fconj_of_subset (Γ := Δ.image LetterlessFormula.lift) hsub;
      exact LogicGL.arithmetical_soundness hmem;
    have hb : C ∈ ((@LogicGL α) +ᴸ X.lift) := by
      apply fconj_mem_sumQuasiNormal;
      intro B hB;
      obtain ⟨C, hCΔ, rfl⟩ := Finset.mem_image.mp hB;
      exact Logic.sumQuasiNormal.mem₂ (Set.mem_image_of_mem _ (hΔ_sub hCΔ));
    exact Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ ha) hb;

theorem LogicGLAlpha.eq_provabilityLogicRelativeTo {Alpha : Set ℕ}
  : LogicGLAlpha (α := α) Alpha = T.provabilityLogicRelativeTo (T + (Alpha.image (λ i => LetterlessFormula.standardInterpret T (TBB i)))) := by
  suffices (LetterlessFormula.standardInterpret T '' TBB '' Alpha) = (Alpha.image (λ i => LetterlessFormula.standardInterpret T (TBB i))) by
    exact this ▸ (letterless_provabilityLogic (X := Alpha.image TBB));
  ext i;
  simp;

theorem LogicGLAlphaOmega.eq_provabilityLogicRelativeTo
  : LogicGLAlphaOmega (α := α) = T.provabilityLogicRelativeTo (T + (Set.univ.image (λ i => LetterlessFormula.standardInterpret T (TBB i)))) := by
  apply LogicGLAlpha.eq_provabilityLogicRelativeTo;

end

end

end
