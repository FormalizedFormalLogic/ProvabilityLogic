module

public import SeqPL.Kripke.Rank
public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.ProvabilityLogic.Interpret
public import SeqPL.Vorspiel.Set.Cofinite
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
lemma spectrum_finite_or_cofinite : A.spectrum.Finite ∨ A.spectrum.Cofinite := by
  induction A with
  | atom a => grind;
  | bot => grind;
  | imp A B ihA ihB =>
    simp only [spectrum_imp, Set.finite_union];
    rcases ihA with (hA | hA) <;> rcases ihB with (hB | hB) <;> grind;
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
lemma trace_finite_or_cofinite : (trace A).Finite ∨ (trace A).Cofinite := by
  grind [trace, spectrum_finite_or_cofinite];

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
    sorry;
  . sorry;

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
  have := TBB_normalization_of_finite_trace (A := ∼A) (by grind);
  sorry;

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

@[grind <=]
lemma spectrum_subset_of_mem (h : A ∈ X) : X.spectrum ⊆ A.spectrum := by
  intro i hi;
  apply Set.mem_iInter.mp hi A;
  grind;

variable [ℕ ⊧ₘ* T]

@[simp, grind =_]
lemma eq_trace_singleton : trace {A} = LetterlessFormula.trace A := by
  rw [eq_trace];
  simp;

lemma eq_TBB_trace : s = LetterlessFormulaSet.trace (TBB '' s) := by simp [eq_trace]

@[simp, grind =]
lemma eq_trace_TBB_trace : X.trace = LetterlessFormulaSet.trace (TBB '' X.trace) := eq_TBB_trace

@[simp, grind .]
lemma regular_TBB_set {X : Set ℕ} : LetterlessFormulaSet.Regular T (X.image TBB) := by grind;

@[simp, grind =]
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
lemma trace_cofinite_of_singular (h : X.Singular T) : X.trace.Cofinite := by
  obtain ⟨A, hA, h⟩ := iff_singular_exists_singular.mp h;
  suffices X.spectrum ⊆ A.spectrum by
    simp [LetterlessFormulaSet.trace, Set.Cofinite]
    apply Set.Finite.subset ?_ this;
    grind;
  grind;

end LetterlessFormulaSet

section

variable {α} {X Y : LetterlessFormulaSet} {A : LetterlessFormula}

lemma iff_GL_sumQuasiNormal_proves_subset_spectrum (hSR : X.Singular T ∨ A.Regular T)
  : ↑A ∈ ((@LogicGL α) +ᴸ X) ↔ X.spectrum ⊆ A.spectrum := by
  sorry;

lemma iff_subset_sumQuasiNormal_subset_spectrum (hSR : X.Regular T ∨ Y.Singular T)
  : ((@LogicGL α) +ᴸ X) ⊆ ((@LogicGL α) +ᴸ Y) ↔ Y.spectrum ⊆ X.spectrum := by calc
  -- _ ↔ ∀ A ∈ Y, A ∈ ((LogicGL) +ᴸ Y) → A ∈ ((LogicGL) +ᴸ X) := by grind;
  _ ↔ ∀ (A : LetterlessFormula), A ∈ X → ↑A ∈ ((@LogicGL α) +ᴸ Y) := by
    rw [Logic.sumQuasiNormal.iff_subset];
    constructor;
    . intro h A hA;
      apply @h A (by sorry);
    . intro h;
      sorry;
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
abbrev LogicGLAlphaω {α} : Logic α := LogicGLAlpha Set.univ
abbrev LogicGLBetaMinus {α} [DecidableEq α] (Beta : Set ℕ) (Beta_cofinite : Beta.Cofinite := by grind) : Logic α := (@LogicGL α) +ᴸ (LetterlessFormulaSet.lift { TBBMinus _ Beta_cofinite })



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
  : ((@LogicGL α) +ᴸ ↑X) = LogicGLAlpha X.trace := by
  apply iff_eq_sumQuasiNormal_eq_trace (T := T) (by grind) |>.mpr;
  grind;

lemma eq_letterless_GL_quasiNormal_extension_GLBetaMinus_of_singular [DecidableEq α] (X_singular : X.Singular T)
  : ((@LogicGL α) +ᴸ ↑X) = LogicGLBetaMinus (α := α) X.trace := by
  apply iff_eq_sumQuasiNormal_eq_trace (T := T) (by grind) |>.mpr;
  grind;

/--
  Quasi-normal `GL` extension by letterless formula set `X` is
  either `LogicGLAlpha X.trace` (when `X` is regular, so `X.trace` is finite) or `LogicGLBetaMinus X.trace` (when `X` is singular, so `X.trace` is cofinite)
-/
theorem eq_letterless_quasiNormal_GL_extension [DecidableEq α] :
  (∃ _ : X.Regular T, ((@LogicGL α) +ᴸ ↑X) = LogicGLAlpha X.trace) ∨
  (∃ _ : X.Singular T, ((@LogicGL α) +ᴸ ↑X) = LogicGLBetaMinus X.trace) := by
  by_cases h : X.Regular T;
  . left;
    exact ⟨h, eq_letterless_GL_quasiNormal_extension_GLAlpha_of_regular h⟩;
  . right;
    exact ⟨h, eq_letterless_GL_quasiNormal_extension_GLBetaMinus_of_singular h⟩;

end
end

end
