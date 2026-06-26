module

public import SeqPL.Formula
public import SeqPL.Formula.Letterless
public import SeqPL.Kripke.Rank
public import SeqPL.Logic.Basic
public import SeqPL.Logic.SumQuasiNormal

@[expose]
public section

namespace Set

variable {α : Type*} {s t : Set α} {a b : α}

abbrev Cofinite (s : Set α) := sᶜ.Finite
abbrev Coinfinite (s : Set α) := sᶜ.Infinite

lemma iff_cofinite_comp_finite : s.Cofinite ↔ sᶜ.Finite := by grind;
lemma iff_coinfinite_comp_infinite : s.Coinfinite ↔ sᶜ.Infinite := by grind;

@[push] lemma iff_cofinite_not_coinfinite : s.Cofinite ↔ ¬s.Coinfinite := by simp;
@[push] lemma iff_coinfinite_not_cofinite : s.Coinfinite ↔ ¬s.Cofinite := by simp;

@[push, grind =_] lemma iff_cofinite_compl : sᶜ.Cofinite ↔ s.Finite := by simp [Cofinite];
@[push, grind =_] lemma iff_coinfinite_compl : sᶜ.Coinfinite ↔ s.Infinite := by simp [Coinfinite];

@[grind ->]
lemma Cofinite.subset (h : s ⊆ t) : s.Cofinite → t.Cofinite := by
  intro h;
  apply Set.Finite.subset (s := sᶜ) h;
  tauto_set;

@[grind ->]
lemma Coinfinite.subset (h : t ⊆ s) : s.Coinfinite → t.Coinfinite := by
  contrapose!;
  suffices t.Cofinite → s.Cofinite by grind;
  grind;

@[simp, grind .]
lemma univ_cofinite : (Set.univ (α := α)).Cofinite := by simp [Set.Cofinite];

@[grind <=]
lemma cofinite_union_left (hs : s.Cofinite) : (s ∪ t).Cofinite := by
  grind [compl_union, Set.Finite.inter_of_left];

@[grind <=]
lemma cofinite_union_right (ht : t.Cofinite) : (s ∪ t).Cofinite := by
  exact (show (t ∪ s) = (s ∪ t) by tauto_set) ▸ cofinite_union_left ht;

end Set


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
  root := ⟨0, by sorry⟩

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
  | last => sorry;
  | cast i ih =>
    suffices (finiteLineModel.of i.castSucc).rank = (finiteLineModel.of i.succ).rank + 1 by grind;
    apply Model.iff_rank_eq.mpr;
    constructor;
    . sorry;
    . intro z;
      sorry;

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

lemma iff_GL_proves_spectrum_univ : A ∈ LogicGL _ ↔ spectrum A = Set.univ := by
  rw [Set.eq_univ_iff_forall];
  apply Iff.trans $ LogicGL_TFAE.out 0 4;
  constructor;
  . intro h n;
    apply spectrum_TFAE.out 1 0 |>.mp;
    intro κ _ _ M _ x rfl;
    apply @h κ _ M (by sorry);
  . intro h κ _ M _ x;
    sorry;

lemma iff_GL_proves_imp_GL_subset_spectrum : (A 🡒 B) ∈ LogicGL _ ↔ spectrum A ⊆ spectrum B := by
  apply Iff.trans iff_GL_proves_spectrum_univ;
  simp only [LetterlessFormula.spectrum_imp, Set.eq_univ_iff_forall, Set.mem_union, Set.mem_compl_iff];
  grind;

lemma iff_GL_proves_iff_GL_subset_spectrum : (A 🡘 B) ∈ LogicGL _ ↔ spectrum A = spectrum B := by
  suffices (A 🡘 B) ∈ LogicGL _ ↔ (A 🡒 B) ∈ LogicGL _ ∧ (B 🡒 A) ∈ LogicGL _ by
    grind [Set.Subset.antisymm_iff, iff_GL_proves_imp_GL_subset_spectrum];
  constructor;
  . intro h;
    sorry;
  . sorry;

lemma GL_proves_letterless_axiomWeakPoint3 : ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A))) ∈ LogicGL _ := by
  apply iff_GL_proves_spectrum_univ.mpr;
  grind;

end

abbrev LogicGLAlpha  (α) (Alpha : Set ℕ) := (LogicGL α) +ᴸ (Alpha.image TBB)
abbrev LogicGLAlphaω (α) := LogicGLAlpha α Set.univ
abbrev LogicGLBetaMinus (α) [DecidableEq α] (Beta : Set ℕ) (Beta_cofinite : Beta.Cofinite := by grind) :=
  (LogicGL α) +ᴸ ∼⋀(Beta_cofinite.toFinset.image TBB)

end
