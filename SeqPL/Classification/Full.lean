module

public import SeqPL.Classification.Letterless

@[expose]
public section

universe u
variable {α : Type u}


namespace Formula

end Formula


namespace Formula

variable {n : ℕ} {A B : Formula α}

@[grind]
def trace (A : Formula α) : Set ℕ := { n |
  ∃ κ : Type u, ∃ _ : Nonempty κ, ∃ M : RootedModel κ α, ∃ _ : Fintype M.World, ∃ _ : M.IsGL,
  (M.height = n ∧ M.root.1 ⊮ A)
}

@[grind =]
lemma iff_mem_trace :
  n ∈ A.trace ↔
  ∃ κ : Type u, ∃ _ : Nonempty κ, ∃ M : RootedModel κ α, ∃ _ : Fintype M.World, ∃ _ : M.IsGL, M.height = n ∧ M.root.1 ⊮ A := by
  grind;

@[grind =]
lemma iff_mem_not_trace :
  n ∉ A.trace ↔
  ∀ κ : Type u, ∀ _ : Nonempty κ, ∀ M : RootedModel κ α, ∀ _ : Fintype M.World, ∀ _ : M.IsGL, M.height = n → M.root.1 ⊩ A := by
  grind;

variable {α : Type 0} {A B : Formula α}

@[grind =]
lemma eq_trace_toLetterless_trace (hA : A.Letterless) : A.trace = LetterlessFormula.trace (A.toLetterless hA) := by
  ext n;

  apply Iff.trans ?_ $ spectrum_TFAE.out 1 0 |>.not;
  push Not;
  rw [iff_mem_trace];
  constructor;
  . sorry;
  . rintro ⟨κ, _, _, M, _, x, rfl, h⟩;
    use κ, ‹_›;
    sorry;

@[simp, grind =]
lemma trace_top : (⊤ : Formula α).trace = ∅ := by grind;

@[simp, grind =]
lemma trace_bot : (⊥ : Formula α).trace = Set.univ := by
  rw [eq_trace_toLetterless_trace (A := ⊥) (by simp [Letterless])];
  exact LetterlessFormula.trace_bot;

@[simp, grind =]
lemma trace_and : (A ⋏ B).trace = A.trace ∪ B.trace := by ext n; grind;

@[simp, grind =]
lemma trace_lconj {Γ : FormulaList α} : (⋀Γ).trace = ⋃ A ∈ Γ, A.trace := by
  match Γ with
  | [] => simp;
  | [A] => simp;
  | A :: B :: Γ => simp [FormulaList.conj, trace_and, trace_lconj];

@[simp, grind =]
lemma trace_fconj {Γ : FormulaFinset α} : (⋀Γ).trace = ⋃ A ∈ Γ, A.trace := by
  simp [FormulaFinset.conj, trace_lconj]

lemma subset_trace_of_provable_GL (h : A 🡒 B ∈ LogicGL _) : B.trace ⊆ A.trace := by
  intro n;
  simp only [iff_mem_trace];
  rintro ⟨κ, _, M, _, _, rfl, hB⟩;
  use κ, ‹_›, M, ‹_›, ‹_›, rfl;
  revert hB;
  contrapose!;
  show M.root.1 ⊩ A 🡒 B;
  sorry;

end Formula



end
