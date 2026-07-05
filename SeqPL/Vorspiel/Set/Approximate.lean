module

public import Mathlib.Data.Set.Countable
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Fintype.Sigma

@[expose]
public section

/-!
  Ports necessary lemmas from `Foundation.Vorspiel.Set.Basic` / `Foundation.Vorspiel.Finset.Basic`.
-/

namespace Set

variable {α : Type*} {s t : Set α} {a : α}

lemma ssubset_of_subset_ne (h : s ⊆ t) (hne : s ≠ t) : s ⊂ t := by
  constructor;
  . assumption;
  . revert hne;
    contrapose!;
    intro _;
    apply Set.eq_of_subset_of_subset <;> assumption;

/--
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539292838
-/
lemma infinitely_finset_approximate (count : s.Countable) (inf : s.Infinite) (ha : a ∈ s) :
  ∃ f : ℕ → Finset α, ((f 0) = {a}) ∧ (∀ i, f i ⊂ f (i + 1)) ∧ (∀ i, ↑(f i) ⊆ s) ∧ (∀ b ∈ s, ∃ i, b ∈ f i) := by
  let X' := s \ {a}
  have count' : Countable X' := (count.mono Set.sdiff_subset).to_subtype
  have inf' : Infinite X' := (inf.sdiff (Set.finite_singleton a)).to_subtype
  obtain ⟨eq⟩ : Nonempty (Nat ≃ X') := nonempty_equiv_of_countable
  use fun n => Finset.cons a ((Finset.range n).map
    (eq.toEmbedding.trans (Function.Embedding.subtype _)))
    (by
      suffices ∀ x < n, ¬↑(eq x) = a by simpa;
      intro x _
      exact (eq x).prop.right)
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [Finset.ssubset_def]
  · suffices ∀ (i : ℕ), Set.Iio i ⊆ (fun a ↦ ↑(eq a)) ⁻¹' s by simpa [Set.insert_subset_iff, ha]
    intro i x _;
    exact (eq x).prop.left
  · intro b hb
    by_cases hba : b = a
    · exact ⟨0, by simp [hba]⟩
    · use eq.symm ⟨b, hb, hba⟩ + 1
      apply Finset.mem_cons_of_mem;
      suffices ∃ a_1 < eq.symm ⟨b, _⟩ + 1, ↑(eq _) = b by simpa;
      exact ⟨eq.symm ⟨b, hb, hba⟩, by simp⟩

end Set


namespace Finset

variable {α : Type*}

/--
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539367015
-/
lemma no_ssubset_descending_chain {f : ℕ → Finset α} : ¬(∀ i, ∃ j > i, f j ⊂ f i) := by
  intro h
  have n := 0
  induction hf : f n using WellFoundedLT.fix generalizing n with subst hf | _ _ ih
  obtain ⟨m, -, hy⟩ := h n
  exact ih (f m) hy m rfl

end Finset


/-- Any finite subset `s` of the image `f '' X` lifts to a finite subset `t ⊆ X` covering the
preimages of `s` under `f`. -/
lemma finite_preimage_choice {α β : Type*} (s : Finset α) (X : Set β) (f : β → α)
    (hs : ∀ a ∈ s, ∃ b ∈ X, f b = a) :
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

end
