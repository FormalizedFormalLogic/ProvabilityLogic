module

public import Foundation.Vorspiel.Set.Basic

@[expose]
public section

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
