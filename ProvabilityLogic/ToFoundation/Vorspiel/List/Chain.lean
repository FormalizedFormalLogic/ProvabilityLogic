module

public import Foundation.Vorspiel.List.Chain

@[expose]
public section

namespace List

variable {α : Type*} {R : α → α → Prop}

/-- In a chain under an irreflexive transitive relation, the last element of a proper
prefix relates to the last element of the whole chain. -/
lemma rel_getLast_getLast_of_prefix [DecidableEq α] [IsTrans α R] [Std.Irrefl R] {l₁ l₂ : List α}
  (hc : l₂.IsChain R) (hp : l₁ <+: l₂) (hlt : l₁.length < l₂.length)
  (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
  R (l₁.getLast h₁) (l₂.getLast h₂) := by
  apply List.rel_getLast_of_isChain_trans hc h₂;
  . exact hp.subset (List.getLast_mem h₁);
  . obtain ⟨t, ht⟩ := hp;
    have htne : t ≠ [] := by
      rintro rfl;
      simp only [List.append_nil] at ht;
      rw [ht] at hlt;
      omega;
    have hd : l₁.Disjoint t := List.disjoint_of_nodup_append (ht ▸ hc.noDup_of_irrefl_trans);
    have he : l₂.getLast h₂ = t.getLast htne := by
      rw [show l₂.getLast h₂ = (l₁ ++ t).getLast (ht ▸ h₂) by simp [ht]];
      exact List.getLast_append_of_ne_nil _ htne;
    rw [he];
    intro e;
    exact hd (e ▸ List.getLast_mem h₁) (List.getLast_mem htne);

end List

end
