module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.S.Basic

@[expose]
public section

abbrev LogicD {α} : Logic α := (LogicGL) +ᴸ (insert (∼□⊥) { □(□A ⋎ □B) 🡒 (□A ⋎ □B) | (A) (B) })

lemma LogicS_subset_LogicD : LogicD (α := α) ⊆ LogicS := by
  intro A h;
  induction h with
  | mem₁ h => apply Logic.sumQuasiNormal.mem₁; exact h
  | mdp h₁ h₂ ih₁ ih₂ => apply Logic.sumQuasiNormal.mdp; exact ih₁; exact ih₂
  | subst h ih => apply Logic.sumQuasiNormal.subst; exact ih
  | mem₂ h =>
    rcases h with (rfl | ⟨A, B, rfl⟩);
    . apply Logic.sumQuasiNormal.mem₂;
      use ⊥;
    . apply Logic.sumQuasiNormal.mem₂;
      use (□A ⋎ □B);

end
