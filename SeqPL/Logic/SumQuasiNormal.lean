module

public import SeqPL.Logic.Basic
public import SeqPL.Formula.Letterless

@[expose]
public section

@[grind]
inductive Logic.sumQuasiNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {A}    : L₁ A → sumQuasiNormal L₁ L₂ A
  | mem₂ {A}    : L₂ A → sumQuasiNormal L₁ L₂ A
  | mdp  {A B}  : sumQuasiNormal L₁ L₂ (A 🡒 B) → sumQuasiNormal L₁ L₂ A → sumQuasiNormal L₁ L₂ B
  | subst {A s} : sumQuasiNormal L₁ L₂ A → sumQuasiNormal L₁ L₂ (A⟦s⟧)
infix:50 " +ᴸ " => Logic.sumQuasiNormal

namespace Logic.sumQuasiNormal

variable {L₁ L₂ : Logic α} {A B : Formula α} {s : Formula.Substitution α}

@[grind .] lemma subset_L₁ : L₁ ⊆ (L₁ +ᴸ L₂) := by apply Logic.sumQuasiNormal.mem₁;
@[grind .] lemma subset_L₂ : L₂ ⊆ (L₁ +ᴸ L₂) := by apply Logic.sumQuasiNormal.mem₂;

lemma iff_subset : (L +ᴸ X) ⊆ (L +ᴸ Y) ↔ X ⊆ (L +ᴸ Y) := by
  constructor;
  . intro h A hA;
    apply h;
    apply Logic.sumQuasiNormal.mem₂;
    exact hA;
  . intro h A hA;
    induction hA with
    | mem₁ hA =>
      apply Logic.sumQuasiNormal.mem₁;
      exact hA
    | mem₂ hA =>
      apply h hA;
    | mdp _ _ ihAB ihA =>
      exact Logic.sumQuasiNormal.mdp ihAB ihA;
    | subst h ih =>
      apply Logic.sumQuasiNormal.subst ih;

end Logic.sumQuasiNormal


abbrev Logic.addQuasiNormal (L : Logic α) (A : Formula α) := L +ᴸ {A}
infixl:50 " +ᴸ " => Logic.addQuasiNormal


abbrev LogicS (α) := (LogicGL α) +ᴸ ({ □A 🡒 A | A })

abbrev LogicD (α) := (LogicGL α) +ᴸ (insert (∼□⊥) { □(□A ⋎ □B) 🡒 (□A ⋎ □B) | (A) (B) })

lemma LogicS_subset_LogicD : LogicD α ⊆ LogicS α := by
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
