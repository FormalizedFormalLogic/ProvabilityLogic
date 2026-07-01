module

public import SeqPL.Logic.Basic
public import SeqPL.Formula.Letterless

@[expose]
public section

lemma ProvableHilbert.subst {A : Formula α} {s : Formula.Substitution α} (h : ⊢ʰ A) : ⊢ʰ A⟦s⟧ := by
  induction h using ProvableHilbert.rec with
  | prop1 => exact ProvableHilbert.prop1
  | prop2 => exact ProvableHilbert.prop2
  | prop3 => exact ProvableHilbert.prop3
  | modalK => exact ProvableHilbert.modalK
  | modal4 => exact ProvableHilbert.modal4
  | modalL => exact ProvableHilbert.modalL
  | mdp h₁ h₂ ih₁ ih₂ => exact ProvableHilbert.mdp ih₁ ih₂
  | nec h ih => exact ProvableHilbert.nec ih

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

end
