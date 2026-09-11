module

public import ProvabilityLogic.Logic.SumQuasiNormal

@[expose]
public section

/-- The *normal* sum of two logics: `Logic.sumQuasiNormal` closed additionally under
necessitation. -/
@[grind]
inductive Logic.sumNormal (L₁ L₂ : Logic α) : Logic α
  | mem₁ {A}    : L₁ A → sumNormal L₁ L₂ A
  | mem₂ {A}    : L₂ A → sumNormal L₁ L₂ A
  | mdp  {A B}  : sumNormal L₁ L₂ (A 🡒 B) → sumNormal L₁ L₂ A → sumNormal L₁ L₂ B
  | subst {A s} : sumNormal L₁ L₂ A → sumNormal L₁ L₂ (A⟦s⟧)
  | nec  {A}    : sumNormal L₁ L₂ A → sumNormal L₁ L₂ (□A)
infix:50 " ⊕ᴸ " => Logic.sumNormal

namespace Logic.sumNormal

variable {L₁ L₂ : Logic α} {A B : Formula α} {s : Formula.Substitution α α}

@[grind .] lemma subset_L₁ : L₁ ⊆ (L₁ ⊕ᴸ L₂) := by apply Logic.sumNormal.mem₁;
@[grind .] lemma subset_L₂ : L₂ ⊆ (L₁ ⊕ᴸ L₂) := by apply Logic.sumNormal.mem₂;

lemma sumQuasiNormal_subset : (L₁ +ᴸ L₂) ⊆ (L₁ ⊕ᴸ L₂) := by
  intro A h;
  induction h with
  | mem₁ h => exact Logic.sumNormal.mem₁ h;
  | mem₂ h => exact Logic.sumNormal.mem₂ h;
  | mdp _ _ ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA;
  | subst _ ih => exact Logic.sumNormal.subst ih;

lemma imp_trans {C : Formula α}
    (htaut : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 A 🡒 C) ∈ L₁)
    (hAB : (A 🡒 B) ∈ L₁ ⊕ᴸ L₂) (hBC : (B 🡒 C) ∈ L₁ ⊕ᴸ L₂) : (A 🡒 C) ∈ L₁ ⊕ᴸ L₂ :=
  Logic.sumNormal.mdp (Logic.sumNormal.mdp (Logic.sumNormal.mem₁ htaut) hAB) hBC

end Logic.sumNormal

end
