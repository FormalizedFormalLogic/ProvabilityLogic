module

public import Foundation.FirstOrder.Basic.Calculus

/-!
# Compactness of first-order provability for theory unions

Corollaries of `Entailment.Compact (Theory L)` for provability from a union of two
theories: a proof from `T ∪ U` already follows from `T` (resp. `U`) together with a finite
conjunction of sentences drawn from `U` (resp. `T`).
-/

@[expose] public section

namespace FFL.FirstOrder.Theory

variable {L : Language} [L.DecidableEq] {T U : Theory L}
  [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)] {φ : Sentence L}

omit [DecidablePred (· ∈ T)] in
private lemma compact_conj (h : T ⊢ φ) :
  ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ T }), (∅ : Theory L) ⊢ s.1.conj 🡒 φ := by
  obtain ⟨𝓕, h𝓕sub, h𝓕fin, h𝓕⟩ := FFL.Entailment.Compact.finite_provable h;
  have h𝓕fin' : 𝓕.Finite := by simpa using h𝓕fin;
  set s : Finset (Sentence L) := h𝓕fin'.toFinset with hs_def;
  have hcoe : (↑s : Theory L) = 𝓕 := h𝓕fin'.coe_toFinset;
  have h𝓕' : (↑s : Theory L) ⊢ φ := by rw [hcoe]; exact h𝓕;
  have H : (↑(insert s.conj ∅ : Theory L)) ⊢* (↑s : Theory L) := by
    intro ψ hψ;
    exact FFL.Entailment.left_Fconj_intro (by simpa using hψ) ⨀ (FFL.Entailment.by_axm (by simp));
  exact ⟨⟨s, hcoe ▸ h𝓕sub⟩,
    FFL.Entailment.Deduction.of_insert!
      (FFL.Entailment.StrongCut.cut! (𝓣 := (↑s : Theory L)) H h𝓕')⟩

lemma compact_add_right (h : (T ∪ U) ⊢ φ) :
  ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ U }), T ⊢ s.1.conj 🡒 φ := by
  obtain ⟨⟨s, hsTU⟩, hs⟩ := compact_conj h;
  let sT := { ψ ∈ s | ψ ∈ T };
  let sU := { ψ ∈ s | ψ ∈ U };
  use ⟨sU, λ _ => by simp [sU]⟩;
  have : (∅ : Theory _) ⊢ sT.conj 🡒 sU.conj 🡒 φ :=
    FFL.Entailment.CK_iff_CC.mp $ FFL.Entailment.C_trans FFL.Entailment.CKFconjFconjUnion $ by
      have : sT ∪ sU = s:= by
        ext ψ;
        constructor;
        . grind;
        . intro hψ; rcases hsTU hψ with (hψT | hψU) <;> grind;
      rwa [this];
  apply FFL.Entailment.mdp $ FFL.Entailment.Axiomatized.weakening! (λ _ => by simp) this;
  apply FFL.Entailment.FConj_iff_forall_provable.mpr;
  intro ψ hψ;
  apply FFL.Entailment.by_axm;
  simp_all [sT];

lemma compact_add_left (h : (T ∪ U) ⊢ φ) :
  ∃ (s : { s : Finset (Sentence L) // ↑s ⊆ T }), U ⊢ s.1.conj 🡒 φ := by
  rw [show (T ∪ U = U ∪ T) from Set.union_comm T U] at h;
  simpa using compact_add_right h;

end FFL.FirstOrder.Theory
