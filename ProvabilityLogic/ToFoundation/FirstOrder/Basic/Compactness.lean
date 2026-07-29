module

public import Foundation.FirstOrder.Basic.Calculus

/-!
# Compactness of first-order provability for theory unions

Corollaries of `Entailment.Compact (Theory L)` (from `Foundation.FirstOrder.Basic.Calculus`)
for provability from a union of two theories: a proof from `T ∪ U` already follows from `T`
(resp. `U`) together with a finite conjunction of sentences drawn from `U` (resp. `T`).

Compactness of first-order provability is textbook material; there is no dedicated citation
for it in `references.bib`.
-/

@[expose] public section

namespace LO.FirstOrder.Theory

/-- Compactness: a proof from a theory factors through a finite subtheory, presented as a
finite conjunction implying the goal. -/
private lemma compact_conj
  {L : FirstOrder.Language} [L.DecidableEq] {T : FirstOrder.Theory L} {φ : FirstOrder.Sentence L}
  (h : T ⊢ φ) : ∃ (s : { s : Finset (FirstOrder.Sentence L) // ↑s ⊆ T }), (∅ : FirstOrder.Theory L) ⊢ s.1.conj 🡒 φ := by
  obtain ⟨𝓕, h𝓕sub, h𝓕fin, h𝓕⟩ := LO.Entailment.Compact.finite_provable h
  have h𝓕fin' : 𝓕.Finite := by simpa using h𝓕fin
  set s : Finset (FirstOrder.Sentence L) := h𝓕fin'.toFinset with hs_def
  have hcoe : (↑s : FirstOrder.Theory L) = 𝓕 := h𝓕fin'.coe_toFinset
  have h𝓕' : (↑s : FirstOrder.Theory L) ⊢ φ := by rw [hcoe]; exact h𝓕
  have H : (↑(insert s.conj ∅ : FirstOrder.Theory L)) ⊢* (↑s : FirstOrder.Theory L) := by
    intro ψ hψ
    exact LO.Entailment.left_Fconj!_intro (by simpa using hψ) ⨀ (LO.Entailment.by_axm (by simp))
  exact ⟨⟨s, hcoe ▸ h𝓕sub⟩,
    LO.Entailment.Deduction.of_insert!
      (LO.Entailment.StrongCut.cut! (𝓣 := (↑s : FirstOrder.Theory L)) H h𝓕')⟩

/-- Compactness for a theory union, isolating the contribution of `U`. -/
lemma compact_add_right
  {L : FirstOrder.Language} [L.DecidableEq] {T U : FirstOrder.Theory L}
  [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)] {φ : FirstOrder.Sentence L}
  (h : (T ∪ U) ⊢ φ) : ∃ (s : { s : Finset (FirstOrder.Sentence L) // ↑s ⊆ U }), T ⊢ s.1.conj 🡒 φ := by
  obtain ⟨⟨s, hsTU⟩, hs⟩ := LO.FirstOrder.Theory.compact_conj h;
  let sT := { ψ ∈ s | ψ ∈ T };
  let sU := { ψ ∈ s | ψ ∈ U };
  use ⟨sU, λ _ => by simp [sU]⟩;
  have : (∅ : FirstOrder.Theory _) ⊢ sT.conj 🡒 sU.conj 🡒 φ := LO.Entailment.CK!_iff_CC!.mp $ LO.Entailment.C!_trans LO.Entailment.CKFconjFconjUnion! $ by
    have : sT ∪ sU = s:= by
      ext ψ;
      constructor;
      . grind;
      . intro hψ; rcases hsTU hψ with (hψT | hψU) <;> grind;
    rwa [this];
  apply LO.Entailment.mdp! $ LO.Entailment.Axiomatized.weakening! (λ _ => by simp) this;
  apply LO.Entailment.FConj!_iff_forall_provable.mpr;
  intro ψ hψ;
  apply LO.Entailment.by_axm;
  simp_all [sT];

/-- Compactness for a theory union, isolating the contribution of `T`. -/
lemma compact_add_left
  {L : FirstOrder.Language} [L.DecidableEq] {T U : FirstOrder.Theory L}
  [DecidablePred (· ∈ T)] [DecidablePred (· ∈ U)] {φ : FirstOrder.Sentence L}
  (h : (T ∪ U) ⊢ φ) : ∃ (s : { s : Finset (FirstOrder.Sentence L) // ↑s ⊆ T }), U ⊢ s.1.conj 🡒 φ := by
  rw [show (T ∪ U = U ∪ T) from Set.union_comm T U] at h
  simpa using LO.FirstOrder.Theory.compact_add_right h;

end LO.FirstOrder.Theory
