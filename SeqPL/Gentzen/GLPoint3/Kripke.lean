module

public import SeqPL.Gentzen.GLPoint3.Basic
public import SeqPL.Gentzen.Kripke
public import SeqPL.Kripke.Linearity

@[expose]
public section

variable {κ : Type u} [Nonempty κ]
         {α : Type v} [DecidableEq α]
         {M : Model κ α}

namespace Model

variable {x : M.World} {D : Formula α}

/-- On a linear (`GLPoint3`) frame, if `x` refutes `□A` for every `A ∈ Δ`, some successor `w`
of `x` refutes exactly a nonempty `S ⊆ Δ`, while forcing `□A` for every `A ∈ S` and refuting
`□A` for every `A ∈ Δ \ S`. This is the witness driving the soundness of `boxGLPoint3`: at `w`
the premise sequent for `S` is falsified. -/
lemma exists_linear_witness [M.IsGLPoint3] :
  ∀ {Δ : FormulaFinset α}, Δ.Nonempty → (∀ A ∈ Δ, x ⊮ □A) →
  ∃ w, x ≺ w ∧ ∃ S ⊆ Δ, S.Nonempty ∧ (∀ A ∈ S, w ⊮ A ∧ w ⊩ □A) ∧ (∀ A ∈ Δ \ S, w ⊮ □A) := by
  intro Δ;
  induction Δ using Finset.strongInductionOn with
  | _ Δ ih =>
  intro hΔne hx;
  obtain ⟨D, hD⟩ := hΔne;
  -- The successor of `x` refuting `D` deepest along `≺` also forces `□D`.
  have terminalBoxRefuter (D : Formula α) (hxD : x ⊮ □D) :
    ∃ z, x ≺ z ∧ z ⊮ D ∧ z ⊩ □D := by
    obtain ⟨z₀, hxz₀, hz₀⟩ := Model.World.not_forces_box.mp hxD;
    obtain ⟨z, ⟨hxz, hzD⟩, hzterm⟩ := M.terminalOf {z | x ≺ z ∧ z ⊮ D} ⟨z₀, hxz₀, hz₀⟩;
    refine ⟨z, hxz, hzD, fun z' hzz' => ?_⟩;
    by_contra hz'D;
    exact hzterm z' ⟨_root_.trans hxz hzz', hz'D⟩ hzz';
  by_cases hΔ' : (Δ.erase D).Nonempty;
  · obtain ⟨w', hxw', S', hS'sub, hS'ne, hS', hDS'⟩ :=
      ih (Δ.erase D) (Finset.erase_ssubset hD) hΔ' (fun A hA => hx A (Finset.mem_of_mem_erase hA));
    by_cases hD1 : w' ⊮ □D;
    · -- `D` joins the already-refuted complement, `S'` is unchanged.
      refine ⟨w', hxw', S', hS'sub.trans (Finset.erase_subset _ _), hS'ne, hS', fun A hA => ?_⟩;
      rcases Finset.mem_sdiff.mp hA with ⟨hAΔ, hAS'⟩;
      by_cases hAD : A = D;
      · subst hAD; exact hD1;
      · exact hDS' A (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hAD, hAΔ⟩, hAS'⟩);
    · push Not at hD1;
      by_cases hD2 : w' ⊮ D;
      · -- `w'` also refutes `D`, so `D` joins `S'`.
        refine ⟨w', hxw', insert D S',
          Finset.insert_subset_iff.mpr ⟨hD, hS'sub.trans (Finset.erase_subset _ _)⟩,
          ⟨D, Finset.mem_insert_self _ _⟩, fun A hA => ?_, fun A hA => ?_⟩;
        · rcases Finset.mem_insert.mp hA with rfl | hA;
          · exact ⟨hD2, hD1⟩;
          · exact hS' A hA;
        · apply hDS' A;
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or] at hA ⊢;
          tauto;
      · -- `w'` forces `D`: descend past `w'` to a deeper world refuting `D` (and everything else).
        push Not at hD2;
        obtain ⟨z, hxz, hzD, hzBoxD⟩ := terminalBoxRefuter D (hx D hD);
        have hzw' : z ≺ w' := by
          rcases Model.linear hxw' hxz with h1 | h2 | h3;
          · exact absurd (hD1 z h1) hzD;
          · rw [h2] at hD2; exact absurd hD2 hzD;
          · exact h3;
        refine ⟨z, hxz, {D}, Finset.singleton_subset_iff.mpr hD, ⟨D, Finset.mem_singleton_self _⟩,
          fun A hA => by rw [Finset.mem_singleton] at hA; subst hA; exact ⟨hzD, hzBoxD⟩, ?_⟩;
        rw [Finset.sdiff_singleton_eq_erase];
        intro A hA;
        by_cases hAS' : A ∈ S';
        · exact fun hzA => (hS' A hAS').1 (hzA w' hzw');
        · obtain ⟨t, hw't, htA⟩ := Model.World.not_forces_box.mp (hDS' A (Finset.mem_sdiff.mpr ⟨hA, hAS'⟩));
          exact fun hzA => htA (hzA t (_root_.trans hzw' hw't));
  · -- Base case: `Δ = {D}`.
    have hΔeq : Δ = {D} := by
      rw [Finset.not_nonempty_iff_eq_empty] at hΔ';
      ext A;
      simp only [Finset.mem_singleton];
      constructor;
      · intro hA;
        by_contra hAD;
        exact absurd (Finset.mem_erase.mpr ⟨hAD, hA⟩) (hΔ' ▸ Finset.notMem_empty A);
      · rintro rfl; exact hD;
    subst hΔeq;
    obtain ⟨z, hxz, hzD, hzBoxD⟩ := terminalBoxRefuter D (hx D (Finset.mem_singleton_self _));
    exact ⟨z, hxz, {D}, subset_refl _, ⟨D, Finset.mem_singleton_self _⟩,
      fun A hA => by rw [Finset.mem_singleton] at hA; subst hA; exact ⟨hzD, hzBoxD⟩,
      fun A hA => by simp at hA⟩;

variable {Γ Δ : FormulaFinset α} {A : Formula α}

open Model.World in
/-- Soundness of `boxGLPoint3`: on a linear (`GLPoint3`) model, if every premise sequent
`□Γ, Γ, □S ⟹ S, □(Δ \ S)` (`S ⊆ Δ` nonempty) is valid, so is the conclusion `□Γ ⟹ □Δ`. -/
lemma validate_gentzen_boxGLPoint3 [M.IsGLPoint3] (hΔ : Δ.Nonempty)
  (h : ∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty → M ⊧ ((Γ.box ∪ Γ ∪ S.box) ⟹ (S ∪ (Δ \ S).box))) :
  M ⊧ (Γ.box ⟹ Δ.box) := by
  intro x hxante;
  by_contra hcon;
  push Not at hcon;
  have hx : ∀ A ∈ Δ, x ⊮ □A := fun A hA => hcon (□A) (Finset.mem_image_of_mem _ hA);
  obtain ⟨w, hxw, S, hSsub, hSne, hSforces, hcompl⟩ := exists_linear_witness hΔ hx;
  have hwante : ∀ C ∈ Γ.box ∪ Γ ∪ S.box, w ⊩ C := by
    intro C hC;
    rcases Finset.mem_union.mp hC with hC | hCS;
    rcases Finset.mem_union.mp hC with hCΓbox | hCΓ;
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hCΓbox;
      exact fun y hwy => hxante (□B) (Finset.mem_image_of_mem _ hB) y (_root_.trans hxw hwy);
    · exact hxante (□C) (Finset.mem_image_of_mem _ hCΓ) w hxw;
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hCS;
      exact (hSforces B hB).2;
  obtain ⟨D, hD, hwD⟩ := h S hSsub hSne w hwante;
  rcases Finset.mem_union.mp hD with hDS | hDbox;
  · exact (hSforces D hDS).1 hwD;
  · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hDbox;
    exact hcompl B hB hwD;

end Model
