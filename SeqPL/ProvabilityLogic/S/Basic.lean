module

public import SeqPL.Logic.S.Basic
public import SeqPL.ProvabilityLogic.GL.Basic

/-!
# Arithmetical soundness and completeness of Logic S

Port of `Foundation.ProvabilityLogic.S.Soundness` and
`Foundation.ProvabilityLogic.S.Completeness` (Theorem 3 in [AB05]) to SeqPL.

Main results:
- `LogicS.arithmetical_soundness`: if `A ∈ LogicS` then `ℕ↓[ℒₒᵣ] ⊧ f A` for every realization `f`.
- `LogicS.arithmetical_completeness_iff`:
  `A ∈ LogicS ↔ ∀ f : StandardRealization α T, ℕ↓[ℒₒᵣ] ⊧ f A` for any sound theory `T`.
- `LogicS.eq_provabilityLogicRelativeTo_TA`: `LogicS` is the provability logic of `T`
  relative to the true arithmetic `𝗧𝗔`.

Unlike Foundation's `GL_S_TFAE` (which proves 1 → 2 → 3 → 1), the two directions here are
independent: soundness is proved by induction via `LogicS.substlessInduction`, and
completeness is reduced to the Kripke-semantical characterization
`LogicS.iff_provable_S_provable_GL` together with the Solovay construction
(`SolovaySentences.rfl_mainlemma` and `solovay_root_sound`).
-/

@[expose] public section

open Classical
open LO
open LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open LO.FirstOrder.Arithmetic
open Model Model.World

variable {κ : Type u} [Nonempty κ]
         {α : Type u}
         {A B : Formula α}

namespace LogicS

section soundness

variable {T₀ T : FirstOrder.ArithmeticTheory} [T₀ ⪯ T] [Diagonalization T₀]
         {𝔅 : Provability T₀ T} [𝔅.HBL] [ℕ↓[ℒₒᵣ] ⊧* T] [𝔅.SoundOn ℕ]

/--
  **Arithmetical soundness of S**: every theorem of `S` is true in the standard model `ℕ`
  under every realization of a provability predicate for a sound theory.

  - [AB05, Theorem 3 (soundness half)]
-/
theorem arithmetical_soundness (h : A ∈ LogicS) (f : Realization α 𝔅) : ℕ↓[ℒₒᵣ] ⊧ f A := by
  induction h using LogicS.substlessInduction with
  | provable_GL h =>
    exact models_of_provable inferInstance (LogicGL.arithmetical_soundness' h);
  | axiomT =>
    simp only [Formula.interpret, models_iff, LO.Semantics.Imp.models_imply];
    intro h;
    exact models_of_provable inferInstance (𝔅.sound_on h);
  | mdp ihAB ihA =>
    simp only [Formula.interpret, models_iff, LO.Semantics.Imp.models_imply] at ihAB;
    exact ihAB ihA;

end soundness


section completeness

open LO.FirstOrder.ProvabilityAbstraction.Provability
open LO.FirstOrder.Arithmetic.Bootstrapping

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]

/--
  **Arithmetical completeness of S**: if `A` is true in `ℕ` under every standard
  realization for `T`, then `A ∈ LogicS`.

  - [AB05, Theorem 3 (completeness half)]
-/
theorem arithmetical_completeness [DecidableEq α]
    (H : ∀ f : StandardRealization α T, ℕ↓[ℒₒᵣ] ⊧ f A) : A ∈ LogicS := by
  -- If `A ∉ LogicS` then by `iff_provable_S_provable_GL` the formula `⋀A.subfmlsS 🡒 A`
  -- is not provable in `GL`, so there is a finite rooted GL countermodel whose root
  -- forces all axiom T instances for boxed subformulas of `A` but refutes `A`. The
  -- Solovay sentence of the new root of the `1`-extended model is true in `ℕ`
  -- (`solovay_root_sound`) and implies the negation of the realization of `A`
  -- (`SolovaySentences.rfl_mainlemma`).
  haveI : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (T := 𝗜𝚺₁) (U := T) (M := ℕ) inferInstance;
  contrapose! H;
  replace H := LogicGL.iff_forces_root.not.mp $ iff_provable_S_provable_GL.not.mp H;
  push Not at H;
  obtain ⟨κ, _, M, _, hA⟩ := H;
  haveI : Fintype M.World := Fintype.ofFinite _;
  obtain ⟨hA₁, hA₂⟩ := not_forces_imp.mp hA;
  have ha : ∀ B, (□B) ∈ A.subfmls → M.root.1 ⊩ ((□B) 🡒 B) := by
    intro B hB;
    apply forces_fconj.mp hA₁;
    simp only [Formula.subfmlsS, Finset.mem_image];
    exact ⟨B, FormulaFinset.iff_mem_prebox_mem.mpr hB, rfl⟩;
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences T (M.extendRoot 1);
  use S.realization;
  have h₁ : ℕ↓[ℒₒᵣ] ⊧ (S.σ (M.extendRoot 1).root.1 🡒 ∼(A.interpret S.realization)) :=
    models_of_provable inferInstance
      (SolovaySentences.rfl_mainlemma ha Formula.mem_subfmls_self |>.2 hA₂);
  have h₂ : ℕ↓[ℒₒᵣ] ⊧ S.σ (M.extendRoot 1).root.1 := by
    simpa [S, models_iff, LO.FirstOrder.Theory.standardProvability.solovaySentences] using!
      SolovaySentences.solovay_root_sound (T := T) (M := M.extendRoot 1);
  simp only [models_iff, LO.Semantics.Not.models_not, LO.Semantics.Imp.models_imply] at h₁;
  exact h₁ h₂;

/--
  **Arithmetical characterization of S**: for any sound theory `T` (i.e. `ℕ↓[ℒₒᵣ] ⊧* T`)
  extending `𝗜𝚺₁`, `S ⊢ A` iff `f A` is true in `ℕ` for every standard realization `f` for `T`.

  - [AB05, Theorem 3]
-/
theorem arithmetical_completeness_iff [DecidableEq α] :
    A ∈ LogicS ↔ (∀ f : StandardRealization α T, ℕ↓[ℒₒᵣ] ⊧ f A) :=
  ⟨fun h f => arithmetical_soundness h f, arithmetical_completeness⟩

/-- `LogicS` is the provability logic of `T` relative to the true arithmetic `𝗧𝗔`. -/
theorem eq_provabilityLogicRelativeTo_TA [DecidableEq α] :
    @LogicS α = T.provabilityLogicRelativeTo 𝗧𝗔 := by
  ext A;
  rw [show (A ∈ T.provabilityLogicRelativeTo (α := α) 𝗧𝗔) ↔
      (∀ f : StandardRealization α T, 𝗧𝗔 ⊢ f A) from Iff.rfl];
  simp only [TA.provable_iff];
  exact arithmetical_completeness_iff;

/-- `LogicS` is the provability logic of `𝗣𝗔` relative to the true arithmetic `𝗧𝗔`. -/
theorem eq_provabilityLogic_PA_TA [DecidableEq α] :
    @LogicS α = 𝗣𝗔.provabilityLogicRelativeTo 𝗧𝗔 :=
  eq_provabilityLogicRelativeTo_TA

end completeness

end LogicS

end
