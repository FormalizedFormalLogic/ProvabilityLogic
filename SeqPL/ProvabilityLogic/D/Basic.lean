module

public import SeqPL.Logic.D.Basic
public import SeqPL.ProvabilityLogic.GL.Basic
public import SeqPL.ProvabilityLogic.Classification.D_S

/-!
# Logic D as the provability logic of `T + Rfn_Σ₁(T)`

Example 60 in [AB05]: `PL_T(T + Rfn_Σ₁(T)) = D`, generalizing Japaridze's theorem
`D = PL_PA(PA + ω-Con(PA))` to the local `Σ₁`-reflection formulation.

Main definitions and results:
- `LO.FirstOrder.ArithmeticTheory.localReflection`: the local reflection schema
  `Rfn_Γₙ(T) = { Pr_T(σ) 🡒 σ | σ a Γₙ-sentence }`.
- `LogicD.arithmetical_soundness` (the `⊇` half): if `A ∈ LogicD` then
  `(T ∪ T.localReflection 𝚺 1) ⊢ f A` for every standard realization `f` for `T`.
- `LO.FirstOrder.ArithmeticTheory.unbounded_localReflection`: the instance of the
  unboundedness theorem ([AB05] Theorem 23) needed for the `⊆` half; `sorry` for now.
- `LogicD.eq_provabilityLogicRelativeTo_localReflection`: the resulting equality
  `D = PL_T(T ∪ Rfn_Σ₁(T))` for sound `T`.
- `LogicD.arithmetical_soundness_PA`, `LogicD.eq_provabilityLogic_PA_localReflection`:
  the specializations to `T = 𝗣𝗔`.
-/

@[expose] public section

open LO
open LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction

/-- The local reflection schema `Rfn_Γₙ(T) = { Pr_T(σ) 🡒 σ | σ a Γₙ-sentence }` for the
standard provability predicate of `T` (cf. §1.3 of [AB05]). -/
def LO.FirstOrder.ArithmeticTheory.localReflection
    (T : FirstOrder.ArithmeticTheory) [T.Δ₁] (Γ : Polarity) (n : ℕ) :
    FirstOrder.ArithmeticTheory :=
  { (T.standardProvability σ) 🡒 σ | (σ) (_ : Arithmetic.Hierarchy Γ n σ) }

/-- The reflection instance at a `Γₙ`-sentence `σ` belongs to `Rfn_Γₙ(T)`. -/
lemma LO.FirstOrder.ArithmeticTheory.mem_localReflection
    {T : FirstOrder.ArithmeticTheory} [T.Δ₁] {Γ : Polarity} {n : ℕ}
    {σ : FirstOrder.Sentence ℒₒᵣ} (hσ : Arithmetic.Hierarchy Γ n σ) :
    ((T.standardProvability σ) 🡒 σ) ∈ T.localReflection Γ n :=
  ⟨σ, hσ, rfl⟩


section

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁]

/-- For sound `T`, every local reflection instance for `T` is true in the standard
model: if `Pr_T(σ)` holds in `ℕ` then `T ⊢ σ` (`Provability.SoundOn`), hence `σ` is
true by the soundness of `T`. So `T + Rfn_Γₙ(T)` is sound as well. -/
instance LO.FirstOrder.ArithmeticTheory.models_localReflection
    [ℕ↓[ℒₒᵣ] ⊧* T] {Γ : Polarity} {n : ℕ} :
    ℕ↓[ℒₒᵣ] ⊧* (T ∪ T.localReflection Γ n) := by
  apply Semantics.modelsSet_iff.mpr;
  rintro φ (hφ | ⟨σ, hσ, rfl⟩);
  . exact Semantics.modelsSet_iff.mp inferInstance hφ;
  . have : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability σ) → ℕ↓[ℒₒᵣ] ⊧ σ := fun h =>
      models_of_provable inferInstance (T.standardProvability.sound_on h);
    simpa using this;

/--
  The instance of the **unboundedness theorem** ([AB05] Theorem 23, Kreisel–Lévy 1968)
  needed for the `⊆` half of Example 60: `T + Rfn_Σ₁(T)`, being a consistent extension
  of `T` by `Π₂`-sentences, cannot prove the full local reflection schema `Rfn(T)`
  (already its `Σ₂`-instances are out of reach).

  The proof for a *finite* extension `T + π` (`π ∈ Π₂`) is a three-line Löb argument:
  `T + π ⊢ Pr_T(¬π) 🡒 ¬π` (the instance at the `Σ₂`-sentence `¬π`) gives
  `T ⊢ Pr_T(¬π) 🡒 ¬π` by deduction, hence `T ⊢ ¬π` by Löb's theorem, contradicting
  the consistency of `T + π`. The reduction of the schema case to the finite case is
  the "trick, akin to Rosser's" omitted in [AB05]; it requires an arithmetized
  deduction theorem and a partial truth predicate for `Σ₁`-sentences, neither of which
  is currently available in Foundation. See `.claude/directions/d-completeness.md` for
  the detailed analysis.
-/
theorem LO.FirstOrder.ArithmeticTheory.unbounded_localReflection
    (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [Entailment.Consistent (T ∪ T.localReflection 𝚺 1)] :
    ¬∀ σ : FirstOrder.Sentence ℒₒᵣ,
      (T ∪ T.localReflection 𝚺 1) ⊢ (T.standardProvability σ) 🡒 σ := by
  sorry

end


namespace LogicD

variable {α : Type*} {A : Formula α}
variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/--
  **Arithmetical soundness of `D`** (the `⊇` half of `PL_T(T + Rfn_Σ₁(T)) = D`,
  Example 60 in [AB05]): every theorem of `D` is provable, under every standard
  realization for `T`, in `T` extended by the local `𝚺₁`-reflection schema for `T`.

  The proof is by `LogicD.substlessInduction`: theorems of `GL` are already provable in
  `T`, and the interpretations of the axioms `P` and `D` are `𝚺₁`-reflection instances
  (at `⊥` and at `f (□A ⋎ □B)` respectively).
-/
theorem arithmetical_soundness (h : A ∈ LogicD) (f : StandardRealization α T) :
    (T ∪ T.localReflection 𝚺 1) ⊢ f A := by
  induction h using LogicD.substlessInduction with
  | provable_GL h => exact Entailment.WeakerThan.pbl $ LogicGL.arithmetical_soundness' h;
  | axiomP =>
    -- the interpretation of `∼□⊥` is the reflection instance at `σ = ⊥`.
    apply Entailment.by_axm;
    apply Set.mem_union_right;
    exact FirstOrder.ArithmeticTheory.mem_localReflection (by simp [Formula.interpret]);
  | axiomD =>
    -- the interpretation of `□(□A ⋎ □B) 🡒 (□A ⋎ □B)` is the reflection instance
    -- at the `𝚺₁`-sentence `σ = f (□A ⋎ □B)`.
    apply Entailment.by_axm;
    apply Set.mem_union_right;
    exact FirstOrder.ArithmeticTheory.mem_localReflection
      (by simp [Formula.interpret, Arithmetic.standardProvability_def]);
  | mdp ihAB ihA => exact ihAB ⨀ ihA;

/-- Arithmetical soundness of `D` specialized to Peano arithmetic (Example 60 in
[AB05]): every theorem of `D` is provable in `𝗣𝗔 + Rfn_Σ₁(𝗣𝗔)` under every standard
realization for `𝗣𝗔`. -/
theorem arithmetical_soundness_PA (h : A ∈ LogicD) (f : StandardRealization α 𝗣𝗔) :
    (𝗣𝗔 ∪ 𝗣𝗔.localReflection 𝚺 1) ⊢ f A :=
  arithmetical_soundness h f


section completeness

variable [DecidableEq α]

/-- The provability logic of `T` relative to `T + Rfn_Σ₁(T)` has trace `ω`: it contains
`D` by arithmetical soundness, and `D ⊢ TBB n` for every `n`. -/
lemma trace_univ_provabilityLogicRelativeTo_localReflection :
    (T.provabilityLogicRelativeTo (T ∪ T.localReflection 𝚺 1) : Logic α).trace
      = Set.univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  exact mem_trace_of_provable_TBB (fun f => arithmetical_soundness provable_TBB f);

/--
  **Example 60 in [AB05]**: for sound `T`, the logic `D` is the provability logic of
  `T` relative to `T + Rfn_Σ₁(T)`. This generalizes Japaridze's theorem
  `D = PL_PA(PA + ω-Con(PA))` to the local `Σ₁`-reflection formulation.

  The `⊆` half is `arithmetical_soundness`. For the `⊇` half, suppose `A` is in the
  provability logic but `A ∉ D`; since the logic has trace `ω`
  (`trace_univ_provabilityLogicRelativeTo_localReflection`), Theorem 1 in §5 of [Bek90]
  (`provable_reflection_of_mem_not_LogicD`) yields that `T + Rfn_Σ₁(T)` proves *every*
  local reflection instance for `T`, contradicting the unboundedness theorem
  (`unbounded_localReflection`).

  Currently depends on two `sorry`s: the semantic core of Lemma 56 (behind
  `provable_reflection_of_mem_not_LogicD`) and the unboundedness theorem.
-/
theorem eq_provabilityLogicRelativeTo_localReflection [ℕ↓[ℒₒᵣ] ⊧* T] :
    @LogicD α = T.provabilityLogicRelativeTo (T ∪ T.localReflection 𝚺 1) := by
  haveI hTU : T ⪯ (T ∪ T.localReflection 𝚺 1) := inferInstance;
  haveI : 𝗜𝚺₁ ⪯ (T ∪ T.localReflection 𝚺 1) :=
    Entailment.WeakerThan.trans (inferInstanceAs (𝗜𝚺₁ ⪯ T)) hTU;
  haveI : Entailment.Consistent (T ∪ T.localReflection 𝚺 1) :=
    consistent_of_model (T ∪ T.localReflection 𝚺 1) ℕ;
  apply Set.Subset.antisymm;
  . intro A hA f;
    exact arithmetical_soundness hA f;
  . intro A hAL;
    by_contra hAD;
    exact T.unbounded_localReflection
      (provable_reflection_of_mem_not_LogicD
        trace_univ_provabilityLogicRelativeTo_localReflection hAL hAD);

/-- **Example 60 in [AB05]** specialized to Peano arithmetic:
`D = PL_PA(PA + Rfn_Σ₁(PA))`. -/
theorem eq_provabilityLogic_PA_localReflection :
    @LogicD α = 𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗣𝗔.localReflection 𝚺 1) :=
  eq_provabilityLogicRelativeTo_localReflection

end completeness

end LogicD

end
