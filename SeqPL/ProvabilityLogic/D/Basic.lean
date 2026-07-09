module

public import SeqPL.Logic.D.Basic
public import SeqPL.ProvabilityLogic.GL.Basic
public import SeqPL.ProvabilityLogic.Classification.D_S
public import SeqPL.ToFoundation.FirstOrder.Incompleteness.Reflection

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
  | axiomP | axiomD =>
    apply Entailment.by_axm;
    right;
    apply FirstOrder.ArithmeticTheory.mem_localReflection;
    simp [Formula.interpret, Arithmetic.standardProvability_def];
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
  (T.provabilityLogicRelativeTo (T ∪ T.localReflection 𝚺 1) : Logic α).trace = Set.univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_of_provable_TBB;
  exact arithmetical_soundness provable_TBB;

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
  haveI : 𝗜𝚺₁ ⪯ (T ∪ T.localReflection 𝚺 1) := Entailment.WeakerThan.trans (inferInstanceAs (𝗜𝚺₁ ⪯ T)) hTU;
  haveI : Entailment.Consistent (T ∪ T.localReflection 𝚺 1) := consistent_of_model (T ∪ T.localReflection 𝚺 1) ℕ;
  apply Set.Subset.antisymm;
  . grind [arithmetical_soundness];
  . intro A hAL;
    by_contra! hAD;
    apply T.unbounded_localReflection;
    apply provable_reflection_of_mem_not_LogicD (A := A);
    . exact trace_univ_provabilityLogicRelativeTo_localReflection;
    . exact hAL;
    . exact hAD;

/-- **Example 60 in [AB05]** specialized to Peano arithmetic:
`D = PL_PA(PA + Rfn_Σ₁(PA))`. -/
theorem eq_provabilityLogic_PA_localReflection :
  @LogicD α = 𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗣𝗔.localReflection 𝚺 1) :=
  eq_provabilityLogicRelativeTo_localReflection

end completeness

end LogicD

end
