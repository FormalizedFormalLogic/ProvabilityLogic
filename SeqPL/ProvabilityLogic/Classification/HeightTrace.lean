module

public import SeqPL.ProvabilityLogic.Classification.Result

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u
variable {α : Type u}
variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

section heightTrace

omit [𝗜𝚺₁ ⪯ T] in
/-- The standard provability predicate of `T` holds in the standard model iff `T` proves it. -/
lemma models_standardProvability_iff {σ : ArithmeticSentence} :
    ℕ↓[ℒₒᵣ] ⊧ T.standardProvability σ ↔ T ⊢ σ := by
  constructor;
  . intro h;
    exact T.standardProvability.sound_on h;
  . intro h;
    exact models_of_provable inferInstance (T.standardProvability.D1 h);

/-- The `(n + 1)`-th iterated standard provability of falsum holds in the standard model
  iff `T`'s height is at most `n`. -/
lemma models_iterate_standardProvability_bot_iff {n : ℕ} :
    ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[n + 1] ⊥) ↔ T.height ≤ n := by
  rw [Function.iterate_succ_apply', models_standardProvability_iff];
  exact Provability.height_le_iff_boxBot.symm;

omit [𝗜𝚺₁ ⪯ T] in
/-- Falsum itself never holds in the standard model. -/
lemma not_models_standardProvability_bot :
    ¬ ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[0] ⊥) := by
  simp;

/-- The standard interpretation of `TBB n` holds in the standard model iff `T`'s height
  is not `n`. -/
lemma models_standardInterpret_TBB_iff {n : ℕ} :
    ℕ↓[ℒₒᵣ] ⊧ (LetterlessFormula.standardInterpret T (TBB n) : ArithmeticSentence) ↔ T.height ≠ n := by
  have e : LetterlessFormula.standardInterpret T (TBB n)
      = ((T.standardProvability^[n + 1] ⊥) 🡒 (T.standardProvability^[n] ⊥)) := by
    dsimp only [TBB, LetterlessFormula.standardInterpret, LetterlessFormula.interpret];
    rw [LetterlessFormula.interpret_boxItr, LetterlessFormula.interpret_boxItr];
    rfl;
  rw [e];
  have himp :
      ℕ↓[ℒₒᵣ] ⊧ ((T.standardProvability^[n + 1] ⊥) 🡒 (T.standardProvability^[n] ⊥)) ↔
      (ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[n + 1] ⊥) → ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability^[n] ⊥)) := by
    simp;
  rw [himp];
  rcases n with _ | m;
  . simp only [not_models_standardProvability_bot, imp_false, models_iterate_standardProvability_bot_iff];
    simp;
  . rw [models_iterate_standardProvability_bot_iff, models_iterate_standardProvability_bot_iff];
    rcases eq_top_or_lt_top T.height with h | h;
    . simp [h, eq_comm];
    . obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne_top;
      rw [← hk];
      simp only [Nat.cast_le, ne_eq, Nat.cast_inj];
      omega;

/-- `TBB n` is a theorem of the truth provability logic of `T` iff `T`'s height is not `n`. -/
lemma mem_provabilityLogicRelativeTo_TA_TBB_iff {n : ℕ} :
    (TBB n : Formula α) ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α) ↔ T.height ≠ n := by
  have e : ∀ f : StandardRealization α T,
      Formula.interpret f (TBB n) = LetterlessFormula.standardInterpret T (TBB n) := by
    intro f;
    rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  constructor;
  . intro h;
    rw [← models_standardInterpret_TBB_iff, ← e ⟨fun _ => ⊥⟩];
    exact Arithmetic.TA.provable_iff.mp (h ⟨fun _ => ⊥⟩);
  . intro h f;
    rw [e f];
    exact Arithmetic.TA.provable_iff.mpr (models_standardInterpret_TBB_iff.mpr h);

/-- `n` is in the trace of the truth provability logic of `T` iff `T`'s height is not `n`. -/
lemma mem_trace_provabilityLogicRelativeTo_TA_iff {n : ℕ} :
    n ∈ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace ↔ T.height ≠ n := by
  rw [← mem_provabilityLogicRelativeTo_TA_TBB_iff];
  exact ⟨provable_TBB_of_mem_trace, mem_trace_of_provable_TBB⟩;

/-- The trace of the truth provability logic of `T` is all of `ℕ` iff `T` has infinite
  height. -/
lemma trace_provabilityLogicRelativeTo_TA_eq_univ_iff [DecidableEq α] [Nonempty α] :
    (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = Set.univ ↔ T.height = (⊤ : ℕ∞) := by
  rw [Set.eq_univ_iff_forall];
  constructor;
  . intro h;
    by_contra hh;
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hh;
    exact (mem_trace_provabilityLogicRelativeTo_TA_iff.mp (h n)) hn.symm;
  . intro h n;
    rw [mem_trace_provabilityLogicRelativeTo_TA_iff, h];
    exact (ENat.coe_lt_top n).ne';

/-- The trace of the truth provability logic of `T` is the complement of `{n}` iff `T`
  has height `n`. -/
lemma trace_provabilityLogicRelativeTo_TA_eq_compl_singleton_iff [DecidableEq α] [Nonempty α]
  {n : ℕ}
  : (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace = {n}ᶜ ↔ T.height = n := by
  constructor;
  . intro h;
    have hn : n ∉ (T.provabilityLogicRelativeTo 𝗧𝗔 : Logic α).trace := by rw [h]; simp;
    rw [mem_trace_provabilityLogicRelativeTo_TA_iff] at hn;
    exact not_not.mp hn;
  . intro h;
    ext m;
    rw [mem_trace_provabilityLogicRelativeTo_TA_iff (n := m), h];
    simp [eq_comm];

end heightTrace
