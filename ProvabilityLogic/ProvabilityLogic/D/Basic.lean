module

public import ProvabilityLogic.ProvabilityLogic.Classification.D_S
public import ProvabilityLogic.ToFoundation.FirstOrder.Incompleteness.Reflection

/-!
# Logic D as the provability logic of `T + Rfn_Σ₁(T)`

Example 60 in [AB05]: `PL_T(T + Rfn_Σ₁(T)) = D`, generalizing Japaridze's theorem
`D = PL_PA(PA + ω-Con(PA))` to the local `Σ₁`-reflection formulation.

Main definitions and results:
- `LO.FirstOrder.ArithmeticTheory.localReflection`: the local reflection schema
  `Rfn_Γₙ(T) = { Pr_T(σ) 🡒 σ | σ a Γₙ-sentence }`.
- `LogicD.arithmetical_soundness` (the `⊇` half): if `A ∈ LogicD` then
  `(T ∪ T.localReflection 𝚺 1) ⊢ f A` for every standard realization `f` for `T`.
- `LogicD.arithmetical_completeness` (the `⊆` half): if `(T ∪ T.localReflection 𝚺 1) ⊢ f A`
  for every standard realization `f` for `T`, then `A ∈ LogicD`; `sorry` for now.
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
open Model Model.World

namespace LogicD

variable {α : Type*} {A : Formula α}
variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/--
**Arithmetical soundness of `D`** (the `⊇` half of `PL_T(T + Rfn_Σ₁(T)) = D`):
every theorem of `D` is provable, under every standard realization for `T`, in `T`
extended by the local `𝚺₁`-reflection schema for `T`.

- [AB05, Example 60]
-/
theorem arithmetical_soundness (h : A ∈ LogicD) (f : StandardRealization α T) :
    (T ∪ T.localReflection 𝚺 1) ⊢ f A := by
  -- By `LogicD.substlessInduction`: theorems of `GL` are already provable in `T`, and
  -- the interpretations of the axioms `P` and `D` are `𝚺₁`-reflection instances (at `⊥`
  -- and at `f (□A ⋎ □B)` respectively).
  induction h using LogicD.substlessInduction with
  | provable_GL h => exact Entailment.WeakerThan.pbl $ LogicGL.arithmetical_soundness' h;
  | axiomP | axiomD =>
    apply Entailment.by_axm;
    right;
    apply FirstOrder.ArithmeticTheory.mem_localReflection;
    simp [Formula.interpret, Arithmetic.standardProvability_def];
  | mdp ihAB ihA => exact ihAB ⨀ ihA;

/--
Arithmetical soundness of `D` specialized to Peano arithmetic: every theorem of `D`
is provable in `𝗣𝗔 + Rfn_Σ₁(𝗣𝗔)` under every standard realization for `𝗣𝗔`.

- [AB05, Example 60]
-/
theorem arithmetical_soundness_PA (h : A ∈ LogicD) (f : StandardRealization α 𝗣𝗔) :
  (𝗣𝗔 ∪ 𝗣𝗔.localReflection 𝚺 1) ⊢ f A :=
  arithmetical_soundness h f


section completeness

variable [DecidableEq α]

/--
**Arithmetical completeness of `D`**: if `A` is provable, under every standard
realization for `T`, in `T` extended by the local `𝚺₁`-reflection schema for `T`, then
`A ∈ D`.

The arithmetical construction (a `D`-analogue of the Solovay sentences used for
`LogicS.arithmetical_completeness`) is not yet formalized.

- [AB05, Example 60 (completeness half)]
-/
theorem arithmetical_completeness
    (H : ∀ f : StandardRealization α T, T ∪ T.localReflection 𝚺 1 ⊢ f A) : A ∈ LogicD := by
  -- If `A ∉ LogicD` then by `iff_provable_D_provable_GL` the formula `⋀A.subfmlsD 🡒 A`
  -- is not provable in `GL`, so there is a finite rooted GL countermodel whose root
  -- forces all axiom `D` instances built from subformulas of `A` but refutes `A`.
  contrapose! H;
  replace H := LogicGL.iff_forces_root.not.mp $ iff_provable_D_provable_GL.not.mp H;
  push Not at H;
  obtain ⟨κ, _, M, _, hA⟩ := H;
  haveI : Fintype M.World := Fintype.ofFinite _;
  obtain ⟨hA₁, hA₂⟩ := not_forces_imp.mp hA;
  have ha : ∀ Γ ⊆ A.subfmls.prebox, M.root.1 ⊩ (Formula.box (⋁Γ.box) 🡒 ⋁Γ.box) := by
    intro Γ hΓ;
    exact forces_fconj.mp hA₁ _
      (by simp only [Formula.subfmlsD, Finset.mem_image, Finset.mem_powerset]; exact ⟨Γ, hΓ, rfl⟩);
  sorry;

/-- The provability logic of `T` relative to `T + Rfn_Σ₁(T)` has trace `ω`. -/
lemma trace_univ_provabilityLogicRelativeTo_localReflection :
  (T.provabilityLogicRelativeTo (T ∪ T.localReflection 𝚺 1) : Logic α).trace = Set.univ := by
  -- The logic contains `D` by arithmetical soundness, and `D ⊢ TBB n` for every `n`.
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_of_provable_TBB;
  exact arithmetical_soundness provable_TBB;

/--
For sound `T`, the logic `D` is the provability logic of `T` relative to
`T + Rfn_Σ₁(T)`. This generalizes Japaridze's theorem `D = PL_PA(PA + ω-Con(PA))` to
the local `Σ₁`-reflection formulation.

- [AB05, Example 60]
-/
theorem eq_provabilityLogicRelativeTo_localReflection [ℕ↓[ℒₒᵣ] ⊧* T] :
  @LogicD α = T.provabilityLogicRelativeTo (T ∪ T.localReflection 𝚺 1) := by
  -- The `⊆` half is `arithmetical_soundness`. For the `⊇` half, suppose `A` is in the
  -- provability logic but `A ∉ D`; since the logic has trace `ω`
  -- (`trace_univ_provabilityLogicRelativeTo_localReflection`), Theorem 1 in §5 of [Bek90]
  -- (`provable_reflection_of_mem_not_LogicD`) yields that `T + Rfn_Σ₁(T)` proves *every*
  -- local reflection instance for `T`, contradicting the unboundedness theorem
  -- (`unbounded_localReflection`).
  -- Currently depends on two `sorry`s: the semantic core of Lemma 56 (behind
  -- `provable_reflection_of_mem_not_LogicD`) and the unboundedness theorem.
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

/--
Specialized to Peano arithmetic: `D = PL_PA(PA + Rfn_Σ₁(PA))`.

- [AB05, Example 60]
-/
theorem eq_provabilityLogic_PA_localReflection :
  @LogicD α = 𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗣𝗔.localReflection 𝚺 1) :=
  eq_provabilityLogicRelativeTo_localReflection

end completeness

end LogicD

end
