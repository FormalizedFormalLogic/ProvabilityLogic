module

public import ProvabilityLogic.ProvabilityLogic.Classification.D_S
public import ProvabilityLogic.ToFoundation.FirstOrder.Incompleteness.Reflection

/-!
# Logic D as the provability logic of `T + Rfn_Σ₁(T)`

`PL_T(T + Rfn_Σ₁(T)) = D`, generalizing Japaridze's theorem `D = PL_PA(PA + ω-Con(PA))` to
the local `Σ₁`-reflection formulation, together with its specialization to `T = 𝗣𝗔`.

`LogicD.arithmetical_completeness` and the unboundedness theorem
`FFL.FirstOrder.Arithmetic.not_localReflection_weakerThan_union_localReflection` it relies
on still rest on `sorry`, and so does everything below that depends on them.

## References

- [AB05, Example 60, Theorem 23]
-/

@[expose] public section

open FFL
open FFL.Entailment
open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction
open Model Model.World

namespace LogicD

variable {α : Type*} {A : Formula α}
variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/--
**Arithmetical soundness of `D`**: the `⊇` half of `PL_T(T + Rfn_Σ₁(T)) = D`.

- [AB05, Example 60]
-/
theorem arithmetical_soundness (h : A ∈ LogicD) (f : Realization α ℒₒᵣ) :
    (T ∪ 𝗥𝗳𝗻[𝚺 1] T) ⊢ f T A := by
  induction h using LogicD.substlessInduction with
  | provable_GL h => exact Entailment.WeakerThan.pbl $ LogicGL.arithmetical_soundness' h;
  | axiomP | axiomD =>
    apply Entailment.by_axm;
    right;
    apply (Provability.mem_localReflectionOn_iff _).mpr ⟨_, ?_, rfl⟩;
    simp [Formula.interpret, Arithmetic.standardProvability_def];
  | mdp ihAB ihA => exact ihAB ⨀ ihA;

/-- - [AB05, Example 60] -/
theorem arithmetical_soundness_PA (h : A ∈ LogicD) (f : Realization α ℒₒᵣ) :
  (𝗣𝗔 ∪ 𝗥𝗳𝗻[𝚺 1] 𝗣𝗔) ⊢ f 𝗣𝗔 A :=
  arithmetical_soundness h f


section completeness

variable [DecidableEq α]

/--
**Arithmetical completeness of `D`**: the `⊆` half of `PL_T(T + Rfn_Σ₁(T)) = D`. The
`D`-analogue of the Solovay construction that it needs is not yet formalized, so the
proof still rests on `sorry`.

- [AB05, Example 60]
-/
theorem arithmetical_completeness
    (H : ∀ f : Realization α ℒₒᵣ, T ∪ 𝗥𝗳𝗻[𝚺 1] T ⊢ f T A) :
    A ∈ LogicD := by
  contrapose! H;
  replace H := LogicGL.iff_forces_root.not.mp $ iff_provable_D_provable_GL.not.mp H;
  push Not at H;
  obtain ⟨κ, _, M, _, hA⟩ := H;
  have : Fintype M.World := Fintype.ofFinite _;
  obtain ⟨hA₁, hA₂⟩ := not_forces_imp.mp hA;
  have ha : ∀ Γ ⊆ A.subfmls.prebox, M.root.1 ⊩[_] (Formula.box (⋁Γ.box) 🡒 ⋁Γ.box) := by
    intro Γ hΓ;
    exact forces_fconj.mp hA₁ _
      (by simp only [Formula.subfmlsD, Finset.mem_image, Finset.mem_powerset]; exact ⟨Γ, hΓ, rfl⟩);
  sorry;

lemma trace_univ_provabilityLogicRelativeTo_localReflection :
  (T.provabilityLogicRelativeTo (T ∪ 𝗥𝗳𝗻[𝚺 1] T) : Logic α).trace = Set.univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_of_provable_TBB;
  exact arithmetical_soundness provable_TBB;

/--
For sound `T`, `D` is the provability logic of `T` relative to `T + Rfn_Σ₁(T)`.

- [AB05, Example 60]
-/
theorem eq_provabilityLogicRelativeTo_localReflection [ℕ↓[ℒₒᵣ] ⊧* T] :
  @LogicD α = T.provabilityLogicRelativeTo (T ∪ 𝗥𝗳𝗻[𝚺 1] T) := by
  have : T ⪯ (T ∪ 𝗥𝗳𝗻[𝚺 1] T) := inferInstance;
  have : 𝗜𝚺₁ ⪯ (T ∪ 𝗥𝗳𝗻[𝚺 1] T) := Entailment.WeakerThan.trans (inferInstance : (𝗜𝚺₁ ⪯ T)) inferInstance;
  have : Entailment.Consistent (T ∪ 𝗥𝗳𝗻[𝚺 1] T) := consistent_of_model (T ∪ 𝗥𝗳𝗻[𝚺 1] T) ℕ;
  apply Set.Subset.antisymm;
  . grind [arithmetical_soundness];
  . intro A hAL;
    apply arithmetical_completeness (T := T);
    apply hAL;

/-- - [AB05, Example 60] -/
theorem eq_provabilityLogic_PA_localReflection :
  @LogicD α = 𝗣𝗔.provabilityLogicRelativeTo (𝗣𝗔 ∪ 𝗥𝗳𝗻[𝚺 1] 𝗣𝗔) :=
  eq_provabilityLogicRelativeTo_localReflection

end completeness

end LogicD

end
