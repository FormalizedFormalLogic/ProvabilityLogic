module

public import AlphaCentauri.Reflection.Unboundedness

/-!
# The unboundedness theorem for `Rfn_{𝚺 1}(T)`

The instance of the unboundedness theorem that the arithmetical completeness of `D` rests on:
a consistent `T + Rfn_{𝚺 1}(T)` does not prove the full local reflection schema `Rfn(T)`.

`AlphaCentauri.Reflection.Unboundedness` proves the theorem for an extension by a `Δ₁`-presented
set of sentences in a *strict* prenex class. `Rfn_{𝚺 1}(T)` comes as neither: its members
`Pr_T(σ) 🡒 σ` are `𝚷₂` but not prenex, and no `Δ₁` presentation of the schema is at hand. The
missing bridge is `exists_delta1_strictHierarchy_equiv_localReflection`, which is still `sorry`.

## References

- [AB05, Theorem 23]
- [KL68]
-/

@[expose] public section

open FFL.Entailment
open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction

namespace FFL.FirstOrder.Arithmetic

variable {T : ArithmeticTheory} [T.Δ₁] {Γ : Polarity} {n : ℕ}

/-- `T + Rfn_{Γ n}(T)` holds in the standard model whenever `T` does. -/
instance models_localReflectionOnHierarchy [ℕ↓[ℒₒᵣ] ⊧* T] :
  ℕ↓[ℒₒᵣ] ⊧* (T ∪ 𝗥𝗳𝗻[Γ n] T) := by
  apply Semantics.modelsSet_iff.mpr;
  rintro φ (hφ | hφ);
  . exact Semantics.modelsSet_iff.mp inferInstance hφ;
  . obtain ⟨σ, -, rfl⟩ := (Provability.mem_localReflectionOn_iff _).mp hφ;
    have : ℕ↓[ℒₒᵣ] ⊧ (T.standardProvability σ) → ℕ↓[ℒₒᵣ] ⊧ σ := fun h =>
      models_of_provable inferInstance (T.standardProvability.sound_on h);
    simpa using this;

variable (T) [𝗜𝚺₁ ⪯ T]

/-- `Rfn_{𝚺 1}(T)` is equivalent over `T` to a `Δ₁`-presented set of strict `𝚷₂` sentences.

This is the hypothesis under which `AlphaCentauri.Reflection.Unboundedness` states the
unboundedness theorem, and it is the one thing separating that theorem from
`not_localReflection_weakerThan_union_localReflection` below. Both halves exist separately —
Craig's trick turns the r.e. schema into a `Δ₁`-presented one, and the prenex normal form theorem
turns each `𝚷₂` member into a strict one — but Craig's padding `σ ⋏ ⊤ ⋏ ⋯ ⋏ ⊤` destroys the
prenex shape, and padding *inside* the `𝚫₀` matrix, which would not, is available in neither
Foundation nor AlphaCentauri. Hence the `sorry`.

- [AB05, Theorem 23]
-/
theorem exists_delta1_strictHierarchy_equiv_localReflection :
  ∃ (U : ArithmeticTheory) (_ : U.Δ₁),
  (∀ σ ∈ U, StrictHierarchy 𝚷 2 σ) ∧ T ∪ U ≊ T ∪ 𝗥𝗳𝗻[𝚺 1] T := by
  sorry

/-- **The unboundedness theorem** for `Rfn_{𝚺 1}(T)`: a consistent `T + Rfn_{𝚺 1}(T)`, an
extension of `T` by `𝚷₂`-sentences, does not prove the full local reflection schema `Rfn(T)` —
already its `𝚺₂`-instances are out of reach.

- [AB05, Theorem 23]
- [KL68]
-/
theorem not_localReflection_weakerThan_union_localReflection
  [Consistent (T ∪ 𝗥𝗳𝗻[𝚺 1] T)] : ¬𝗥𝗳𝗻 T ⪯ T ∪ 𝗥𝗳𝗻[𝚺 1] T := by
  intro h;
  obtain ⟨U, dU, hU, hequiv⟩ := exists_delta1_strictHierarchy_equiv_localReflection T;
  let := dU;
  obtain ⟨h₁, h₂⟩ := Equiv.antisymm_iff.mp hequiv;
  have : Consistent (T ∪ U) := Consistent.of_le inferInstance h₁;
  exact not_localReflectionOnHierarchy_weakerThan_union (Γ := 𝚷) (n := 1) hU
    (((WeakerThan.ofSubset
      (T.standardProvability.localReflectionOn_mono fun _ _ => trivial)).trans h).trans h₂);

end FFL.FirstOrder.Arithmetic
