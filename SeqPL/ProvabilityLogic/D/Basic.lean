module

public import SeqPL.Logic.D.Basic
public import SeqPL.ProvabilityLogic.GL.Basic

/-!
# Arithmetical soundness of Logic D

The `⊇` half of Example 60 in [AB05]: `PL_T(T + Rfn_Σ₁(T)) ⊇ D`, i.e. every theorem of
`D` is, under every standard realization for `T`, provable in `T` extended by the local
`Σ₁`-reflection schema for `T`.

Main definitions and results:
- `LO.FirstOrder.ArithmeticTheory.localReflection`: the local reflection schema
  `Rfn_Γₙ(T) = { Pr_T(σ) 🡒 σ | σ a Γₙ-sentence }`.
- `LogicD.arithmetical_soundness`: if `A ∈ LogicD` then
  `(T ∪ T.localReflection 𝚺 1) ⊢ f A` for every standard realization `f` for `T`.
- `LogicD.arithmetical_soundness_PA`: the specialization to `T = 𝗣𝗔`.
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

end LogicD

end
