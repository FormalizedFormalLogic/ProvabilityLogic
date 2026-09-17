module

public import AlphaCentauri.Hierarchy.NormalForm
public import AlphaCentauri.Reflection.Unboundedness

/-!
# Binary uniform reflection

A single `𝚷₂` sentence `uniformReflection₂ T φ` asserting, for a two-variable `𝚺₁` formula `φ`,
that every `T`-provable numerical instance `φ(ẋ, ẏ)` is true.

Unlike the local reflection *schema*, one such sentence covers infinitely many reflection
instances at once, which is what lets the unboundedness theorem of
`AlphaCentauri.Reflection.StandardProvability` — stated there for an extension by a single
sentence, or by finitely many — reach the extension of `T` that the arithmetical completeness of
`D` needs. Two instances suffice for `D`: `φ = ⊥` gives the axiom `P`, and `φ = provOrProv T`
gives the axiom `D`.

The code `z` quantified over here is always the code of a *closed* sentence, being pinned down by
`ssnums` as a numeral substitution instance of the fixed `φ`. That is what makes
`models_uniformReflection₂` provable: AlphaCentauri's partial truth predicates agree with truth on
sentences only, so a schema quantifying over arbitrary codes of `𝚺₁` formulas would need a
"variable free" predicate that neither library has.

## References

- [Lin97, §4.1, p. 52]
- [AB05, §4.2]
-/

@[expose] public section

open FFL
open FFL.Entailment
open FFL.FirstOrder FFL.FirstOrder.ProvabilityAbstraction

namespace FFL.FirstOrder.Arithmetic

open Bootstrapping

variable (T : ArithmeticTheory) [T.Δ₁]

/-- Binary uniform reflection for `φ`: `∀ x y, Pr_T(⌜φ(ẋ, ẏ)⌝) 🡒 φ(x, y)`.

- [Lin97, §4.1, p. 52]
- [AB05, §4.2]
-/
noncomputable def uniformReflection₂ (φ : ArithmeticSemisentence 2) : ArithmeticSentence :=
  “∀ x, ∀ y, ∀ z, !(Bootstrapping.Arithmetic.ssnums (k := 2)) z ↑(Encodable.encode φ) x y →
    !(provable T).val z → !φ x y”

/-- The two-variable formula `(Pr_T(x) 🡒 ⊥) 🡒 Pr_T(y)`: the shape the modal disjunction
`□A ⋎ □B` unfolds to under `Formula.interpret`. -/
noncomputable def provOrProv : ArithmeticSemisentence 2 :=
  “x y. (!(provable T).val x → ⊥) → !(provable T).val y”

/-- Substituting two sentence codes into `provOrProv T` yields the disjunction of the two
provability statements, in that same unfolded shape. -/
lemma subst_provOrProv (σ π : ArithmeticSentence) :
  ((Rew.subst ![⌜σ⌝, ⌜π⌝]) ▹ provOrProv T : ArithmeticSentence) =
  ((T.standardProvability σ 🡒 ⊥) 🡒 T.standardProvability π) := by
  simp [provOrProv, Arithmetic.standardProvability_def, Bootstrapping.provabilityPred,
    Rewriting.subst, ← TransitiveRewriting.comp_app, Rew.subst_comp_subst];

section

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Truth of `uniformReflection₂` in a model of `𝗜𝚺₁`. -/
lemma models_uniformReflection₂_iff (φ : ArithmeticSemisentence 2) :
  V↓[ℒₒᵣ] ⊧ uniformReflection₂ T φ ↔
  ∀ x y : V, Bootstrapping.Provable T
    (Bootstrapping.Arithmetic.substNumerals (⌜φ⌝ : V) ![x, y]) → V ⊧/![x, y] φ := by
  have h₁ := (inferInstance : Arithmetic.HierarchySymbol.DefinedFunction (ℌ := 𝚺₁)
    (fun v : Fin 3 → V ↦ Bootstrapping.Arithmetic.substNumerals (v 0) (v ·.succ))
    (Bootstrapping.Arithmetic.ssnums (k := 2))).df;
  simp [uniformReflection₂, models_iff, h₁,
    (Bootstrapping.Provable.defined (T := T) (V := V)).df,
    Semiformula.Evalb, Sentence.quote_eq_encode, numeral_eq_natCast];

set_option maxHeartbeats 1000000 in
/-- The numeral substitution instance of `provOrProv T` at two sentence codes is the code of the
consequent of the corresponding axiom `D` instance. -/
lemma substNumerals_provOrProv (σ π : ArithmeticSentence) :
  Bootstrapping.Arithmetic.substNumerals (⌜provOrProv T⌝ : V) ![⌜σ⌝, ⌜π⌝] =
  (⌜(((T.standardProvability σ 🡒 ⊥) 🡒 T.standardProvability π) : ArithmeticSentence)⌝ : V) := by
  have h := Bootstrapping.Arithmetic.substNumerals_app_quote (V := V) (provOrProv T)
    ![(⌜σ⌝ : ℕ), (⌜π⌝ : ℕ)];
  have h₁ : (fun i => ((![(⌜σ⌝ : ℕ), (⌜π⌝ : ℕ)] i : ℕ) : V)) = ![(⌜σ⌝ : V), (⌜π⌝ : V)] := by
    simp [Matrix.fun_eq_vec_two, Sentence.coe_quote_eq_quote];
  have h₂ : (fun i => ((![(⌜σ⌝ : ℕ), (⌜π⌝ : ℕ)] i : ℕ) : ArithmeticSemiterm Empty 0)) =
      ![(⌜σ⌝ : ArithmeticSemiterm Empty 0), (⌜π⌝ : ArithmeticSemiterm Empty 0)] := by
    simp [Matrix.fun_eq_vec_two];
  rw [h₁, h₂, subst_provOrProv] at h;
  exact h;

end

/-- Uniform reflection holds in the standard model whenever `T` does. -/
lemma models_uniformReflection₂ [ℕ↓[ℒₒᵣ] ⊧* T] (φ : ArithmeticSemisentence 2) :
  ℕ↓[ℒₒᵣ] ⊧ uniformReflection₂ T φ := by
  apply (models_uniformReflection₂_iff T φ).mpr;
  intro x y h;
  have h₁ : Bootstrapping.Provable T
      (⌜((Rew.subst fun i => ↑(![x, y] i)) ▹ φ : ArithmeticSentence)⌝ : ℕ) := by
    rw [← Bootstrapping.Arithmetic.substNumerals_app_quote (V := ℕ) φ ![x, y]];
    simpa using h;
  have h₂ : ℕ↓[ℒₒᵣ] ⊧ ((Rew.subst fun i => ↑(![x, y] i)) ▹ φ : ArithmeticSentence) :=
    models_of_provable inferInstance (Bootstrapping.Provable.sound h₁);
  simpa [models_iff, Function.comp_def, Semiformula.eval_substs,
    Matrix.empty_eq, Structure.numeral_eq_numeral, numeral_eq_natCast] using h₂;

/-- `uniformReflection₂ T φ` is `𝚷₂` whenever `φ` is `𝚺₁`. -/
theorem hierarchy_uniformReflection₂ (φ : ArithmeticSemisentence 2) (hφ : Hierarchy 𝚺 1 φ) :
  Hierarchy 𝚷 2 (uniformReflection₂ T φ) := by
  have h₁ : Hierarchy 𝚺 2 (Bootstrapping.Arithmetic.ssnums (k := 2)).val :=
    (Bootstrapping.Arithmetic.ssnums (k := 2)).sigma_prop.mono (by omega);
  have h₂ : Hierarchy 𝚺 2 (provable T).val := (provable T).sigma_prop.mono (by omega);
  have h₃ : Hierarchy 𝚷 2 φ := hφ.strict_mono 𝚷 (by omega);
  simp [uniformReflection₂, h₁, h₂, h₃];

@[simp] theorem hierarchy_provOrProv : Hierarchy 𝚺 1 (provOrProv T) := by
  simp [provOrProv, (provable T).sigma_prop];

set_option maxHeartbeats 1000000 in
/-- The instances of the modal axiom `D` all follow from the single sentence
`uniformReflection₂ T (provOrProv T)`. -/
theorem provable_uniformReflection₂_imp_axiomD (σ π : ArithmeticSentence) :
  𝗜𝚺₁ ⊢ uniformReflection₂ T (provOrProv T) 🡒
  (T.standardProvability ((T.standardProvability σ 🡒 ⊥) 🡒 T.standardProvability π) 🡒
    ((T.standardProvability σ 🡒 ⊥) 🡒 T.standardProvability π)) := by
  apply Arithmetic.complete.{0};
  intro M _ _;
  simp only [Semantics.Imp.models_imply];
  intro h₁ h₂;
  have h₃ : Bootstrapping.Provable T
      (Bootstrapping.Arithmetic.substNumerals (⌜provOrProv T⌝ : M) ![⌜σ⌝, ⌜π⌝]) := by
    rw [substNumerals_provOrProv];
    simpa [Arithmetic.standardProvability_def, models_iff,
      (Bootstrapping.Provable.defined (T := T) (V := M)).df] using h₂;
  have h₄ := (models_uniformReflection₂_iff T (provOrProv T)).mp h₁ ⌜σ⌝ ⌜π⌝ h₃;
  simpa [provOrProv, models_iff, Arithmetic.standardProvability_def,
    Bootstrapping.provabilityPred,
    (Bootstrapping.Provable.defined (T := T) (V := M)).df] using h₄;

set_option maxHeartbeats 1000000 in
/-- The modal axiom `P` follows from the degenerate uniform reflection instance at `⊥`. -/
theorem provable_uniformReflection₂_bot_imp_con :
  𝗜𝚺₁ ⊢ uniformReflection₂ T (⊥ : ArithmeticSemisentence 2) 🡒 ∼T.standardProvability ⊥ := by
  apply Arithmetic.complete.{0};
  intro M _ _;
  simp only [Semantics.Imp.models_imply];
  intro h₁;
  have h₂ : Bootstrapping.Arithmetic.substNumerals ((⌜(⊥ : ArithmeticSemisentence 2)⌝ : M))
      ![0, 0] = (⌜(⊥ : ArithmeticSentence)⌝ : M) := by
    have h := Bootstrapping.Arithmetic.substNumerals_app_quote (V := M)
      (⊥ : ArithmeticSemisentence 2) ![(0 : ℕ), (0 : ℕ)];
    simpa [Matrix.fun_eq_vec_two] using h;
  have h₃ : ¬ (M↓[ℒₒᵣ] ⊧ (T.standardProvability ⊥ : ArithmeticSentence)) := by
    intro h₄;
    have h₅ : Bootstrapping.Provable T
        (Bootstrapping.Arithmetic.substNumerals (⌜(⊥ : ArithmeticSemisentence 2)⌝ : M) ![0, 0]) := by
      rw [h₂];
      simpa [Arithmetic.standardProvability_def, models_iff,
        (Bootstrapping.Provable.defined (T := T) (V := M)).df] using h₄;
    have h₆ := (models_uniformReflection₂_iff T (⊥ : ArithmeticSemisentence 2)).mp h₁ 0 0 h₅;
    simp at h₆;
  simpa using h₃;

-- Kept opaque: unfolding the Gödel code of `provOrProv T` makes definitional unification diverge
-- in the proofs downstream of this file.
attribute [irreducible] provOrProv uniformReflection₂

end FFL.FirstOrder.Arithmetic
