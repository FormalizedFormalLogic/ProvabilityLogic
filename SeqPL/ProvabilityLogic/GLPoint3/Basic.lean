module

public import SeqPL.Logic.GLPoint3.Letterless
public import SeqPL.Logic.GLPoint3.Completeness
public import SeqPL.ProvabilityLogic.GL.Basic
public import SeqPL.ProvabilityLogic.Classification.GeneralTrace

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction
open LetterlessFormula (spectrum)

variable {α : Type u}


/-! ### Consistency assertions

A modal formula `A` is a theorem of `GLPoint3` (`GLlin`) iff every arithmetical
interpretation of `A` sending each propositional variable to a *consistency
assertion* is provable in `𝗣𝗔`.

- [VS83, §1, Theorem 1]
-/

namespace LO.FirstOrder.ProvabilityAbstraction

variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L}

/--
Consistency assertions: the inductive subset of sentences generated from
`∼Pr(⌜⊥⌝)` and `Pr(⌜⊥⌝)` (i.e. `¬Pr(⌜0=1⌝)` and `Pr(⌜0=1⌝)` in the paper) by closing
under `Pr(⌜·⌝), ∼, ⋏, ⋎, 🡒`.

- [VS83, §1]
-/
@[grind]
inductive Provability.IsConsistencyAssertion (𝔅 : Provability T₀ T) : FirstOrder.Sentence L → Prop
  | con       : IsConsistencyAssertion 𝔅 (∼(𝔅 ⊥))
  | incon     : IsConsistencyAssertion 𝔅 (𝔅 ⊥)
  | prov {σ}  : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 (𝔅 σ)
  | neg {σ}   : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 (∼σ)
  | and {σ τ} : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 τ → IsConsistencyAssertion 𝔅 (σ ⋏ τ)
  | or {σ τ}  : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 τ → IsConsistencyAssertion 𝔅 (σ ⋎ τ)
  | imp {σ τ} : IsConsistencyAssertion 𝔅 σ → IsConsistencyAssertion 𝔅 τ → IsConsistencyAssertion 𝔅 (σ 🡒 τ)

end LO.FirstOrder.ProvabilityAbstraction

section

variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L}

/--
A realization is a *consistency realization* (the interpretation `φ` of Theorem 1) iff
it sends every propositional variable to a consistency assertion.

- [VS83, Theorem 1]
-/
def Realization.IsConsistencyRealization {𝔅 : Provability T₀ T} (f : Realization α 𝔅) : Prop :=
  ∀ a, 𝔅.IsConsistencyAssertion (f.val a)

/--
The subtype of realizations sending every propositional variable to a consistency
assertion: the type of interpretations `φ` in Theorem 1.

- [VS83, Theorem 1]
-/
abbrev ConsistencyRealization (α : Type*) (𝔅 : Provability T₀ T) :=
  {f : Realization α 𝔅 // f.IsConsistencyRealization}

instance {𝔅 : Provability T₀ T} :
    CoeFun (ConsistencyRealization α 𝔅) (fun _ => Formula α → FirstOrder.Sentence L) :=
  ⟨fun f => Formula.interpret f.1⟩

end

/--
The consistency realizations for the standard provability predicate of an arithmetic
theory `T` (Theorem 1, specialized to `T`).

- [VS83, Theorem 1]
-/
abbrev StandardConsistencyRealization (α : Type*) (T : FirstOrder.ArithmeticTheory) [T.Δ₁] :=
  ConsistencyRealization α T.standardProvability


/--
  Modal counterpart of consistency assertions: the letterless formulas generated from
  `∼□⊥` and `□⊥` by closing under `□, ∼, ⋏, ⋎, 🡒`. Interpreting a `IsConsistencyForm`
  by a provability predicate yields (up to provable equivalence) exactly the
  consistency assertions.
-/
@[grind]
inductive LetterlessFormula.IsConsistencyForm : LetterlessFormula → Prop
  | con       : IsConsistencyForm (∼(□⊥))
  | incon     : IsConsistencyForm (□⊥)
  | box {A}   : IsConsistencyForm A → IsConsistencyForm (□A)
  | neg {A}   : IsConsistencyForm A → IsConsistencyForm (∼A)
  | and {A B} : IsConsistencyForm A → IsConsistencyForm B → IsConsistencyForm (A ⋏ B)
  | or {A B}  : IsConsistencyForm A → IsConsistencyForm B → IsConsistencyForm (A ⋎ B)
  | imp {A B} : IsConsistencyForm A → IsConsistencyForm B → IsConsistencyForm (A 🡒 B)


section correspondence

variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T₀ T : FirstOrder.Theory L} [T₀ ⪯ T]
         {𝔅 : Provability T₀ T} [𝔅.HBL2]

/--
  Every consistency form is interpreted (up to `T₀`-provable equivalence) by a
  consistency assertion.
-/
lemma LetterlessFormula.IsConsistencyForm.exists_consistencyAssertion {A : LetterlessFormula}
  (hA : A.IsConsistencyForm) :
  ∃ σ, 𝔅.IsConsistencyAssertion σ ∧ T₀ ⊢ σ 🡘 (A.interpret 𝔅) := by
  induction hA with
  | con =>
    use ∼(𝔅 ⊥), .con;
    dsimp [LetterlessFormula.interpret];
    cl_prover;
  | incon =>
    use 𝔅 ⊥, .incon;
    dsimp [LetterlessFormula.interpret];
    cl_prover;
  | box _ ih =>
    obtain ⟨σ, hσ, e⟩ := ih;
    exact ⟨𝔅 σ, .prov hσ, 𝔅.ext' e⟩;
  | neg _ ih =>
    obtain ⟨σ, hσ, e⟩ := ih;
    use ∼σ, .neg hσ;
    dsimp [LetterlessFormula.interpret];
    cl_prover [e];
  | and _ _ ih₁ ih₂ =>
    obtain ⟨σ₁, hσ₁, e₁⟩ := ih₁;
    obtain ⟨σ₂, hσ₂, e₂⟩ := ih₂;
    use σ₁ ⋏ σ₂, .and hσ₁ hσ₂;
    dsimp [LetterlessFormula.interpret];
    exact LO.Entailment.E!_trans (LO.Entailment.EKK!_of_E!_of_E! e₁ e₂) (by cl_prover);
  | or _ _ ih₁ ih₂ =>
    obtain ⟨σ₁, hσ₁, e₁⟩ := ih₁;
    obtain ⟨σ₂, hσ₂, e₂⟩ := ih₂;
    use σ₁ ⋎ σ₂, .or hσ₁ hσ₂;
    dsimp [LetterlessFormula.interpret];
    cl_prover [e₁, e₂];
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨σ₁, hσ₁, e₁⟩ := ih₁;
    obtain ⟨σ₂, hσ₂, e₂⟩ := ih₂;
    use σ₁ 🡒 σ₂, .imp hσ₁ hσ₂;
    dsimp [LetterlessFormula.interpret];
    cl_prover [e₁, e₂];

/--
  Every consistency assertion is (up to `T₀`-provable equivalence) the interpretation
  of a consistency form.
-/
lemma Provability.IsConsistencyAssertion.exists_consistencyForm {σ : FirstOrder.Sentence L}
  (hσ : 𝔅.IsConsistencyAssertion σ) :
  ∃ A : LetterlessFormula, A.IsConsistencyForm ∧ T₀ ⊢ σ 🡘 (A.interpret 𝔅) := by
  induction hσ with
  | con =>
    use ∼(□⊥), .con;
    dsimp [LetterlessFormula.interpret];
    cl_prover;
  | incon =>
    use □⊥, .incon;
    dsimp [LetterlessFormula.interpret];
    cl_prover;
  | prov _ ih =>
    obtain ⟨A, hA, e⟩ := ih;
    exact ⟨□A, .box hA, 𝔅.ext' e⟩;
  | neg _ ih =>
    obtain ⟨A, hA, e⟩ := ih;
    use ∼A, .neg hA;
    dsimp [LetterlessFormula.interpret];
    cl_prover [e];
  | and _ _ ih₁ ih₂ =>
    obtain ⟨A, hA, e₁⟩ := ih₁;
    obtain ⟨B, hB, e₂⟩ := ih₂;
    use A ⋏ B, .and hA hB;
    dsimp [LetterlessFormula.interpret];
    exact LO.Entailment.E!_trans (LO.Entailment.EKK!_of_E!_of_E! e₁ e₂) (by cl_prover);
  | or _ _ ih₁ ih₂ =>
    obtain ⟨A, hA, e₁⟩ := ih₁;
    obtain ⟨B, hB, e₂⟩ := ih₂;
    use A ⋎ B, .or hA hB;
    dsimp [LetterlessFormula.interpret];
    cl_prover [e₁, e₂];
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨A, hA, e₁⟩ := ih₁;
    obtain ⟨B, hB, e₂⟩ := ih₂;
    use A 🡒 B, .imp hA hB;
    dsimp [LetterlessFormula.interpret];
    cl_prover [e₁, e₂];

end correspondence


section substLetterless

namespace Formula

/-- Substitute every atom of `A` by a letterless formula, yielding a letterless formula. -/
def substLetterless (g : α → LetterlessFormula) : Formula α → LetterlessFormula
  | #a => g a
  | ⊥ => ⊥
  | A 🡒 B => (A.substLetterless g) 🡒 (B.substLetterless g)
  | □A => □(A.substLetterless g)

@[simp, grind =]
lemma lift_substLetterless {g : α → LetterlessFormula} {A : Formula α} :
  (LetterlessFormula.lift (A.substLetterless g) : Formula α) = A⟦fun a => LetterlessFormula.lift (g a)⟧ := by
  induction A <;> simp_all [Formula.substLetterless];

variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L}
         {𝔅 : Provability T₀ T}

/-- Interpreting a letterless substitution instance is interpreting under the composed
realization. -/
lemma interpret_substLetterless {g : α → LetterlessFormula} {A : Formula α} :
  (A.substLetterless g).interpret 𝔅 = Formula.interpret (⟨fun a => (g a).interpret 𝔅⟩ : Realization α 𝔅) A := by
  induction A <;> simp_all [Formula.substLetterless, LetterlessFormula.interpret, Formula.interpret];

/-- On letterless formulas (`Formula Empty`), `Formula.interpret` does not depend on the
realization and coincides with `LetterlessFormula.interpret`. -/
lemma interpret_letterless {f : Realization Empty 𝔅} {A : LetterlessFormula} :
  Formula.interpret f A = A.interpret 𝔅 := by
  induction A with
  | atom a => exact a.elim;
  | bot => rfl;
  | imp A B ihA ihB => simp only [Formula.interpret, LetterlessFormula.interpret, ihA, ihB];
  | box A ih => simp only [Formula.interpret, LetterlessFormula.interpret, ih];

end Formula

end substLetterless


section kripke

variable {κ : Type u} [Nonempty κ]

open Model Model.World

/- NOTE: forcing of a lifted letterless formula depends only on the rank (cf. [VS83, Lemma 5]);
this is the existing (sorry-free) lemma
`Model.iff_forces_lift_rank_mem_spectrum` in `SeqPL.ProvabilityLogic.Classification.LetterlessTrace`. -/

/-- In a finite rooted linear GL model, the rank determines the world: `rank` is
injective. -/
lemma RootedModel.eq_of_rank_eq {M : RootedModel κ α} [Fintype M.World] [M.IsFiniteGLPoint3]
  {x y : M.World} (h : x.rank = y.rank) : x = y := by
  -- Any two distinct worlds are comparable (linearity), hence have distinct ranks.
  by_contra! ne;
  suffices x ≺ y ∨ y ≺ x by grind [Model.rank_lt_of_rel];
  by_cases hx : x ≠ M.root.1 <;>
  by_cases hy : y ≠ M.root.1;
  . rcases Model.linear (M.root.2 x hx) (M.root.2 y hy) with (Rxy | rfl | Ryx) <;>
    grind;
  all_goals grind;

end kripke


section rankDisj

/--
Finite disjunction of "exact rank" formulas: `rankDisj [n₁, …, nₖ]` is a letterless
consistency form whose spectrum is exactly `{n₁, …, nₖ}`. This realizes the formula
`ψ*(pᵢ) = ⋁_{j ∈ H(pᵢ)} (□^[j+1]⊥ ⋏ ∼□^[j]⊥)` in the proof of the theorems below
(`∼TBB j` is equivalent to `□^[j+1]⊥ ⋏ ∼□^[j]⊥`).

- [VS83, Theorem 1, Theorem 2]
-/
def rankDisj : List ℕ → LetterlessFormula
  | [] => (□⊥) ⋏ (∼(□⊥))
  | n :: l => (∼(TBB n)) ⋎ (rankDisj l)

@[simp]
lemma spectrum_rankDisj {l : List ℕ} : spectrum (rankDisj l) = {n | n ∈ l} := by
  induction l with
  | nil =>
    have h : spectrum ((□⊥ : LetterlessFormula)) = {0} := by
      rw [LetterlessFormula.spectrum_box];
      ext i;
      suffices (∀ j < i, j ∈ (∅ : Set ℕ)) ↔ i = 0 by simpa [LetterlessFormula.spectrum_bot];
      constructor;
      . intro hj;
        by_contra hne;
        exact hj 0 (by omega);
      . rintro rfl;
        omega;
    show spectrum (((□⊥) ⋏ (∼(□⊥))) : LetterlessFormula) = _;
    rw [LetterlessFormula.spectrum_and, LetterlessFormula.spectrum_neg, h];
    simp;
  | cons n l ih =>
    show spectrum (((∼(TBB n)) ⋎ (rankDisj l)) : LetterlessFormula) = _;
    rw [LetterlessFormula.spectrum_or, LetterlessFormula.spectrum_neg,
      LetterlessFormula.spectrum_TBB, ih];
    ext i;
    simp;

lemma isConsistencyForm_boxItr_bot : ∀ {n : ℕ}, 0 < n →
    LetterlessFormula.IsConsistencyForm (□^[n]⊥)
  | 1, _ => .incon
  | n + 2, _ => .box (isConsistencyForm_boxItr_bot (by omega))

lemma isConsistencyForm_TBB : ∀ {n : ℕ}, LetterlessFormula.IsConsistencyForm (TBB n)
  | 0 => .con
  | n + 1 => .imp (isConsistencyForm_boxItr_bot (by omega)) (isConsistencyForm_boxItr_bot (by omega))

lemma isConsistencyForm_rankDisj : ∀ {l : List ℕ}, LetterlessFormula.IsConsistencyForm (rankDisj l)
  | [] => .and .incon .con
  | _ :: _ => .or (.neg isConsistencyForm_TBB) isConsistencyForm_rankDisj

end rankDisj


namespace LogicGLPoint3

section soundness

variable {L : FirstOrder.Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T U : FirstOrder.Theory L} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL] {f : ConsistencyRealization α 𝔅}
         {A : Formula α}

/--
Arithmetical soundness of `GLPoint3` w.r.t. consistency realizations (the easy
direction of Theorem 1): a `GLPoint3` theorem is provable under every consistency
realization.

- [VS83, Theorem 1]
-/
theorem arithmetical_soundness (hA : A ∈ LogicGLPoint3) : T ⊢ f A := by
  -- Replace each atom by an equivalent consistency form, so that the substituted formula
  -- is letterless; `GLPoint3` and `GL` prove the same letterless formulas
  -- ([SV82, Theorem 2], `iff_provable_GLPoint3_provable_GL_of_letterless`), and the
  -- arithmetical soundness of `GL` applies.
  choose g hg₁ hg₂ using fun a => Provability.IsConsistencyAssertion.exists_consistencyForm (f.2 a);
  have hGL : (LetterlessFormula.lift (A.substLetterless g) : Formula α) ∈ LogicGL := by
    apply iff_provable_GLPoint3_provable_GL_of_letterless.mp;
    rw [Formula.lift_substLetterless];
    exact Logic.sumNormal.subst (s := fun a => LetterlessFormula.lift (g a)) hA;
  have h₂ : T ⊢ Formula.interpret (⟨fun a => (g a).interpret 𝔅⟩ : Realization α 𝔅) A := by
    have := LogicGL.arithmetical_soundness (f := f.1) hGL;
    rwa [LetterlessFormula.interpret_lift, Formula.interpret_substLetterless] at this;
  have h₃ : T ⊢ (f A) 🡘 Formula.interpret (⟨fun a => (g a).interpret 𝔅⟩ : Realization α 𝔅) A :=
    Formula.interpret_iff_congr (f₁ := f.1) (fun a => hg₂ a) A;
  cl_prover [h₂, h₃];

/-- Arithmetical soundness of `GLPoint3` w.r.t. consistency realizations, at the
object-theory level. -/
theorem arithmetical_soundness' (hA : A ∈ LogicGLPoint3) : U ⊢ f A :=
  Entailment.WeakerThan.pbl (arithmetical_soundness hA)

end soundness


section completeness

open Model Model.World

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {A : Formula α}

/--
Arithmetical completeness of `GLPoint3` w.r.t. consistency realizations (the hard
direction of Theorem 1): if `A` is not a theorem of `GLPoint3`, then some consistency
realization of `A` is unprovable in `T` (provided `T.height = ⊤`, e.g. `T = 𝗣𝗔`).

- [VS83, Theorem 1]
-/
theorem arithmetical_completeness_of_infinity_height [DecidableEq α] (height : T.height = (⊤ : ℕ∞)) :
  (∀ f : StandardConsistencyRealization α T, T ⊢ f A) → A ∈ LogicGLPoint3 := by
  -- Following §5 of the paper, without Solovay sentences: take a finite rooted linear
  -- countermodel of `A` (Kripke completeness of `GLPoint3`, `LogicGLPoint3.iff_forces_root`),
  -- replace each atom `a` by the letterless formula `ψ*(a) = rankDisj H(a)` whose spectrum
  -- is the set of ranks at which `a` is forced; since ranks determine worlds in a linear
  -- model, the substituted letterless formula `B₀` is not forced at the root, hence
  -- `n := M.height ∉ spectrum B₀` and `GL ⊢ B₀ 🡒 TBB n`. If the corresponding consistency
  -- realization of `A` were provable, then `T ⊢ 𝔅^[n+1]⊥ 🡒 𝔅^[n]⊥`, so `T ⊢ 𝔅^[n]⊥` by
  -- Löb's theorem, contradicting `T.height = ⊤`.
  contrapose!;
  intro hA;
  replace hA := LogicGLPoint3.iff_forces_root.not.mp hA;
  push Not at hA;
  obtain ⟨κ, _, M, _, hM⟩ := hA;
  haveI : Fintype M.World := Fintype.ofFinite _;
  -- `H a`: the set of ranks at which the atom `a` is forced
  let H : α → Finset ℕ := fun a => (Finset.univ.filter fun y : M.World => y ⊩ (#a : Formula α)).image World.rank;
  -- `ψ*` of the paper: a consistency form whose spectrum is exactly `H a`
  let ψ : α → LetterlessFormula := fun a => rankDisj (H a).toList;
  have hspec : ∀ a, spectrum (ψ a) = ↑(H a) := by
    intro a;
    rw [show ψ a = rankDisj (H a).toList by rfl, spectrum_rankDisj];
    ext i;
    simp;
  -- in a linear model the rank determines the world, so `x ⊩ a ↔ x.rank ∈ H a`
  have hatom : ∀ (a : α) (x : M.World), x.rank ∈ H a ↔ x ⊩ (#a : Formula α) := by
    intro a x;
    constructor;
    . intro h;
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h;
      rw [←RootedModel.eq_of_rank_eq hyx];
      exact (Finset.mem_filter.mp hy).2;
    . intro h;
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩);
  -- substituting `ψ*` for the atoms does not change forcing anywhere in `M`
  have hsubst : ∀ B (x : M.World), x ⊩ B⟦fun a => ψ a⟧ ↔ x ⊩ B := by
    intro B;
    induction B with
    | atom a =>
      intro x;
      calc
        x ⊩ ψ a ↔ x.rank ∈ spectrum (ψ a) := Model.iff_forces_lift_rank_mem_spectrum
        _       ↔ x.rank ∈ H a            := by rw [hspec a]; rfl;
        _       ↔ x ⊩ #a                  := hatom a x
    | _ => grind;
  -- the letterless substitution instance `B₀` is not forced at the root
  set B₀ : LetterlessFormula := A.substLetterless ψ with hB₀;
  have hroot : M.root.1 ⊮ (LetterlessFormula.lift B₀ : Formula α) := by
    rw [hB₀, Formula.lift_substLetterless];
    exact fun h => hM ((hsubst A M.root.1).mp h);
  -- hence the height of `M` is missing from the spectrum of `B₀`, and `GL ⊢ B₀ 🡒 TBB n`
  have hnotin : M.height ∉ spectrum B₀ := by
    intro h;
    exact hroot (Model.iff_forces_lift_rank_mem_spectrum.mpr h);
  have hGL : ((B₀ 🡒 TBB M.height)) ∈ @LogicGL Empty := by
    apply iff_GL_proves_imp_GL_subset_spectrum.mpr;
    grind [LetterlessFormula.spectrum_TBB];
  -- the counterexample realization: consistency assertions equivalent to `interpret (ψ a)`
  choose σ hσ₁ hσ₂ using
    fun a => (isConsistencyForm_rankDisj (l := (H a).toList)).exists_consistencyAssertion
      (𝔅 := T.standardProvability);
  use ⟨⟨σ⟩, hσ₁⟩;
  intro hprov;
  -- `f* A` is provably equivalent to `interpret 𝔅 B₀`
  have hequiv :
    𝗜𝚺₁ ⊢ (Formula.interpret (⟨σ⟩ : StandardRealization α T) A) 🡘
      (Formula.interpret (⟨fun a => (ψ a).interpret T.standardProvability⟩ : StandardRealization α T) A) :=
    Formula.interpret_iff_congr (fun a => hσ₂ a) A;
  have h₁ : T ⊢ Formula.interpret (⟨fun a => (ψ a).interpret T.standardProvability⟩ : StandardRealization α T) A := by
    have h : T ⊢ (Formula.interpret (⟨σ⟩ : StandardRealization α T) A) 🡘
        (Formula.interpret (⟨fun a => (ψ a).interpret T.standardProvability⟩ : StandardRealization α T) A) :=
      Entailment.WeakerThan.pbl hequiv;
    cl_prover [hprov, h];
  have h₂ : T ⊢ B₀.interpret T.standardProvability := by
    rwa [hB₀, Formula.interpret_substLetterless];
  -- soundness of `GL` yields `T ⊢ 𝔅^[n+1]⊥ 🡒 𝔅^[n]⊥`, hence `T ⊢ 𝔅^[n]⊥` by Löb
  have h₃ : T ⊢ LetterlessFormula.interpret T.standardProvability (TBB M.height) := by
    have h := LogicGL.arithmetical_soundness'
      (f := (⟨Empty.elim⟩ : StandardRealization Empty T)) hGL;
    rw [Formula.interpret_letterless] at h;
    simp only [LetterlessFormula.interpret] at h;
    exact h ⨀ h₂;
  have h₄ : T ⊢ T.standardProvability^[M.height] ⊥ := by
    apply löb_theorem (𝔅 := T.standardProvability);
    have e : LetterlessFormula.interpret T.standardProvability (TBB M.height)
        = ((T.standardProvability^[M.height + 1] ⊥) 🡒 (T.standardProvability^[M.height] ⊥)) := by
      dsimp only [TBB, LetterlessFormula.interpret];
      rw [LetterlessFormula.interpret_boxItr, LetterlessFormula.interpret_boxItr];
      rfl;
    rw [e, Function.iterate_succ_apply'] at h₃;
    exact h₃;
  exact Provability.height_eq_top_iff.mp height M.height h₄;

/--
For any theory of infinite height, `A` is a theorem of `GLPoint3` iff every
consistency realization of `A` is provable.

- [VS83, Theorem 1]
-/
theorem arithmetical_completeness_iff_of_infinity_height [DecidableEq α] (height : T.height = (⊤ : ℕ∞)) :
  A ∈ LogicGLPoint3 ↔ ∀ f : StandardConsistencyRealization α T, T ⊢ f A := by
  constructor;
  . intro h f;
    exact arithmetical_soundness' (f := f) h;
  . exact arithmetical_completeness_of_infinity_height height;

theorem arithmetical_completeness_iff_of_sigma1_sound [DecidableEq α] [T.SoundOnHierarchy 𝚺 1] :
  A ∈ LogicGLPoint3 ↔ ∀ f : StandardConsistencyRealization α T, T ⊢ f A :=
  arithmetical_completeness_iff_of_infinity_height (FirstOrder.Arithmetic.height_eq_top_of_sigma1_sound T)

/--
For each modal formula `A`, `A ∈ LogicGLPoint3` iff `⊢PA φ(A)` for each interpretation
`φ` sending every propositional variable to a consistency assertion of `𝗣𝗔`.

- [VS83, Theorem 1]
-/
theorem arithmetical_completeness_iff_peano_arithmetic [DecidableEq α] :
  A ∈ LogicGLPoint3 ↔ ∀ f : StandardConsistencyRealization α 𝗣𝗔, 𝗣𝗔 ⊢ f A :=
  arithmetical_completeness_iff_of_sigma1_sound

end completeness

end LogicGLPoint3

end
