module

public import Foundation.FirstOrder.Arithmetic.Schemata
public import Foundation.FirstOrder.Arithmetic.Definability.Definable
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

@[expose] public section

open Classical
open LO
open LO.FirstOrder

universe u
noncomputable section

namespace LO.FirstOrder.Arithmetic

variable {V : Type u} [ORingStructure V]

/-- Inserting a fresh unused variable right after the leading (witness) variable of a
formula: evaluating the result at `u :> w :> e` ignores `w` and agrees with evaluating
the original formula at `u :> e`. -/
lemma eval_insert1 {n : ℕ} (θ : Semiformula ℒₒᵣ Empty (n + 1)) (u w : V) (e : Fin n → V) :
  V ⊧/(u :> w :> e) (Rew.bShift.q ▹ θ) ↔ V ⊧/(u :> e) θ := by
  simp [Semiformula.eval_rew_q, Function.comp_def];

@[simp] lemma hierarchy_insert1 {n : ℕ} {Γ s} {θ : Semiformula ℒₒᵣ Empty (n + 1)} :
  Hierarchy Γ s (Rew.bShift.q ▹ θ) ↔ Hierarchy Γ s θ := by
  simp;

/-- Inserting a fresh unused variable right after the two leading variables of a
formula: evaluating the result at `u :> x :> w :> e` ignores `w` and agrees with
evaluating the original formula at `u :> x :> e`. -/
lemma eval_insert2 {n : ℕ} (θ : Semiformula ℒₒᵣ Empty (n + 2)) (u x w : V) (e : Fin n → V) :
  V ⊧/(u :> x :> w :> e) (Rew.bShift.q.q ▹ θ) ↔ V ⊧/(u :> x :> e) θ := by
  simp only [Semiformula.eval_rew_q, Function.comp_def];
  refine Iff.of_eq (congrArg (fun b => Semiformula.Eval (L := ℒₒᵣ) (M := V) b Empty.elim θ) ?_);
  funext i;
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp

@[simp] lemma hierarchy_insert2 {n : ℕ} {Γ s} {θ : Semiformula ℒₒᵣ Empty (n + 2)} :
  Hierarchy Γ s (Rew.bShift.q.q ▹ θ) ↔ Hierarchy Γ s θ := by
  simp;

/-- Base case of the induction: a `𝚫₀` formula already witnesses itself, with an
unused fresh witness variable prepended. -/
lemma base_case {n : ℕ} {φ : Semiformula ℒₒᵣ Empty n} (hφ : Hierarchy 𝚺 0 φ) :
  ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] (e : Fin n → V),
      V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ := by
  use Rew.bShift ▹ φ;
  refine ⟨by simpa using hφ, ?_⟩;
  intro V _ e;
  constructor;
  · intro h; exact ⟨0, by simpa using h⟩;
  · rintro ⟨w, h⟩; simpa using h;

/-- Variant of `base_case` with the (unused) `𝗜𝚺₁` model hypothesis added, matching the
shape expected by the other induction steps. -/
lemma base_case' {n : ℕ} {φ : Semiformula ℒₒᵣ Empty n} (hφ : Hierarchy 𝚺 0 φ) :
  ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ := by
  obtain ⟨θ, hθ, hiff⟩ := base_case hφ;
  exact ⟨θ, hθ, fun V _ _ e => hiff V e⟩;

/-- Combine two `𝚫₀`-witnessed forms of `φ₁`, `φ₂` into a `𝚫₀`-witnessed form of
`φ₁ ⋏ φ₂`, using a single witness bounding both original witnesses. -/
lemma and_case {n : ℕ} {φ₁ φ₂ : Semiformula ℒₒᵣ Empty n}
  {θ₁ θ₂ : Semiformula ℒₒᵣ Empty (n + 1)} (hθ₁ : Hierarchy 𝚺 0 θ₁) (hθ₂ : Hierarchy 𝚺 0 θ₂)
  (h₁ :
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
    V ⊧/e φ₁ ↔ ∃ w, V ⊧/(w :> e) θ₁
  )
  (h₂ :
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
    V ⊧/e φ₂ ↔ ∃ w, V ⊧/(w :> e) θ₂
  )
  : ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e (φ₁ ⋏ φ₂) ↔ ∃ w, V ⊧/(w :> e) θ := by
  use (Rew.bShift.q ▹ θ₁).bexsLTSucc (#0 : Semiterm ℒₒᵣ Empty (n + 1)) ⋏
    (Rew.bShift.q ▹ θ₂).bexsLTSucc (#0 : Semiterm ℒₒᵣ Empty (n + 1));
  refine ⟨by simp [hθ₁, hθ₂], ?_⟩;
  intro V _ _ e;
  simp only [LO.LogicalConnective.HomClass.map_and];
  rw [h₁ V e, h₂ V e];
  simp only [Semiformula.eval_bexsLTSucc, Arithmetic.lt_succ_iff_le, eval_insert1];
  constructor;
  · rintro ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩;
    exact ⟨w₁ + w₂, ⟨w₁, self_le_add_right w₁ w₂, hw₁⟩, ⟨w₂, self_le_add_left w₂ w₁, hw₂⟩⟩;
  · rintro ⟨w, ⟨w₁, _, hw₁⟩, ⟨w₂, _, hw₂⟩⟩;
    exact ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩;

/-- Combine two `𝚫₀`-witnessed forms of `φ₁`, `φ₂` into a `𝚫₀`-witnessed form of
`φ₁ ⋎ φ₂`, reusing the same witness for whichever disjunct holds. -/
lemma or_case {n : ℕ} {φ₁ φ₂ : Semiformula ℒₒᵣ Empty n}
  {θ₁ θ₂ : Semiformula ℒₒᵣ Empty (n + 1)} (hθ₁ : Hierarchy 𝚺 0 θ₁) (hθ₂ : Hierarchy 𝚺 0 θ₂)
  (h₁ :
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
    V ⊧/e φ₁ ↔ ∃ w, V ⊧/(w :> e) θ₁
  )
  (h₂ :
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
    V ⊧/e φ₂ ↔ ∃ w, V ⊧/(w :> e) θ₂
  )
  : ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e (φ₁ ⋎ φ₂) ↔ ∃ w, V ⊧/(w :> e) θ := by
  use θ₁ ⋎ θ₂;
  refine ⟨by simp [hθ₁, hθ₂], ?_⟩;
  intro V _ _ e;
  simp only [LO.LogicalConnective.HomClass.map_or];
  rw [h₁ V e, h₂ V e];
  aesop;

section Collection

variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The formula obtained from a `𝚺₀` formula `θ` (in context `u :> x :> e`) together with
bound variables `w` (for the witness bound) and `y` (unused here) by substituting the
parameter vector `e` with constants: a `Semiformula` in context `u :> x :> w :> y`. -/
private noncomputable def collectionCore {n : ℕ} (θ : Semiformula ℒₒᵣ Empty (n + 2))
  (e : Fin n → V) : Semiformula ℒₒᵣ V 4 :=
  Rew.embSubsts (#0 :> #1 :> fun i => (&(e i) : Semiterm ℒₒᵣ V 4)) ▹ θ

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma hierarchy_collectionCore {n : ℕ} {θ : Semiformula ℒₒᵣ Empty (n + 2)}
  (hθ : Hierarchy 𝚺 0 θ) (e : Fin n → V) : Hierarchy 𝚺 0 (collectionCore θ e) := by
  simp [collectionCore, hθ];

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma eval_collectionCore {n : ℕ} {θ : Semiformula ℒₒᵣ Empty (n + 2)} (e : Fin n → V)
  (u x w y : V) :
  (collectionCore θ e).Eval (u :> x :> w :> ![y]) id ↔ V ⊧/(u :> x :> e) θ := by
  simp only [collectionCore, Semiformula.eval_embSubsts, Function.comp_def];
  refine Iff.of_eq (congrArg (fun b => Semiformula.Evalb (M := V) b θ) ?_);
  funext i;
  induction i using Fin.cases with
  | zero => simp
  | succ i =>
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp

/-- The `𝚺₁` formula `Q(y) := ∃ w, ∀ x < y, x < a → ∃ u ≤ w, θ.Eval (u :> x :> e)`, with `a`
and `e` fixed as parameters. -/
private noncomputable def collectionMotive {n : ℕ} (θ : Semiformula ℒₒᵣ Empty (n + 2))
  (e : Fin n → V) (a : V) : Semiformula ℒₒᵣ V 1 :=
  let cond : Semiformula ℒₒᵣ V 3 :=
    Semiformula.rel Language.LT.lt ![(#0 : Semiterm ℒₒᵣ V 3), (&a : Semiterm ℒₒᵣ V 3)];
  let inner : Semiformula ℒₒᵣ V 3 := (collectionCore θ e).bexsLTSucc (#1 : Semiterm ℒₒᵣ V 3);
  ∃⁰ ((cond 🡒 inner).ballLT (#1 : Semiterm ℒₒᵣ V 2))

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private lemma hierarchy_collectionMotive {n : ℕ} {θ : Semiformula ℒₒᵣ Empty (n + 2)}
  (hθ : Hierarchy 𝚺 0 θ) (e : Fin n → V) (a : V) :
  Hierarchy 𝚺 1 (collectionMotive θ e a) := by
  have : Hierarchy 𝚺 1 (collectionCore θ e) := (hierarchy_collectionCore hθ e).mono (by omega);
  simp [collectionMotive, this];

private lemma eval_collectionMotive {n : ℕ} {θ : Semiformula ℒₒᵣ Empty (n + 2)}
  (e : Fin n → V) (a : V) (v : Fin 1 → V) :
  (collectionMotive θ e a).Eval v id ↔
    ∃ w, ∀ x < v 0, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have hv : v = ![v 0] := by funext i; induction i using Fin.cases with | zero => simp | succ i => exact i.elim0;
  rw [hv];
  simp [collectionMotive, Semiformula.eval_ballLT, Semiformula.eval_bexsLTSucc,
    Arithmetic.lt_succ_iff_le, eval_collectionCore, Function.comp_def];

private lemma collectionMotive_definable {n : ℕ} {θ : Semiformula ℒₒᵣ Empty (n + 2)}
  (hθ : Hierarchy 𝚺 0 θ) (e : Fin n → V) (a : V) :
  𝚺-[1].DefinablePred (fun y => ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ) :=
  HierarchySymbol.Definable.mkPolarity (collectionMotive θ e a) (hierarchy_collectionMotive hθ e a)
    (fun v => (eval_collectionMotive e a v).symm)

/-- Bounded collection for `𝚺₀`-defined predicates: if a `𝚺₀` formula `θ` has a witness for
every `x` below `a`, a single bound `w` majorizes all of these witnesses. This is provable
in `𝗜𝚺₁` via `𝚺₁`-induction on the collecting bound. -/
lemma exists_bound_witness {n : ℕ} {θ : Semiformula ℒₒᵣ Empty (n + 2)} (hθ : Hierarchy 𝚺 0 θ)
  (e : Fin n → V) (a : V) (h : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
  ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have key : ∀ y : V, ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 1
      (P := fun y => ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ)
      (hP := collectionMotive_definable hθ e a);
    · exact ⟨0, fun x hx _ => absurd hx (by simp)⟩;
    · rintro y ⟨w, hw⟩;
      by_cases hya : y < a;
      · obtain ⟨u₀, hu₀⟩ := h y hya;
        refine ⟨max w u₀, fun x hx _ => ?_⟩;
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
        · obtain ⟨u, hu, hPu⟩ := hw x hx (lt_trans hx hya);
          exact ⟨u, le_trans hu (le_max_left w u₀), hPu⟩;
        · exact ⟨u₀, le_max_right w u₀, hu₀⟩;
      · refine ⟨w, fun x hx hxa => ?_⟩;
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl;
        · exact hw x hx hxa;
        · exact absurd hxa hya;
  obtain ⟨w, hw⟩ := key (a + 1);
  exact ⟨w, fun x hx => hw x (lt_trans hx (lt_add_one a)) hx⟩;

end Collection

/-- Combine a `𝚫₀`-witnessed form of `φ` (with one extra bound variable `x`) into a
`𝚫₀`-witnessed form of `∃⁰ φ`, using a single witness bounding both the existential
witness of `φ` and its own `𝚫₀`-witness. -/
private lemma exs_case {n : ℕ} {φ : Semiformula ℒₒᵣ Empty (n + 1)}
  {θ' : Semiformula ℒₒᵣ Empty (n + 2)} (hθ' : Hierarchy 𝚺 0 θ')
  (h :
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e' : Fin (n + 1) → V),
    V ⊧/e' φ ↔ ∃ w, V ⊧/(w :> e') θ'
  )
  : ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e (∃⁰ φ) ↔ ∃ w, V ⊧/(w :> e) θ := by
  use ((Rew.bShift.q.q ▹ θ').bexsLTSucc (#1 : Semiterm ℒₒᵣ Empty (n + 2))).bexsLTSucc
    (#0 : Semiterm ℒₒᵣ Empty (n + 1));
  refine ⟨by simp [hθ'], ?_⟩;
  intro V _ _ e;
  simp only [Semiformula.eval_ex, eval_bexsLTSucc', eval_insert2];
  constructor;
  · rintro ⟨x, hx⟩;
    obtain ⟨w', hw'⟩ := (h V (x :> e)).mp hx;
    exact ⟨x + w', x, self_le_add_right x w', w', self_le_add_left w' x, hw'⟩;
  · rintro ⟨_, x, -, w', -, hw'⟩;
    exact ⟨x, (h V (x :> e)).mpr ⟨w', hw'⟩⟩;

/-- Combine a `𝚫₀`-witnessed form of `φ` (with one extra bound variable `x`) into a
`𝚫₀`-witnessed form of `∀ x < t, φ`, using the collection principle to find a single
witness bounding the whole bounded family of witnesses. -/
private lemma ball_case {n : ℕ} {t : Semiterm ℒₒᵣ Empty n} {φ : Semiformula ℒₒᵣ Empty (n + 1)}
  {θ' : Semiformula ℒₒᵣ Empty (n + 2)} (hθ' : Hierarchy 𝚺 0 θ')
  (h :
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e' : Fin (n + 1) → V),
    V ⊧/e' φ ↔ ∃ w, V ⊧/(w :> e') θ'
  )
  : ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e (φ.ballLT t) ↔ ∃ w, V ⊧/(w :> e) θ := by
  use ((Rew.bShift.q.q ▹ θ').bexsLTSucc (#1 : Semiterm ℒₒᵣ Empty (n + 2))).ballLT
    (Rew.bShift t : Semiterm ℒₒᵣ Empty (n + 1));
  refine ⟨by simp [hθ'], ?_⟩;
  intro V _ _ e;
  simp only [Semiformula.eval_ballLT, eval_bexsLTSucc', eval_insert2, Semiterm.val_bShift];
  constructor;
  · intro hφ;
    have hex : ∀ x < t.valb e, ∃ w', V ⊧/(w' :> x :> e) θ' :=
      fun x hx => (h V (x :> e)).mp (hφ x hx);
    obtain ⟨w, hw⟩ := exists_bound_witness hθ' e (t.valb e) hex;
    exact ⟨w, fun x hx => hw x hx⟩;
  · rintro ⟨w, hw⟩ x hx;
    obtain ⟨w', -, hθ'x⟩ := hw x hx;
    exact (h V (x :> e)).mpr ⟨w', hθ'x⟩;

/-- Every `𝚺₁` formula is, in every model of `𝗜𝚺₁`, equivalent to a `𝚫₀`-witnessed
existential: there is a `𝚺₀` formula `θ` with one extra variable (the witness, at
de Bruijn index `0`) such that `φ` holds iff `θ` has a witness. -/
lemma exists_delta0_witness_form {n : ℕ} {φ : Semiformula ℒₒᵣ Empty n} (hφ : Hierarchy 𝚺 1 φ) :
  ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
    ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
      V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ := by
  apply sigma₁_induction' hφ
    (P := fun n φ => ∃ θ : Semiformula ℒₒᵣ Empty (n + 1), Hierarchy 𝚺 0 θ ∧
      ∀ (V : Type u) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (e : Fin n → V),
        V ⊧/e φ ↔ ∃ w, V ⊧/(w :> e) θ);
  · exact fun n => base_case' (Hierarchy.verum _ _ _);
  · exact fun n => base_case' (Hierarchy.falsum _ _ _);
  · exact fun n t₁ t₂ => base_case' (Hierarchy.rel _ _ _ _);
  · exact fun n t₁ t₂ => base_case' (Hierarchy.nrel _ _ _ _);
  · exact fun n t₁ t₂ => base_case' (Hierarchy.rel _ _ _ _);
  · exact fun n t₁ t₂ => base_case' (Hierarchy.nrel _ _ _ _);
  · rintro n φ ψ hφ hψ ⟨θ₁, hθ₁, h₁⟩ ⟨θ₂, hθ₂, h₂⟩;
    exact and_case hθ₁ hθ₂ h₁ h₂;
  · rintro n φ ψ hφ hψ ⟨θ₁, hθ₁, h₁⟩ ⟨θ₂, hθ₂, h₂⟩;
    exact or_case hθ₁ hθ₂ h₁ h₂;
  · rintro n t φ hφ ⟨θ', hθ', h⟩;
    exact ball_case hθ' h;
  · rintro n φ hφ ⟨θ', hθ', h⟩;
    exact exs_case hθ' h;

end LO.FirstOrder.Arithmetic
