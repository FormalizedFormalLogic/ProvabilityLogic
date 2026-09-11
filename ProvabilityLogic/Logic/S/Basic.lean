module

public import ProvabilityLogic.Logic.GL.Basic
public import ProvabilityLogic.Kripke.Tail
public import ProvabilityLogic.Gentzen.S.Kripke

@[expose]
public section

abbrev LogicS {α} : Logic α := (LogicGL) +ᴸ ({ □A 🡒 A | A })

universe u v
variable {α : Type u}

open LogicGL
open Logic.sumQuasiNormal

namespace LogicS

@[grind →]
lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicS :=
  mem₁ h

lemma provable_axiomT {A : Formula α} : (□A 🡒 A) ∈ LogicS := mem₂ ⟨A, rfl⟩

section

/-- Intrinsic definition of `LogicS` avoiding `subst`. -/
private inductive substless : Logic α
  | provable_GL {A} : A ∈ LogicGL → substless A
  | axiomT (A) : substless (□A 🡒 A)
  | mdp {A B} : substless (A 🡒 B) → substless A → substless B

private lemma substless.eq_LogicS : substless (α := α) = LogicS := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | provable_GL h => exact provable_of_provable_GL h;
    | axiomT A => exact provable_axiomT;
    | mdp _ _ ihAB ihA => exact Logic.sumQuasiNormal.mdp ihAB ihA;
  . intro h;
    induction h with
    | mem₁ h => exact substless.provable_GL h;
    | mem₂ h =>
      obtain ⟨B, rfl⟩ := h;
      exact substless.axiomT B;
    | mdp _ _ ihAB ihA => exact substless.mdp ihAB ihA;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | provable_GL h => exact substless.provable_GL (ProvableHilbert.subst h);
      | axiomT B => exact substless.axiomT _;
      | mdp _ _ ihAB ihA => exact substless.mdp ihAB ihA;

private lemma substless.toLogicS {A : Formula α} (h : substless A) : A ∈ LogicS :=
  substless.eq_LogicS ▸ h

private lemma substless.ofLogicS {A : Formula α} (h : A ∈ LogicS) : substless A :=
  substless.eq_LogicS.symm ▸ h

/-- Induction principle for `LogicS` avoiding `subst`. -/
protected lemma substlessInduction
  {motive : (A : Formula α) → A ∈ LogicS → Prop}
  (provable_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (axiomT : ∀ {A}, motive (□A 🡒 A) provable_axiomT)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicS} → {hA : A ∈ LogicS} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : A ∈ LogicS) → motive A h := by
  intro A h;
  induction substless.ofLogicS h with
  | provable_GL hg => exact provable_GL hg;
  | axiomT A => exact axiomT;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := substless.toLogicS hAB) (hA := substless.toLogicS hA)
      (ihAB _) (ihA _);

end


variable {A B C : Formula α}

lemma provable_lconj_of_forall_provable {Γ : FormulaList α} (h : ∀ B ∈ Γ, B ∈ LogicS) :
  (⋀Γ) ∈ LogicS := by
  match Γ with
  | [] => exact provable_of_provable_GL ProvableHilbert.top;
  | [B] => exact h B (by simp);
  | B :: C :: Γ =>
    exact Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mdp (provable_of_provable_GL ProvableHilbert.andIntro) (h B (by simp)))
      (provable_lconj_of_forall_provable (Γ := C :: Γ) (by grind));

lemma provable_fconj_of_forall_provable {Γ : FormulaFinset α} (h : ∀ B ∈ Γ, B ∈ LogicS) :
  (⋀Γ) ∈ LogicS :=
  provable_lconj_of_forall_provable (by simpa)

lemma provable_fconj_subfmlsS [DecidableEq α] : (⋀A.subfmlsS) ∈ LogicS := by
  apply provable_fconj_of_forall_provable;
  intro B hB;
  obtain ⟨C, _, rfl⟩ : ∃ C ∈ A.subfmls.prebox, (□C 🡒 C) = B := by
    simpa [Formula.subfmlsS] using hB;
  exact provable_axiomT;


open Model Model.World

lemma eventually_forces_tail_nat_of_provable [DecidableEq α] (h : A ∈ LogicS) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n → toTail.chainPoint n ⊩[(M.toTail tail).toModel] A := by
  intro κ _ M _ tail;
  induction h using LogicS.substlessInduction with
  | provable_GL h =>
    exact ⟨0, fun n _ => ProvableHilbert.Kripke.soundness h ((M.toTail tail).toModel) _⟩;
  | @axiomT B =>
    obtain ⟨k, hk⟩ := toTail.forces_nat_eventually_stable (M := M) (tail := tail) B;
    use k + 1;
    intro n hn hbox;
    have hBk : toTail.chainPoint k ⊩[(M.toTail tail).toModel] B :=
      hbox (toTail.chainPoint k)
        (toTail.rel_chainPoint_chainPoint.mpr (by exact_mod_cast Nat.lt_of_succ_le hn));
    exact (hk n (by omega)).mpr hBk;
  | mdp ihAB ihA =>
    obtain ⟨k₁, h₁⟩ := ihAB;
    obtain ⟨k₂, h₂⟩ := ihA;
    exact ⟨max k₁ k₂, fun n hn =>
      h₁ n (le_trans (le_max_left _ _) hn) (h₂ n (le_trans (le_max_right _ _) hn))⟩;

lemma root_forces_subfmlsS_imp [DecidableEq α]
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → toTail.chainPoint n ⊩[(M.toTail tail).toModel] A) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
  M.root.1 ⊩[_] (⋀A.subfmlsS 🡒 A) := by
  intro κ _ M _ h₁;
  have hΓ : ∀ B ∈ A.subfmls.prebox, M.root.1 ⊩[_] (□B 🡒 B) := by
    intro B hB;
    exact forces_fconj.mp h₁ _ (by
      simp only [Formula.subfmlsS, Finset.mem_image];
      exact ⟨B, hB, rfl⟩);
  obtain ⟨k, hk⟩ := h M.toModel M.root.1;
  exact (toTail.root_forces_iff_forces_nat (Γ := A.subfmls)
    (fun B hB => Formula.subfmls_trans hB) hΓ A Formula.mem_subfmls_self k).mpr (hk k le_rfl);


lemma isReflexive_prebox_box_iff_forces_fconj_subfmlsS [DecidableEq α]
  {κ : Type v} [Nonempty κ] {M : Model κ α} {x : M.World} :
  x.IsReflexiveOf (A.subfmls.prebox.box) ↔ x ⊩[_] ⋀A.subfmlsS := by
  simp [Model.World.IsReflexiveOf, forces_fconj, Formula.subfmlsS, FormulaFinset.box]

lemma exists_isReflexive_forces_of_GL_provable [DecidableEq α]
  (h : (⋀A.subfmlsS 🡒 A) ∈ LogicGL) :
  ∃ X : FormulaFinset α, ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
  ∀ (x : M.ReflexiveWorldOf X), (x : M.World) ⊩[_] (∅ ⟹ {A}) := by
  use A.subfmls.prebox.box;
  intro κ _ M _ x;
  have hHilbert := LogicGL.iff_provableHilbert.mp h;
  have hsound := ProvableHilbert.Kripke.soundness hHilbert M (x : M.World);
  have hAnt := isReflexive_prebox_box_iff_forces_fconj_subfmlsS.mp x.2;
  apply Model.World.forces_singleton_sequent.mpr;
  grind

lemma provableGentzen_of_GL_provable [DecidableEq α]
  (h : (⋀A.subfmlsS 🡒 A) ∈ LogicGL) :
  ⊢ᵍ[S] (∅ ⟹[1] {A}) := by
  apply ProvableGentzen.Kripke.completeness;
  intro κ _ M _ w hw;
  obtain ⟨X, hX⟩ := exists_isReflexive_forces_of_GL_provable h;
  obtain ⟨i, hi⟩ := eventually_forces_of_exists_isReflexive_forces (fun {κ} _ M _ => ⟨X, hX M⟩) M w hw;
  exact ⟨i, hi i (le_refl i)⟩;

lemma eventually_forces_tail_nat_of_provableGentzen [DecidableEq α]
  (h : ⊢ᵍ[S] (∅ ⟹[1] {A})) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n → toTail.chainPoint n ⊩[(M.toTail tail).toModel] A := by
  intro κ _ M _ tail;
  have h1 := GentzenWithCutProvable.of_without_cut h;
  obtain ⟨X, hX⟩ := GentzenWithCutProvable.soundness h1;
  have hw : ∀ n : ℕ,
      (toTail.chainPoint (M := M) (tail := tail) (↑(n + 1) : ℕ∞)) ≺
      (toTail.chainPoint (↑n : ℕ∞)) := by
    intro n;
    exact toTail.rel_chainPoint_chainPoint.mpr (by exact_mod_cast Nat.lt_succ_self n);
  obtain ⟨i, hi⟩ :=
    Model.eventually_isReflexive_of_descending (M := (M.toTail tail).toModel)
      (w := fun n => toTail.chainPoint (↑n : ℕ∞)) hw X;
  refine ⟨i, ?_⟩;
  intro n hn;
  exact Model.World.forces_singleton_sequent.mp
    (hX ((M.toTail tail).toModel) ⟨toTail.chainPoint (↑n : ℕ∞), hi n hn⟩);

/--
  Characterizations of `LogicS`: in terms of `GL`, of the two-layered sequent calculus for
  `S`, and of forcing in tail models of finite `GL` models.

  - [KK23]
-/
theorem provability_TFAE [DecidableEq α] : [
  A ∈ LogicS,
  ⊢ᵍ[S] (∅ ⟹[1] {A}),
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n → toTail.chainPoint n ⊩[(M.toTail tail).toModel] A,
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    M.root.1 ⊩[_] (⋀A.subfmlsS 🡒 A),
  ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] → ∀ (tail : M.World),
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m → toTail.chainPoint m ⊩[(M.toTail tail).toModel] A,
  (⋀A.subfmlsS 🡒 A) ∈ LogicGL,
].TFAE := by
  tfae_have 1 → 3 := eventually_forces_tail_nat_of_provable;
  tfae_have 3 → 4 := root_forces_subfmlsS_imp;
  tfae_have 4 ↔ 6 := LogicGL.iff_forces_root.symm;
  tfae_have 6 → 1 := fun h => mdp (provable_of_provable_GL h) provable_fconj_subfmlsS;
  tfae_have 6 → 2 := provableGentzen_of_GL_provable;
  tfae_have 2 → 3 := eventually_forces_tail_nat_of_provableGentzen;
  tfae_have 3 → 5 := by
    intro h n _ M _ tail;
    obtain ⟨k, hk⟩ :=
      h (M.reindex (Equiv.ulift (α := Fin n)).symm) ((Equiv.ulift (α := Fin n)).symm tail);
    exact ⟨k, fun m hm => Model.forces_toTail_reindex_chainPoint_iff.mp (hk m hm)⟩;
  tfae_have 5 → 3 := by
    intro h κ _ M _ tail;
    obtain ⟨k, hk⟩ := h M.card M.toConcrete (Finite.equivFin κ tail);
    exact ⟨k, fun m hm => Model.forces_toTail_reindex_chainPoint_iff.mp (hk m hm)⟩;
  tfae_finish;

theorem iff_provable_S_provable_GL [DecidableEq α] :
  A ∈ LogicS ↔ (⋀A.subfmlsS 🡒 A) ∈ LogicGL := provability_TFAE.out 0 5

theorem iff_eventually_forces_tail_nat [DecidableEq α] :
  A ∈ LogicS ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] →
  ∀ (tail : M.World),
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n → toTail.chainPoint n ⊩[(M.toTail tail).toModel] A :=
  provability_TFAE.out 0 2

theorem iff_forces_root_subfmlsS_imp [DecidableEq α] :
  A ∈ LogicS ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
  M.root.1 ⊩[_] (⋀A.subfmlsS 🡒 A) :=
  provability_TFAE.out 0 3

theorem iff_eventually_forces_tail_nat_concrete [DecidableEq α] :
  A ∈ LogicS ↔ ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] →
  ∀ (tail : M.World), ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
  toTail.chainPoint m ⊩[(M.toTail tail).toModel] A :=
  provability_TFAE.out 0 4

lemma consistent [DecidableEq α] : ⊥ ∉ @LogicS α := by
  intro h;
  obtain ⟨k, hk⟩ :=
    iff_eventually_forces_tail_nat_concrete.mp h 1 (Model.pointModel (fun _ => False)) 0;
  exact hk k le_rfl;

/-- - [KK23] -/
theorem iff_provable_provableGentzen [DecidableEq α] :
    A ∈ LogicS ↔ ⊢ᵍ[S] (∅ ⟹[1] {A}) :=
  provability_TFAE.out 0 1

end LogicS

end
