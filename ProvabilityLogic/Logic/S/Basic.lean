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

namespace LogicS

@[grind →]
lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicS :=
  Logic.sumQuasiNormal.mem₁ h

lemma provable_axiomT {A : Formula α} : (□A 🡒 A) ∈ LogicS := Logic.sumQuasiNormal.mem₂ ⟨A, rfl⟩

section

/-- Intrinsic definition of `LogicS` avoiding `subst` (for `LogicS.substlessInduction`). -/
private inductive substless : Logic α
  | provable_GL {A} : A ∈ LogicGL → LogicS.substless A
  | axiomT (A) : LogicS.substless (□A 🡒 A)
  | mdp {A B} : LogicS.substless (A 🡒 B) → LogicS.substless A → LogicS.substless B

private lemma substless.eq_LogicS : LogicS.substless (α := α) = LogicS := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | provable_GL h => exact provable_of_provable_GL h;
    | axiomT A => exact provable_axiomT;
    | mdp _ _ ihAB ihA => exact Logic.sumQuasiNormal.mdp ihAB ihA;
  . intro h;
    induction h with
    | mem₁ h => exact LogicS.substless.provable_GL h;
    | mem₂ h =>
      obtain ⟨B, rfl⟩ := h;
      exact LogicS.substless.axiomT B;
    | mdp _ _ ihAB ihA => exact LogicS.substless.mdp ihAB ihA;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | provable_GL h => exact LogicS.substless.provable_GL (ProvableHilbert.subst h);
      | axiomT B => exact LogicS.substless.axiomT _;
      | mdp _ _ ihAB ihA => exact LogicS.substless.mdp ihAB ihA;

private lemma substless.toLogicS {A : Formula α} (h : LogicS.substless A) : A ∈ LogicS :=
  LogicS.substless.eq_LogicS ▸ h

private lemma substless.ofLogicS {A : Formula α} (h : A ∈ LogicS) : LogicS.substless A :=
  LogicS.substless.eq_LogicS.symm ▸ h

/-- Induction principle for `LogicS` avoiding `subst` (GL part, axiom T, mdp). -/
protected lemma substlessInduction
  {motive : (A : Formula α) → A ∈ LogicS → Prop}
  (provable_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (axiomT : ∀ {A}, motive (□A 🡒 A) provable_axiomT)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicS} → {hA : A ∈ LogicS} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : A ∈ LogicS) → motive A h := by
  intro A h;
  induction LogicS.substless.ofLogicS h with
  | provable_GL hg => exact provable_GL hg;
  | axiomT A => exact axiomT;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := LogicS.substless.toLogicS hAB) (hA := LogicS.substless.toLogicS hA)
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

/-- Theorems of `LogicS` are eventually forced along the chain of the tail model of any
finite GL model. -/
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

/-- From eventual forcing along the tail-model chain, the root of any finite rooted GL model
forces `⋀A.subfmlsS 🡒 A`. -/
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


/--
  Bridge between `Model.World.IsReflexiveOf` (over the boxed prebox-subformulas of `A`) and
  forcing the conjunction `⋀A.subfmlsS` of the corresponding instances of the T axiom.
-/
lemma isReflexive_prebox_box_iff_forces_fconj_subfmlsS [DecidableEq α]
  {κ : Type v} [Nonempty κ] {M : Model κ α} {x : M.World} :
  x.IsReflexiveOf (A.subfmls.prebox.box) ↔ x ⊩[_] ⋀A.subfmlsS := by
  simp [Model.World.IsReflexiveOf, forces_fconj, Formula.subfmlsS, FormulaFinset.box]

/--
  From `GL`-provability of `⋀A.subfmlsS 🡒 A`, the finite set `A.subfmls.prebox.box` witnesses
  forcing of `∅ ⟹ {A}` at every reflexive world of every `GL`-model.
-/
lemma exists_isReflexive_forces_of_GL_provable [DecidableEq α]
  (h : (⋀A.subfmlsS 🡒 A) ∈ LogicGL) :
  ∃ X : FormulaFinset α, ∀ {κ : Type v}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsGL] →
  ∀ (x : M.ReflexiveWorldOf X), (x : M.World) ⊩[_] ((∅ : FormulaFinset α) ⟹ {A}) := by
  use A.subfmls.prebox.box;
  intro κ _ M _ x;
  have hHilbert := LogicGL.iff_provableHilbert.mp h;
  have hsound := ProvableHilbert.Kripke.soundness hHilbert M (x : M.World);
  have hAnt := isReflexive_prebox_box_iff_forces_fconj_subfmlsS.mp x.2;
  apply Model.World.forces_singleton_sequent.mpr;
  grind

/-- Direction `6 → 2` of `provability_TFAE`: `GL`-provability of `⋀A.subfmlsS 🡒 A` yields a
`LogicS.ProofGentzen`-proof of the level-`1` sequent `∅ ⟹[1] {A}`. -/
lemma provableGentzen_of_GL_provable [DecidableEq α]
  (h : (⋀A.subfmlsS 🡒 A) ∈ LogicGL) :
  ⊢ᵍ[S] ((∅ : FormulaFinset α) ⟹[1] ({A} : FormulaFinset α)) := by
  apply ProvableGentzen.Kripke.completeness;
  intro κ _ M _ w hw;
  obtain ⟨X, hX⟩ := exists_isReflexive_forces_of_GL_provable h;
  obtain ⟨i, hi⟩ := eventually_forces_of_exists_isReflexive_forces (fun {κ} _ M _ => ⟨X, hX M⟩) M w hw;
  exact ⟨i, hi i (le_refl i)⟩;

/-- Direction `2 → 3` of `provability_TFAE`: `LogicS.ProofGentzen`-provability of the level-`1`
sequent `∅ ⟹[1] {A}` yields eventual forcing of `A` along the tail-model chain. -/
lemma eventually_forces_tail_nat_of_provableGentzen [DecidableEq α]
  (h : ⊢ᵍ[S] ((∅ : FormulaFinset α) ⟹[1] ({A} : FormulaFinset α))) :
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
  GL-characterization of `LogicS`: `S ⊢ A` iff `GL ⊢ ⋀{□B 🡒 B | □B ∈ Sub(A)} 🡒 A`. Also
  characterized by `LogicS.ProofGentzen`-provability of the level-`1` sequent `∅ ⟹[1] {A}`,
  the two-level sequent calculus for `S`.

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
  tfae_have 6 → 1 := fun h => Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_fconj_subfmlsS;
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

/-- `LogicS`-provability characterized by eventual forcing along the tail-model chain of any
finite `GL` model, over an arbitrary index type `κ`. -/
theorem iff_eventually_forces_tail_nat [DecidableEq α] :
    A ∈ LogicS ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] →
      ∀ (tail : M.World),
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n → toTail.chainPoint n ⊩[(M.toTail tail).toModel] A :=
  provability_TFAE.out 0 2

/-- `LogicS`-provability characterized by root-forcing of `⋀A.subfmlsS 🡒 A` at every finite `GL`
rooted model. -/
theorem iff_forces_root_subfmlsS_imp [DecidableEq α] :
    A ∈ LogicS ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩[_] (⋀A.subfmlsS 🡒 A) :=
  provability_TFAE.out 0 3

theorem iff_eventually_forces_tail_nat_concrete [DecidableEq α] :
    A ∈ LogicS ↔ ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] →
      ∀ (tail : M.World), ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
        toTail.chainPoint m ⊩[(M.toTail tail).toModel] A :=
  provability_TFAE.out 0 4

/-- `LogicS` is consistent: `⊥` is not a theorem. -/
lemma consistent [DecidableEq α] : ⊥ ∉ @LogicS α := by
  intro h;
  -- A theorem of `S` is eventually forced on the chain of the tail model of any finite GL
  -- model, but `⊥` is forced nowhere; take the one-point GL model with the empty relation.
  obtain ⟨k, hk⟩ :=
    iff_eventually_forces_tail_nat_concrete.mp h 1 (Model.pointModel (fun _ => False)) 0;
  exact hk k le_rfl;

/--
  `S ⊢ A` iff the level-`1` sequent `∅ ⟹[1] {A}` is provable in `LogicS.ProofGentzen`,
  the cut-free sequent calculus for `S`.

  - [KK23]
-/
theorem iff_provable_provableGentzen [DecidableEq α] :
    A ∈ LogicS ↔ ⊢ᵍ[S] ((∅ : FormulaFinset α) ⟹[1] ({A} : FormulaFinset α)) :=
  provability_TFAE.out 0 1

end LogicS

end
