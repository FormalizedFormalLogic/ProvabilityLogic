module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.GL.Basic
public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.Tail

@[expose]
public section

abbrev LogicS {α} : Logic α := (LogicGL) +ᴸ ({ □A 🡒 A | A })

universe u
variable {α : Type u}

/-- Instances of the T axiom `□B 🡒 B` built from the subformulas of `A`. -/
noncomputable def Formula.subfmlsS [DecidableEq α] (A : Formula α) : FormulaFinset α :=
  (A.subfmls.prebox).image (λ B => □B 🡒 B)


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
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) A := by
  intro κ _ M _ tail;
  induction h using LogicS.substlessInduction with
  | provable_GL h =>
    exact ⟨0, fun n _ => ProvableHilbert.Kripke.soundness h ((M.toTail tail).toModel) _⟩;
  | @axiomT B =>
    obtain ⟨k, hk⟩ := toTail.forces_nat_eventually_stable (M := M) (tail := tail) B;
    use k + 1;
    intro n hn hbox;
    have hBk : Forces (M := (M.toTail tail).toModel) (toTail.chainPoint k) B :=
      hbox (toTail.chainPoint k)
        (toTail.rel_chainPoint_chainPoint.mpr (by exact_mod_cast Nat.lt_of_succ_le hn));
    exact (hk n (by omega)).mpr hBk;
  | mdp ihAB ihA =>
    obtain ⟨k₁, h₁⟩ := ihAB;
    obtain ⟨k₂, h₂⟩ := ihA;
    exact ⟨max k₁ k₂, fun n hn =>
      h₁ n (le_trans (le_max_left _ _) hn) (h₂ n (le_trans (le_max_right _ _) hn))⟩;

/-- `LogicS` is consistent: `⊥` is not a theorem. -/
lemma consistent [DecidableEq α] : ⊥ ∉ @LogicS α := by
  intro h;
  -- A theorem of `S` is eventually forced on the chain of the tail model of any finite GL
  -- model, but `⊥` is forced nowhere; take the one-point GL model with the empty relation.
  let M : Model PUnit.{u + 1} α := ⟨fun _ _ => False, fun _ _ => False⟩;
  haveI : M.IsFiniteGL :=
    { trans := fun _ _ _ hf _ => hf.elim
      irrefl := fun _ hf => hf
      finite := inferInstance };
  obtain ⟨k, hk⟩ := eventually_forces_tail_nat_of_provable h M PUnit.unit;
  exact hk k le_rfl;

/-- From eventual forcing along the tail-model chain, the root of any finite rooted GL model
forces `⋀A.subfmlsS 🡒 A`. -/
lemma root_forces_subfmlsS_imp [DecidableEq α]
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
       ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) A) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
  M.root.1 ⊩ (⋀A.subfmlsS 🡒 A) := by
  intro κ _ M _ h₁;
  have hΓ : ∀ B ∈ A.subfmls.prebox, M.root.1 ⊩ (□B 🡒 B) := by
    intro B hB;
    exact forces_fconj.mp h₁ _ (by
      simp only [Formula.subfmlsS, Finset.mem_image];
      exact ⟨B, hB, rfl⟩);
  obtain ⟨k, hk⟩ := h M.toModel M.root.1;
  exact (toTail.root_forces_iff_forces_nat (Γ := A.subfmls)
    (fun B hB => Formula.subfmls_trans hB) hΓ A Formula.mem_subfmls_self k).mpr (hk k le_rfl);


/-- GL-characterization of `LogicS`: `S ⊢ A` iff `GL ⊢ ⋀{□B 🡒 B | □B ∈ Sub(A)} 🡒 A`. -/
theorem provability_TFAE [DecidableEq α] : [
    A ∈ LogicS,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (tail : M.World),
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail tail).toModel) (toTail.chainPoint n) A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩ (⋀A.subfmlsS 🡒 A),
    (⋀A.subfmlsS 🡒 A) ∈ LogicGL
  ].TFAE := by
  tfae_have 1 → 2 := eventually_forces_tail_nat_of_provable;
  tfae_have 2 → 3 := root_forces_subfmlsS_imp;
  tfae_have 3 ↔ 4 := LogicGL.iff_forces_root.symm;
  tfae_have 4 → 1 := fun h => Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_fconj_subfmlsS;
  tfae_finish;

theorem iff_provable_S_provable_GL [DecidableEq α] :
    A ∈ LogicS ↔ (⋀A.subfmlsS 🡒 A) ∈ LogicGL := provability_TFAE.out 0 3

end LogicS

end
