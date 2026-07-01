module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.S.Basic
public import SeqPL.Kripke.Tail

@[expose]
public section

universe u
variable {α : Type u}

/-- `A` の部分論理式から作られる公理 T（`□B 🡒 B`）のインスタンスたち． -/
noncomputable def Formula.subfmlsS [DecidableEq α] (A : Formula α) : FormulaFinset α :=
  (A.subfmls.prebox).image (λ B => □B 🡒 B)


namespace LogicS

lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicS :=
  Logic.sumQuasiNormal.mem₁ h

lemma provable_axiomT {A : Formula α} : (□A 🡒 A) ∈ LogicS := Logic.sumQuasiNormal.mem₂ ⟨A, rfl⟩

section

/-- `subst` を経由しない `LogicS` の内在的定義（`LogicS.substlessInduction` 用）． -/
protected inductive substless : Logic α
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

/-- `LogicS` の帰納原理：`subst` を経由しない形（GL 部分・公理 T・mdp）で帰納できる． -/
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

/-- `LogicS` の定理は任意の有限 GL モデルの tail model の鎖上で最終的に成立する． -/
lemma eventually_forces_tail_nat_of_provable [DecidableEq α] (h : A ∈ LogicS) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World),
  ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail r).toModel) (.inr (n : ℕ∞)) A := by
  intro κ _ M _ r;
  induction h using LogicS.substlessInduction with
  | provable_GL h =>
    exact ⟨0, fun n _ => ProvableHilbert.Kripke.soundness h ((M.toTail r).toModel) _⟩;
  | @axiomT B =>
    obtain ⟨k, hk⟩ := toTail.forces_nat_eventually_stable (M := M) (r := r) B;
    refine ⟨k + 1, fun n hn hbox => ?_⟩;
    have hBk : Forces (M := (M.toTail r).toModel) (.inr (k : ℕ∞)) B :=
      hbox (.inr (k : ℕ∞)) (toTail.rel_inr_inr.mpr (by exact_mod_cast Nat.lt_of_succ_le hn));
    exact (hk n (by omega)).mpr hBk;
  | mdp ihAB ihA =>
    obtain ⟨k₁, h₁⟩ := ihAB;
    obtain ⟨k₂, h₂⟩ := ihA;
    exact ⟨max k₁ k₂, fun n hn =>
      h₁ n (le_trans (le_max_left _ _) hn) (h₂ n (le_trans (le_max_right _ _) hn))⟩;

/--
  tail model の鎖上での最終的成立から，任意の有限根付き GL モデルの根で
  `⋀A.subfmlsS 🡒 A` が成立する．
-/
lemma root_forces_subfmlsS_imp [DecidableEq α]
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World),
       ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail r).toModel) (.inr (n : ℕ∞)) A) :
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


/--
  **Logic S の GL による特徴づけ**（tail model による意味論的証明）：
  `S ⊢ A` ↔ `GL ⊢ ⋀{□B 🡒 B | □B ∈ Sub(A)} 🡒 A`．
  Foundation の `GL_S_TFAE`（主張 1・2 の同値性）の算術的完全性を経由しない証明．
-/
theorem provability_TFAE [DecidableEq α] : [
    A ∈ LogicS,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World),
      ∃ k : ℕ, ∀ n : ℕ, k ≤ n → Forces (M := (M.toTail r).toModel) (.inr (n : ℕ∞)) A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩ (⋀A.subfmlsS 🡒 A),
    (⋀A.subfmlsS 🡒 A) ∈ LogicGL
  ].TFAE := by
  tfae_have 1 → 2 := eventually_forces_tail_nat_of_provable;
  tfae_have 2 → 3 := root_forces_subfmlsS_imp;
  tfae_have 3 ↔ 4 := LogicGL_semantical_TFAE.out 2 0;
  tfae_have 4 → 1 := fun h => Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_fconj_subfmlsS;
  tfae_finish;

theorem iff_provable_S_provable_GL [DecidableEq α] :
    A ∈ LogicS ↔ (⋀A.subfmlsS 🡒 A) ∈ LogicGL := provability_TFAE.out 0 3

end LogicS

end
