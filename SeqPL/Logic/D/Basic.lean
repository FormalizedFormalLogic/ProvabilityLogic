module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.S.Basic
public import SeqPL.Kripke.PseudoTail

@[expose]
public section

abbrev LogicD {α} : Logic α := (LogicGL) +ᴸ (insert (∼□⊥) { □(□A ⋎ □B) 🡒 (□A ⋎ □B) | (A) (B) })

lemma LogicS_subset_LogicD : LogicD (α := α) ⊆ LogicS := by
  intro A h;
  induction h with
  | mem₁ h => apply Logic.sumQuasiNormal.mem₁; exact h
  | mdp h₁ h₂ ih₁ ih₂ => apply Logic.sumQuasiNormal.mdp; exact ih₁; exact ih₂
  | subst h ih => apply Logic.sumQuasiNormal.subst; exact ih
  | mem₂ h =>
    rcases h with (rfl | ⟨A, B, rfl⟩);
    . apply Logic.sumQuasiNormal.mem₂;
      use ⊥;
    . apply Logic.sumQuasiNormal.mem₂;
      use (□A ⋎ □B);


universe u
variable {α : Type u}

/-- GL の有限モデル完全性による意味論的な GL 所属証明． -/
lemma LogicGL.provable_of_valid [DecidableEq α] {A : Formula α}
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A) : A ∈ LogicGL :=
  ProvableHilbert.Kripke.completeness h


open scoped FormulaFinset in
/-- `A` の部分論理式から作られる `n` 項公理 D のインスタンスたち． -/
noncomputable def Formula.subfmlsD [DecidableEq α] (A : Formula α) : FormulaFinset α :=
  (A.subfmls.prebox).powerset.image (λ (Γ : FormulaFinset α) => □(⋁(□Γ)) 🡒 ⋁(□Γ))


namespace LogicD

open scoped FormulaFinset

lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicD := Logic.sumQuasiNormal.mem₁ h

lemma provable_axiomP : (∼□⊥ : Formula α) ∈ LogicD :=
  Logic.sumQuasiNormal.mem₂ (Set.mem_insert _ _)

lemma provable_axiomD {A B : Formula α} : (□(□A ⋎ □B) 🡒 (□A ⋎ □B)) ∈ LogicD :=
  Logic.sumQuasiNormal.mem₂ (Set.mem_insert_iff.mpr (Or.inr ⟨A, B, rfl⟩))

section

/-- `subst` を経由しない `LogicD` の内在的定義（`LogicD.substlessInduction` 用）． -/
protected inductive substless : Logic α
  | provable_GL {A} : A ∈ LogicGL → LogicD.substless A
  | axiomP : LogicD.substless (∼□⊥)
  | axiomD (A B) : LogicD.substless (□(□A ⋎ □B) 🡒 (□A ⋎ □B))
  | mdp {A B} : LogicD.substless (A 🡒 B) → LogicD.substless A → LogicD.substless B

private lemma substless.eq_LogicD : LogicD.substless (α := α) = LogicD := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | provable_GL h => exact provable_of_provable_GL h;
    | axiomP => exact provable_axiomP;
    | axiomD A B => exact provable_axiomD;
    | mdp _ _ ihAB ihA => exact Logic.sumQuasiNormal.mdp ihAB ihA;
  . intro h;
    induction h with
    | mem₁ h => exact LogicD.substless.provable_GL h;
    | mem₂ h =>
      rcases h with (rfl | ⟨B, C, rfl⟩);
      . exact LogicD.substless.axiomP;
      . exact LogicD.substless.axiomD B C;
    | mdp _ _ ihAB ihA => exact LogicD.substless.mdp ihAB ihA;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | provable_GL h => exact LogicD.substless.provable_GL (ProvableHilbert.subst h);
      | axiomP => exact LogicD.substless.axiomP;
      | axiomD B C => exact LogicD.substless.axiomD _ _;
      | mdp _ _ ihAB ihA => exact LogicD.substless.mdp ihAB ihA;

private lemma substless.toLogicD {A : Formula α} (h : LogicD.substless A) : A ∈ LogicD :=
  LogicD.substless.eq_LogicD ▸ h

private lemma substless.ofLogicD {A : Formula α} (h : A ∈ LogicD) : LogicD.substless A :=
  LogicD.substless.eq_LogicD.symm ▸ h

/-- `LogicD` の帰納原理：`subst` を経由しない形（GL 部分・公理 P・公理 D・mdp）で帰納できる． -/
protected lemma substlessInduction
  {motive : (A : Formula α) → A ∈ LogicD → Prop}
  (provable_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (axiomP : motive (∼□⊥) provable_axiomP)
  (axiomD : ∀ {A B}, motive (□(□A ⋎ □B) 🡒 (□A ⋎ □B)) provable_axiomD)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicD} → {hA : A ∈ LogicD} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : A ∈ LogicD) → motive A h := by
  intro A h;
  induction LogicD.substless.ofLogicD h with
  | provable_GL hg => exact provable_GL hg;
  | axiomP => exact axiomP;
  | axiomD A B => exact axiomD;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := LogicD.substless.toLogicD hAB) (hA := LogicD.substless.toLogicD hA)
      (ihAB _) (ihA _);

end


variable {A B C : Formula α}

section

/-! ### GL の意味論的補題（有限モデル完全性経由） -/

open Model.World

private lemma GL_taut_trans [DecidableEq α] : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C)) ∈ LogicGL := by
  apply LogicGL.provable_of_valid;
  intro κ _ M _ x;
  grind;

private lemma GL_taut_or_mono [DecidableEq α] : ((A 🡒 B) 🡒 ((C ⋎ A) 🡒 (C ⋎ B))) ∈ LogicGL := by
  apply LogicGL.provable_of_valid;
  intro κ _ M _ x;
  grind;

private lemma GL_box_fdisj_step [DecidableEq α] {Γ : FormulaFinset α} :
    (□(⋁(□(insert A Γ))) 🡒 □(□A ⋎ □(⋁(□Γ)))) ∈ LogicGL := by
  apply LogicGL.provable_of_valid;
  intro κ _ M _ x hx y Rxy;
  have hy := hx y Rxy;
  obtain ⟨C, hC, hyC⟩ := forces_fdisj.mp hy;
  simp only [FormulaFinset.box, Finset.mem_image, Finset.mem_insert] at hC;
  obtain ⟨B, (rfl | hBΓ), rfl⟩ := hC;
  . exact forces_or.mpr (Or.inl hyC);
  . apply forces_or.mpr;
    right;
    intro z Ryz;
    apply forces_fdisj.mpr;
    refine ⟨□B, Finset.mem_image_of_mem _ hBΓ, ?_⟩;
    intro w Rzw;
    exact hyC w (IsTrans.trans _ _ _ Ryz Rzw);

private lemma GL_or_fdisj_insert [DecidableEq α] {Γ : FormulaFinset α} :
    ((□A ⋎ ⋁(□Γ)) 🡒 ⋁(□(insert A Γ))) ∈ LogicGL := by
  apply LogicGL.provable_of_valid;
  intro κ _ M _ x hx;
  rcases forces_or.mp hx with (h | h);
  . exact forces_fdisj.mpr ⟨□A, by simp, h⟩;
  . obtain ⟨C, hC, hxC⟩ := forces_fdisj.mp h;
    exact forces_fdisj.mpr ⟨C, Finset.image_subset_image (Finset.subset_insert _ _) hC, hxC⟩;

end


lemma provable_of_provable_GL_imp [DecidableEq α] (hAB : (A 🡒 B) ∈ LogicGL) (hA : A ∈ LogicD) : B ∈ LogicD :=
  Logic.sumQuasiNormal.mdp (provable_of_provable_GL hAB) hA

lemma provable_imp_trans [DecidableEq α] (h₁ : (A 🡒 B) ∈ LogicD) (h₂ : (B 🡒 C) ∈ LogicD) : (A 🡒 C) ∈ LogicD :=
  Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mdp (provable_of_provable_GL GL_taut_trans) h₁) h₂

/-- `n` 項化された公理 D：`□(□A₁ ⋎ ⋯ ⋎ □Aₙ) 🡒 (□A₁ ⋎ ⋯ ⋎ □Aₙ)` は `LogicD` で証明可能． -/
lemma provable_fdisj_axiomD [DecidableEq α] {Γ : FormulaFinset α} : (□(⋁(□Γ)) 🡒 ⋁(□Γ)) ∈ LogicD := by
  induction Γ using Finset.induction_on with
  | empty => simpa using provable_axiomP;
  | insert A Γ hAΓ ih =>
    have t₁ : (□(⋁(□(insert A Γ))) 🡒 □(□A ⋎ □(⋁(□Γ)))) ∈ LogicD := provable_of_provable_GL GL_box_fdisj_step;
    have t₂ : (□(□A ⋎ □(⋁(□Γ))) 🡒 (□A ⋎ □(⋁(□Γ)))) ∈ LogicD := provable_axiomD;
    have t₃ : ((□A ⋎ □(⋁(□Γ))) 🡒 (□A ⋎ ⋁(□Γ))) ∈ LogicD := provable_of_provable_GL_imp GL_taut_or_mono ih;
    have t₄ : ((□A ⋎ ⋁(□Γ)) 🡒 ⋁(□(insert A Γ))) ∈ LogicD := provable_of_provable_GL GL_or_fdisj_insert;
    exact provable_imp_trans (provable_imp_trans (provable_imp_trans t₁ t₂) t₃) t₄;

lemma provable_lconj_of_forall_provable {Γ : FormulaList α} (h : ∀ B ∈ Γ, B ∈ LogicD) : (⋀Γ) ∈ LogicD := by
  match Γ with
  | [] => exact provable_of_provable_GL ProvableHilbert.top;
  | [B] => exact h B (by simp);
  | B :: C :: Γ =>
    exact Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mdp (provable_of_provable_GL ProvableHilbert.andIntro) (h B (by simp)))
      (provable_lconj_of_forall_provable (Γ := C :: Γ) (by grind));

lemma provable_fconj_of_forall_provable {Γ : FormulaFinset α} (h : ∀ B ∈ Γ, B ∈ LogicD) : (⋀Γ) ∈ LogicD :=
  provable_lconj_of_forall_provable (by simpa)

lemma provable_fconj_subfmlsD [DecidableEq α] : (⋀A.subfmlsD) ∈ LogicD := by
  apply provable_fconj_of_forall_provable;
  intro B hB;
  obtain ⟨Γ, _, rfl⟩ : ∃ Γ ⊆ A.subfmls.prebox, (□(⋁(□Γ)) 🡒 ⋁(□Γ)) = B := by
    simpa [Formula.subfmlsD] using hB;
  exact provable_fdisj_axiomD;


open Model Model.World

/-- `LogicD` の定理は任意の有限 GL モデルの pseudo-tail model の根（ω）で妥当． -/
lemma forces_pseudoTail_root_of_provable [DecidableEq α] (h : A ∈ LogicD) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World) (o : α → Prop),
  Forces (M := (M.toPseudoTail r o).toModel) (M.toPseudoTail r o).root.1 A := by
  intro κ _ M _ r o;
  induction h using LogicD.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.soundness h ((M.toPseudoTail r o).toModel) _;
  | axiomP =>
    intro hbox;
    exact hbox (.inl (Classical.arbitrary κ)) toPseudoTail.rel_inr_inl;
  | @axiomD B C =>
    intro hbox;
    by_contra hC;
    obtain ⟨h₁, h₂⟩ := not_forces_or.mp hC;
    obtain ⟨x, Rrx, hx⟩ := not_forces_box.mp h₁;
    obtain ⟨y, Rry, hy⟩ := not_forces_box.mp h₂;
    have key : ∀ w : (M.toPseudoTail r o).World, (M.toPseudoTail r o).Rel (.inr ⊤) w →
        ∃ k : ℕ, ∀ n : ℕ, k < n → (M.toPseudoTail r o).Rel (.inr ((n : ℕ) : ℕ∞)) w := by
      rintro (w | i) hw;
      . exact ⟨0, fun n _ => toPseudoTail.rel_inr_inl⟩;
      . have hi : i < (⊤ : ℕ∞) := toPseudoTail.rel_inr_inr.mp hw;
        refine ⟨i.toNat, fun n hn => toPseudoTail.rel_inr_inr.mpr ?_⟩;
        calc i = ((i.toNat : ℕ) : ℕ∞) := (ENat.coe_toNat hi.ne).symm
          _ < ((n : ℕ) : ℕ∞) := by exact_mod_cast hn;
    obtain ⟨k₁, hk₁⟩ := key x Rrx;
    obtain ⟨k₂, hk₂⟩ := key y Rry;
    have hz : Forces (M := (M.toPseudoTail r o).toModel) (.inr ((k₁ + k₂ + 1 : ℕ) : ℕ∞)) (□B ⋎ □C) :=
      hbox _ (toPseudoTail.rel_inr_inr.mpr (ENat.coe_lt_top _));
    rcases forces_or.mp hz with (hzB | hzC);
    . exact hx (hzB x (hk₁ _ (by omega)));
    . exact hy (hzC y (hk₂ _ (by omega)));
  | mdp ihAB ihA => exact ihAB ihA;

open Classical in
/--
  pseudo-tail model の根での妥当性から，任意の有限根付き GL モデルの根で `⋀A.subfmlsD 🡒 A` が成立する．
-/
lemma root_forces_subfmlsD_imp [DecidableEq α]
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World) (o : α → Prop),
       Forces (M := (M.toPseudoTail r o).toModel) (M.toPseudoTail r o).root.1 A) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] → M.root.1 ⊩ (⋀A.subfmlsD 🡒 A) := by
  intro κ _ M _;
  by_contra hC;
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hC;
  replace h₁ : ∀ Γ ⊆ A.subfmls.prebox, M.root.1 ⊩ (□(⋁(□Γ)) 🡒 ⋁(□Γ)) := by
    intro Γ hΓ;
    exact forces_fconj.mp h₁ _ (by simp only [Formula.subfmlsD, Finset.mem_image, Finset.mem_powerset]; exact ⟨Γ, hΓ, rfl⟩);
  -- 根で `□B` が反証される部分論理式 `B` を集める
  let Δ := (A.subfmls.prebox).filter (λ (B : Formula α) => ¬(M.root.1 ⊩ □B));
  obtain ⟨x, Rrx, hx⟩ : ∃ x, M.root.1 ≺ x ∧ ∀ B ∈ Δ, ¬(x ⊩ □B) := by
    have hΔ₁ : M.root.1 ⊮ ⋁(□Δ) := by
      intro hd;
      obtain ⟨C, hC, hrC⟩ := forces_fdisj.mp hd;
      obtain ⟨B, hB, rfl⟩ : ∃ B ∈ Δ, □B = C := by simpa using hC;
      exact (Finset.mem_filter.mp hB).2 hrC;
    have hΔ₂ : M.root.1 ⊮ □(⋁(□Δ)) := fun hbox => hΔ₁ (h₁ Δ (Finset.filter_subset _ _) hbox);
    obtain ⟨x, Rrx, hx⟩ := not_forces_box.mp hΔ₂;
    refine ⟨x, Rrx, ?_⟩;
    intro B hB hxB;
    exact hx (forces_fdisj.mpr ⟨□B, Finset.mem_image_of_mem _ hB, hxB⟩);
  -- `x` で点生成した部分モデル
  let N : RootedModel (M.toModel↾x) α := M.toModel.toRootedModel x;
  have hS : ∀ B ∈ A.subfmls.prebox, N.root.1 ⊩ (□B 🡒 B) := by
    intro B hB;
    apply Model.toRootedModel.forces_same_at_root.mpr;
    intro hxB;
    by_cases hBΔ : B ∈ Δ;
    . exact absurd hxB (hx B hBΔ);
    . have : M.root.1 ⊩ □B := by
        have := Finset.mem_filter.not.mp hBΔ;
        push Not at this;
        exact this hB;
      exact this x Rrx;
  have hA := h N.toModel N.root.1 (M.Val M.root.1);
  -- `A` の部分論理式について，pseudo-tail model の根（ω）と元の `M` の根で forces が一致する
  have transport : ∀ B, B ∈ A.subfmls →
      (Forces (M := (N.toModel.toPseudoTail N.root.1 (M.Val M.root.1)).toModel) (.inr ⊤) B ↔ M.root.1 ⊩ B) := by
    intro B;
    induction B with
    | atom a =>
      intro _;
      show (if ((⊤ : ℕ∞) = (⊤ : ℕ∞)) then M.Val M.root.1 a else N.toModel.Val N.root.1 a) ↔ M.Val M.root.1 a;
      rw [if_pos rfl];
    | bot => intro _; exact Iff.rfl;
    | imp B C ihB ihC =>
      intro hBC;
      replace ihB := ihB (Formula.subfmls_trans hBC (by grind));
      replace ihC := ihC (Formula.subfmls_trans hBC (by grind));
      constructor;
      . intro hi hB; exact ihC.mp (hi (ihB.mpr hB));
      . intro hi hB; exact ihC.mpr (hi (ihB.mp hB));
    | box B ihB =>
      intro hB;
      constructor;
      . intro hω;
        have hxB : x ⊩ □B := by
          have hl : Forces (M := (N.toModel.toPseudoTail N.root.1 (M.Val M.root.1)).toModel) (.inl N.root.1) (□B) :=
            Model.toPseudoTail.forces_box_of_root_forces_box hω;
          exact Model.toRootedModel.forces_same_at_root.mp (Model.toPseudoTail.forces_inl.mp hl);
        by_contra hroot;
        exact hx B (Finset.mem_filter.mpr ⟨by grind, hroot⟩) hxB;
      . intro hroot;
        rintro (w | j) Rωw;
        . apply Model.toPseudoTail.forces_inl.mpr;
          apply Model.toRootedModel.forces_same_at_successor.mpr;
          rcases w.2 with (hwx | hxw);
          . rw [hwx]; exact hroot _ Rrx;
          . exact hroot _ (IsTrans.trans _ _ _ Rrx hxw);
        . have hj : j < (⊤ : ℕ∞) := Model.toPseudoTail.rel_inr_inr.mp Rωw;
          obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hj.ne;
          apply (Model.toPseudoTail.root_forces_iff_forces_nat (M := N) (o := M.Val M.root.1) (S := A.subfmls)
            (fun B hB => Formula.subfmls_trans hB) hS B (Formula.subfmls_trans hB (by grind)) m).mp;
          apply Model.toRootedModel.forces_same_at_root.mpr;
          exact hroot x Rrx;
  exact h₂ ((transport A (by grind)).mp hA);


/-- **Logic D の GL による特徴づけ**（pseudo-tail model による意味論的証明）． -/
theorem provability_TFAE [DecidableEq α] : [
    A ∈ LogicD,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World) (o : α → Prop),
      Forces (M := (M.toPseudoTail r o).toModel) (M.toPseudoTail r o).root.1 A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] → M.root.1 ⊩ (⋀A.subfmlsD 🡒 A),
    (⋀A.subfmlsD 🡒 A) ∈ LogicGL
  ].TFAE := by
  tfae_have 1 → 2 := forces_pseudoTail_root_of_provable;
  tfae_have 2 → 3 := root_forces_subfmlsD_imp;
  tfae_have 3 ↔ 4 := LogicGL_semantical_TFAE.out 2 0;
  tfae_have 4 → 1 := fun h => Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_fconj_subfmlsD;
  tfae_finish;

theorem iff_provable_D_provable_GL [DecidableEq α] :
    A ∈ LogicD ↔ (⋀A.subfmlsD 🡒 A) ∈ LogicGL := provability_TFAE.out 0 3

end LogicD

end
