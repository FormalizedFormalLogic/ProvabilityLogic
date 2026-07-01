module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.S.Basic
public import SeqPL.Kripke.Tail

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
variable {α : Type u} {A B C : Formula α}

/-- GL の有限モデル完全性による意味論的な GL 所属証明． -/
lemma LogicGL.mem_of_valid [DecidableEq α]
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A) : A ∈ LogicGL :=
  ProvableHilbert.Kripke.completeness h


namespace LogicD

lemma mem_of_mem_GL (h : A ∈ LogicGL) : A ∈ LogicD := Logic.sumQuasiNormal.mem₁ h

lemma mem_axiomP : (∼□⊥ : Formula α) ∈ LogicD :=
  Logic.sumQuasiNormal.mem₂ (Set.mem_insert _ _)

lemma mem_axiomDz : (□(□A ⋎ □B) 🡒 (□A ⋎ □B)) ∈ LogicD :=
  Logic.sumQuasiNormal.mem₂ (Set.mem_insert_iff.mpr (Or.inr ⟨A, B, rfl⟩))

section

private inductive D' {β : Type u} : Logic β
  | mem_GL {X} : X ∈ LogicGL → D' X
  | axiomP : D' (∼□⊥)
  | axiomDz (X Y) : D' (□(□X ⋎ □Y) 🡒 (□X ⋎ □Y))
  | mdp {X Y} : D' (X 🡒 Y) → D' X → D' Y

private lemma D'.eq_LogicD : D' (β := α) = LogicD := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | mem_GL h => exact mem_of_mem_GL h;
    | axiomP => exact mem_axiomP;
    | axiomDz A B => exact mem_axiomDz;
    | mdp _ _ ihAB ihA => exact Logic.sumQuasiNormal.mdp ihAB ihA;
  . intro h;
    induction h with
    | mem₁ h => exact D'.mem_GL h;
    | mem₂ h =>
      rcases h with (rfl | ⟨B, C, rfl⟩);
      . exact D'.axiomP;
      . exact D'.axiomDz B C;
    | mdp _ _ ihAB ihA => exact D'.mdp ihAB ihA;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | mem_GL h => exact D'.mem_GL (ProvableHilbert.subst h);
      | axiomP => exact D'.axiomP;
      | axiomDz B C => exact D'.axiomDz _ _;
      | mdp _ _ ihAB ihA => exact D'.mdp ihAB ihA;

private lemma D'.toLogicD {A : Formula α} (h : D' A) : A ∈ LogicD := D'.eq_LogicD ▸ h

private lemma D'.ofLogicD {A : Formula α} (h : A ∈ LogicD) : D' A := D'.eq_LogicD.symm ▸ h

private lemma rec'_aux
  {motive : (A : Formula α) → A ∈ LogicD → Prop}
  (mem_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (mem_of_mem_GL h))
  (axiomP : motive (∼□⊥) mem_axiomP)
  (axiomDz : ∀ {A B}, motive (□(□A ⋎ □B) 🡒 (□A ⋎ □B)) mem_axiomDz)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicD} → {hA : A ∈ LogicD} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : D' A) → motive A (D'.toLogicD h) := by
  intro A h;
  induction h with
  | mem_GL hg => exact mem_GL hg;
  | axiomP => exact axiomP;
  | axiomDz X Y => exact axiomDz;
  | mdp hXY hX ihXY ihX =>
    exact mdp (hAB := D'.toLogicD hXY) (hA := D'.toLogicD hX) ihXY ihX;

/-- `LogicD` の帰納原理：`subst` を経由しない形（GL 部分・公理 P・公理 Dz・mdp）で帰納できる． -/
protected lemma rec'
  {motive : (A : Formula α) → A ∈ LogicD → Prop}
  (mem_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (mem_of_mem_GL h))
  (axiomP : motive (∼□⊥) mem_axiomP)
  (axiomDz : ∀ {A B}, motive (□(□A ⋎ □B) 🡒 (□A ⋎ □B)) mem_axiomDz)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicD} → {hA : A ∈ LogicD} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : A ∈ LogicD) → motive A h := by
  intro A h;
  exact rec'_aux (motive := motive) mem_GL axiomP axiomDz mdp (D'.ofLogicD h);

end


section

/-! ### GL の意味論的補題（有限モデル完全性経由） -/

open Model.World

private lemma GL_taut_trans [DecidableEq α] : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C)) ∈ LogicGL := by
  apply LogicGL.mem_of_valid;
  intro κ _ M _ x;
  grind;

private lemma GL_taut_or_mono [DecidableEq α] : ((A 🡒 B) 🡒 ((C ⋎ A) 🡒 (C ⋎ B))) ∈ LogicGL := by
  apply LogicGL.mem_of_valid;
  intro κ _ M _ x;
  grind;

private lemma GL_box_fdisj_step [DecidableEq α] {Γ : FormulaFinset α} :
    (□(⋁((FormulaFinset.box (insert A Γ)))) 🡒 □(□A ⋎ □(⋁((FormulaFinset.box Γ))))) ∈ LogicGL := by
  apply LogicGL.mem_of_valid;
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
    ((□A ⋎ ⋁((FormulaFinset.box Γ))) 🡒 ⋁((FormulaFinset.box (insert A Γ)))) ∈ LogicGL := by
  apply LogicGL.mem_of_valid;
  intro κ _ M _ x hx;
  rcases forces_or.mp hx with (h | h);
  . exact forces_fdisj.mpr ⟨□A, by simp, h⟩;
  . obtain ⟨C, hC, hxC⟩ := forces_fdisj.mp h;
    exact forces_fdisj.mpr ⟨C, Finset.image_subset_image (Finset.subset_insert _ _) hC, hxC⟩;

end


lemma mem_of_mem_GL_imp [DecidableEq α] (hAB : (A 🡒 B) ∈ LogicGL) (hA : A ∈ LogicD) : B ∈ LogicD :=
  Logic.sumQuasiNormal.mdp (mem_of_mem_GL hAB) hA

lemma mem_imp_trans [DecidableEq α] (h₁ : (A 🡒 B) ∈ LogicD) (h₂ : (B 🡒 C) ∈ LogicD) : (A 🡒 C) ∈ LogicD :=
  Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mdp (mem_of_mem_GL GL_taut_trans) h₁) h₂

/-- `n` 項化された公理 Dz：`□(□A₁ ⋎ ⋯ ⋎ □Aₙ) 🡒 (□A₁ ⋎ ⋯ ⋎ □Aₙ)` は `LogicD` で証明可能． -/
lemma mem_fdisj_axiomDz [DecidableEq α] {Γ : FormulaFinset α} : (□(⋁((FormulaFinset.box Γ))) 🡒 ⋁((FormulaFinset.box Γ))) ∈ LogicD := by
  induction Γ using Finset.induction_on with
  | empty => simpa using mem_axiomP;
  | insert A Γ hAΓ ih =>
    have t₁ : (□(⋁((FormulaFinset.box (insert A Γ)))) 🡒 □(□A ⋎ □(⋁((FormulaFinset.box Γ))))) ∈ LogicD := mem_of_mem_GL GL_box_fdisj_step;
    have t₂ : (□(□A ⋎ □(⋁((FormulaFinset.box Γ)))) 🡒 (□A ⋎ □(⋁((FormulaFinset.box Γ))))) ∈ LogicD := mem_axiomDz;
    have t₃ : ((□A ⋎ □(⋁((FormulaFinset.box Γ)))) 🡒 (□A ⋎ ⋁((FormulaFinset.box Γ)))) ∈ LogicD := mem_of_mem_GL_imp GL_taut_or_mono ih;
    have t₄ : ((□A ⋎ ⋁((FormulaFinset.box Γ))) 🡒 ⋁((FormulaFinset.box (insert A Γ)))) ∈ LogicD := mem_of_mem_GL GL_or_fdisj_insert;
    exact mem_imp_trans (mem_imp_trans (mem_imp_trans t₁ t₂) t₃) t₄;

lemma mem_lconj_of_forall_mem {Γ : FormulaList α} (h : ∀ B ∈ Γ, B ∈ LogicD) : (⋀Γ) ∈ LogicD := by
  match Γ with
  | [] => exact mem_of_mem_GL ProvableHilbert.top;
  | [B] => exact h B (by simp);
  | B :: C :: Γ =>
    exact Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mdp (mem_of_mem_GL ProvableHilbert.andIntro) (h B (by simp)))
      (mem_lconj_of_forall_mem (Γ := C :: Γ) (by grind));

lemma mem_fconj_of_forall_mem {Γ : FormulaFinset α} (h : ∀ B ∈ Γ, B ∈ LogicD) : (⋀Γ) ∈ LogicD :=
  mem_lconj_of_forall_mem (by simpa)

end LogicD


/-- `A` の部分論理式から作られる `n` 項公理 Dz のインスタンスたち． -/
noncomputable def Formula.dzSubfmls [DecidableEq α] (A : Formula α) : FormulaFinset α :=
  (A.subfmls.prebox).powerset.image (λ Γ => □(⋁((FormulaFinset.box Γ))) 🡒 ⋁((FormulaFinset.box Γ)))

namespace LogicD

lemma mem_fconj_dzSubfmls [DecidableEq α] : (⋀A.dzSubfmls) ∈ LogicD := by
  apply mem_fconj_of_forall_mem;
  intro B hB;
  obtain ⟨Γ, _, rfl⟩ : ∃ Γ ⊆ A.subfmls.prebox, (□(⋁((FormulaFinset.box Γ))) 🡒 ⋁((FormulaFinset.box Γ))) = B := by
    simpa [Formula.dzSubfmls] using hB;
  exact mem_fdisj_axiomDz;


open Model Model.World

/-- `LogicD` の定理は任意の有限 GL モデルの pseudo-tail model の根（ω）で妥当． -/
lemma forces_pseudoTail_root_of_mem [DecidableEq α] (h : A ∈ LogicD) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World) (o : α → Prop),
  Forces (M := (M.toPseudoTail r o).toModel) (M.toPseudoTail r o).root.1 A := by
  intro κ _ M _ r o;
  induction h using LogicD.rec' with
  | mem_GL h => exact ProvableHilbert.Kripke.soundness h ((M.toPseudoTail r o).toModel) _;
  | axiomP =>
    intro hbox;
    exact hbox (.inl (Classical.arbitrary κ)) toPseudoTail.rel_inr_inl;
  | @axiomDz B C =>
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
  pseudo-tail model の根での妥当性から，任意の有限根付き GL モデルの根で `⋀A.dzSubfmls 🡒 A` が成立する．
-/
lemma root_forces_dzSubfmls_imp [DecidableEq α]
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ (r : M.World) (o : α → Prop),
       Forces (M := (M.toPseudoTail r o).toModel) (M.toPseudoTail r o).root.1 A) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] → M.root.1 ⊩ (⋀A.dzSubfmls 🡒 A) := by
  intro κ _ M _;
  by_contra hC;
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hC;
  replace h₁ : ∀ Γ ⊆ A.subfmls.prebox, M.root.1 ⊩ (□(⋁((FormulaFinset.box Γ))) 🡒 ⋁((FormulaFinset.box Γ))) := by
    intro Γ hΓ;
    exact forces_fconj.mp h₁ _ (by simp only [Formula.dzSubfmls, Finset.mem_image, Finset.mem_powerset]; exact ⟨Γ, hΓ, rfl⟩);
  -- 根で `□B` が反証される部分論理式 `B` を集める
  let X := (A.subfmls.prebox).filter (λ B => ¬(M.root.1 ⊩ □B));
  obtain ⟨x, Rrx, hx⟩ : ∃ x, M.root.1 ≺ x ∧ ∀ B ∈ X, ¬(x ⊩ □B) := by
    have hX₁ : M.root.1 ⊮ ⋁((FormulaFinset.box X)) := by
      intro hd;
      obtain ⟨C, hC, hrC⟩ := forces_fdisj.mp hd;
      obtain ⟨B, hB, rfl⟩ : ∃ B ∈ X, □B = C := by simpa using hC;
      exact (Finset.mem_filter.mp hB).2 hrC;
    have hX₂ : M.root.1 ⊮ □(⋁((FormulaFinset.box X))) := fun hbox => hX₁ (h₁ X (Finset.filter_subset _ _) hbox);
    obtain ⟨x, Rrx, hx⟩ := not_forces_box.mp hX₂;
    refine ⟨x, Rrx, ?_⟩;
    intro B hB hxB;
    exact hx (forces_fdisj.mpr ⟨□B, Finset.mem_image_of_mem _ hB, hxB⟩);
  -- `x` で点生成した部分モデル
  let N : RootedModel (M.toModel↾x) α := M.toModel.toRootedModel x;
  have hS : ∀ B ∈ A.subfmls.prebox, N.root.1 ⊩ (□B 🡒 B) := by
    intro B hB;
    apply Model.toRootedModel.forces_same_at_root.mpr;
    intro hxB;
    by_cases hBX : B ∈ X;
    . exact absurd hxB (hx B hBX);
    . have : M.root.1 ⊩ □B := by
        have := Finset.mem_filter.not.mp hBX;
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

end LogicD


open LogicD in
/-- **Logic D の GL による特徴づけ**（pseudo-tail model による意味論的証明）． -/
theorem iff_provable_D_provable_GL [DecidableEq α] {A : Formula α} :
    A ∈ LogicD ↔ (⋀A.dzSubfmls 🡒 A) ∈ LogicGL := by
  constructor;
  . intro h;
    apply LogicGL_semantical_TFAE.out 0 2 |>.mpr;
    intro κ _ M _;
    exact root_forces_dzSubfmls_imp (forces_pseudoTail_root_of_mem h) M;
  . intro h;
    exact Logic.sumQuasiNormal.mdp (mem_of_mem_GL h) mem_fconj_dzSubfmls;

end
