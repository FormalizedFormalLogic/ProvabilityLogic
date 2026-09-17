module

public import ProvabilityLogic.Logic.S.Basic
public import ProvabilityLogic.Gentzen.D.Kripke

@[expose]
public section

abbrev LogicD {α} : Logic α := (LogicGL) +ᴸ (insert (∼□⊥) { □(□A ⋎ □B) 🡒 (□A ⋎ □B) | (A) (B) })

lemma LogicS_subset_LogicD : LogicD (α := α) ⊆ LogicS := by
  intro A h;
  induction h with
  | mem₁ h => exact Logic.sumQuasiNormal.mem₁ h
  | mdp h₁ h₂ ih₁ ih₂ => exact Logic.sumQuasiNormal.mdp ih₁ ih₂
  | subst h ih => exact Logic.sumQuasiNormal.subst ih
  | mem₂ h =>
    rcases h with (rfl | ⟨A, B, rfl⟩);
    . exact Logic.sumQuasiNormal.mem₂ ⟨⊥, rfl⟩;
    . exact Logic.sumQuasiNormal.mem₂ ⟨□A ⋎ □B, rfl⟩;


universe u
variable {α : Type u}

open LogicGL

lemma LogicGL.provable_of_valid [DecidableEq α] {A : Formula α}
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A) :
  A ∈ LogicGL :=
  iff_forces.mpr h


open scoped FormulaFinset in
/-- The `n`-ary axiom `D` instances built from the subformulas of `A`. -/
noncomputable def Formula.subfmlsD [DecidableEq α] (A : Formula α) : FormulaFinset α :=
  (A.subfmls.prebox).powerset.image (fun (Γ : FormulaFinset α) => □(⋁(□Γ)) 🡒 ⋁(□Γ))


namespace LogicD

open scoped FormulaFinset

lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicD := Logic.sumQuasiNormal.mem₁ h

lemma provable_axiomP : (∼□⊥ : Formula α) ∈ LogicD :=
  Logic.sumQuasiNormal.mem₂ (Set.mem_insert _ _)

lemma provable_axiomD {A B : Formula α} : (□(□A ⋎ □B) 🡒 (□A ⋎ □B)) ∈ LogicD :=
  Logic.sumQuasiNormal.mem₂ (Set.mem_insert_iff.mpr (Or.inr ⟨A, B, rfl⟩))

lemma provable_neg_boxItr_bot [DecidableEq α] {n : ℕ} : (∼□^[n]⊥ : Formula α) ∈ LogicD := by
  match n with
  | 0 => exact provable_of_provable_GL (iff_forces.mpr (by grind));
  | n + 1 =>
    induction n with
    | zero => simpa [Formula.boxItr_one] using provable_axiomP;
    | succ n ih =>
      have h : ((□(□^[n + 1]⊥ ⋎ □^[n + 1]⊥) 🡒 (□^[n + 1]⊥ ⋎ □^[n + 1]⊥)) 🡒
        (∼□^[n + 1]⊥) 🡒 (∼□^[n + 2]⊥) : Formula α) ∈ LogicGL := iff_forces.mpr (by grind);
      exact Logic.sumQuasiNormal.mdp
        (Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_axiomD) ih;

section

/-- The intrinsic definition of `LogicD` that avoids `subst`. -/
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

/-- Induction principle for `LogicD` avoiding `subst`. -/
protected lemma substlessInduction
  {motive : (A : Formula α) → A ∈ LogicD → Prop}
  (provable_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (axiomP : motive (∼□⊥) provable_axiomP)
  (axiomD : ∀ {A B}, motive (□(□A ⋎ □B) 🡒 (□A ⋎ □B)) provable_axiomD)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicD} → {hA : A ∈ LogicD} →
  motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumQuasiNormal.mdp hAB hA))
  : ∀ {A}, (h : A ∈ LogicD) → motive A h := by
  intro A h;
  induction LogicD.substless.eq_LogicD.symm ▸ h with
  | provable_GL hg => exact provable_GL hg;
  | axiomP => exact axiomP;
  | axiomD A B => exact axiomD;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := LogicD.substless.toLogicD hAB) (hA := LogicD.substless.toLogicD hA)
      (ihAB _) (ihA _);

end


variable {A B C : Formula α}

lemma provable_of_provable_GL_imp [DecidableEq α]
  (hAB : (A 🡒 B) ∈ LogicGL) (hA : A ∈ LogicD) :
  B ∈ LogicD :=
  Logic.sumQuasiNormal.mdp (provable_of_provable_GL hAB) hA

lemma provable_imp_trans [DecidableEq α]
  (h₁ : (A 🡒 B) ∈ LogicD) (h₂ : (B 🡒 C) ∈ LogicD) :
  (A 🡒 C) ∈ LogicD := by
  have h_taut : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C)) ∈ LogicGL := by
    apply provable_of_valid;
    grind;
  exact Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mdp (provable_of_provable_GL h_taut) h₁) h₂;

open Model.World in
/-- The `n`-ary form of axiom `D`, `□(□A₁ ⋎ ⋯ ⋎ □Aₙ) 🡒 (□A₁ ⋎ ⋯ ⋎ □Aₙ)`. -/
lemma provable_fdisj_axiomD [DecidableEq α] {Γ : FormulaFinset α} :
  (□(⋁(□Γ)) 🡒 ⋁(□Γ)) ∈ LogicD := by
  induction Γ using Finset.induction_on with
  | empty => simpa using provable_axiomP;
  | insert A Γ hAΓ ih =>
    have h_box_step : (□(⋁(□(insert A Γ))) 🡒 □(□A ⋎ □(⋁(□Γ)))) ∈ LogicGL := by
      apply provable_of_valid;
      intro κ _ M _ x hx y Rxy;
      have hy := hx y Rxy;
      obtain ⟨C, hC, hyC⟩ := forces_fdisj.mp hy;
      simp only [FormulaFinset.box, Finset.mem_image, Finset.mem_insert] at hC;
      obtain ⟨B, (rfl | hBΓ), rfl⟩ := hC;
      . apply forces_or.mpr;
        left;
        exact hyC;
      . apply forces_or.mpr;
        right;
        intro z Ryz;
        apply forces_fdisj.mpr;
        refine ⟨□B, Finset.mem_image_of_mem _ hBΓ, ?_⟩;
        intro w Rzw;
        exact hyC w (IsTrans.trans _ _ _ Ryz Rzw);
    have h_taut_or_mono : ((□(⋁(□Γ)) 🡒 ⋁(□Γ)) 🡒
      ((□A ⋎ □(⋁(□Γ))) 🡒 (□A ⋎ ⋁(□Γ)))) ∈ LogicGL := by
      apply provable_of_valid;
      grind;
    have h_or_insert : ((□A ⋎ ⋁(□Γ)) 🡒 ⋁(□(insert A Γ))) ∈ LogicGL := by
      apply provable_of_valid;
      intro κ _ M _ x hx;
      rcases forces_or.mp hx with (h | h);
      . exact forces_fdisj.mpr ⟨□A, by simp, h⟩;
      . obtain ⟨C, hC, hxC⟩ := forces_fdisj.mp h;
        exact forces_fdisj.mpr ⟨C, Finset.image_subset_image (Finset.subset_insert _ _) hC, hxC⟩;
    have t₁ : (□(⋁(□(insert A Γ))) 🡒 □(□A ⋎ □(⋁(□Γ)))) ∈ LogicD :=
      provable_of_provable_GL h_box_step;
    have t₂ : (□(□A ⋎ □(⋁(□Γ))) 🡒 (□A ⋎ □(⋁(□Γ)))) ∈ LogicD := provable_axiomD;
    have t₃ : ((□A ⋎ □(⋁(□Γ))) 🡒 (□A ⋎ ⋁(□Γ))) ∈ LogicD :=
      provable_of_provable_GL_imp h_taut_or_mono ih;
    have t₄ : ((□A ⋎ ⋁(□Γ)) 🡒 ⋁(□(insert A Γ))) ∈ LogicD :=
      provable_of_provable_GL h_or_insert;
    exact provable_imp_trans (provable_imp_trans (provable_imp_trans t₁ t₂) t₃) t₄;

lemma provable_TBB [DecidableEq α] {n : ℕ} : (TBB n : Formula α) ∈ LogicD := by
  match n with
  | 0 => exact provable_axiomP;
  | n + 1 => simpa [TBB, Formula.boxItr] using provable_fdisj_axiomD (Γ := ({□^[n]⊥} : FormulaFinset α));

lemma provable_lconj_of_forall_provable {Γ : FormulaList α} (h : ∀ B ∈ Γ, B ∈ LogicD) :
  (⋀Γ) ∈ LogicD := by
  match Γ with
  | [] => exact provable_of_provable_GL ProvableHilbert.top;
  | [B] => exact h B (by simp);
  | B :: C :: Γ =>
    exact Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mdp (provable_of_provable_GL ProvableHilbert.andIntro) (h B (by simp)))
      (provable_lconj_of_forall_provable (Γ := C :: Γ) (by grind));

lemma provable_fconj_of_forall_provable {Γ : FormulaFinset α} (h : ∀ B ∈ Γ, B ∈ LogicD) :
  (⋀Γ) ∈ LogicD :=
  provable_lconj_of_forall_provable (by simpa)

lemma provable_fconj_subfmlsD [DecidableEq α] : (⋀A.subfmlsD) ∈ LogicD := by
  apply provable_fconj_of_forall_provable;
  intro B hB;
  obtain ⟨Γ, _, rfl⟩ : ∃ Γ ⊆ A.subfmls.prebox, (□(⋁(□Γ)) 🡒 ⋁(□Γ)) = B := by
    simpa [Formula.subfmlsD] using hB;
  exact provable_fdisj_axiomD;


open Model Model.World

lemma forces_pseudoTail_root_of_provable [DecidableEq α] (h : A ∈ LogicD) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] →
    ∀ (r : M.World) (o : α → Prop), (M.toPseudoTail r o).root.1 ⊩[_] A := by
  intro κ _ M _ r o;
  induction h using LogicD.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.soundness h ((M.toPseudoTail r o).toModel) _;
  | axiomP =>
    intro hbox;
    exact hbox (toPseudoTail.embed (Classical.arbitrary κ)) toPseudoTail.rel_chainPoint_embed;
  | @axiomD B C =>
    intro hbox;
    by_contra hC;
    obtain ⟨h₁, h₂⟩ := not_forces_or.mp hC;
    obtain ⟨x, Rrx, hx⟩ := not_forces_box.mp h₁;
    obtain ⟨y, Rry, hy⟩ := not_forces_box.mp h₂;
    have key : ∀ w : (M.toPseudoTail r o).World,
        (M.toPseudoTail r o).Rel (toPseudoTail.chainPoint ⊤) w →
        ∃ k : ℕ, ∀ n : ℕ, k < n →
          (M.toPseudoTail r o).Rel (toPseudoTail.chainPoint ((n : ℕ) : ℕ∞)) w := by
      rintro (w | i) hw;
      . exact ⟨0, fun n _ => toPseudoTail.rel_chainPoint_embed⟩;
      . have hi : i < (⊤ : ℕ∞) := toPseudoTail.rel_chainPoint_chainPoint.mp hw;
        refine ⟨i.toNat, ?_⟩;
        intro n hn;
        apply toPseudoTail.rel_chainPoint_chainPoint.mpr;
        calc i = ((i.toNat : ℕ) : ℕ∞) := (ENat.natCast_toNat hi.ne).symm
          _ < ((n : ℕ) : ℕ∞) := by exact_mod_cast hn;
    obtain ⟨k₁, hk₁⟩ := key x Rrx;
    obtain ⟨k₂, hk₂⟩ := key y Rry;
    have hz : toPseudoTail.chainPoint ((k₁ + k₂ + 1 : ℕ) : ℕ∞) ⊩[_] (□B ⋎ □C) :=
      hbox _ (toPseudoTail.rel_chainPoint_chainPoint.mpr (ENat.natCast_lt_top _));
    rcases forces_or.mp hz with (hzB | hzC);
    . exact hx (hzB x (hk₁ _ (by omega)));
    . exact hy (hzC y (hk₂ _ (by omega)));
  | mdp ihAB ihA => exact ihAB ihA;

open Classical in
lemma root_forces_subfmlsD_imp [DecidableEq α]
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ r o,
    (M.toPseudoTail r o).root.1 ⊩[_] A) :
  ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
    M.root.1 ⊩[_] (⋀A.subfmlsD 🡒 A) := by
  intro κ _ M _;
  by_contra hC;
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hC;
  replace h₁ : ∀ Γ ⊆ A.subfmls.prebox, M.root.1 ⊩[M.toModel] (□(⋁(□Γ)) 🡒 ⋁(□Γ)) := by
    intro Γ hΓ;
    exact forces_fconj.mp h₁ _
      (by simp only [Formula.subfmlsD, Finset.mem_image, Finset.mem_powerset]; exact ⟨Γ, hΓ, rfl⟩);
  let Δ := (A.subfmls.prebox).filter (fun B => ¬(M.root.1 ⊩[M.toModel] □B));
  obtain ⟨x, Rrx, hx⟩ : ∃ x, M.root.1 ≺ x ∧ ∀ B ∈ Δ, ¬(x ⊩[M.toModel] □B) := by
    have hΔ₁ : M.root.1 ⊮[M.toModel] ⋁(□Δ) := by grind;
    have hΔ₂ : M.root.1 ⊮[M.toModel] □(⋁(□Δ)) := by grind;
    grind;
  let N := M.toModel.toRootedModel x;
  have hS : ∀ B ∈ A.subfmls.prebox, N.root.1 ⊩[N.toModel] (□B 🡒 B) := by
    intro B hB;
    apply Model.toRootedModel.forces_same_at_root.mpr;
    grind;
  have hA := h N.toModel N.root.1 (M.Val M.root.1);
  have transport : ∀ B, B ∈ A.subfmls →
      (toPseudoTail.chainPoint ⊤ ⊩[(N.toModel.toPseudoTail N.root.1 (M.Val M.root.1)).toModel] B
        ↔ M.root.1 ⊩[M.toModel] B) := by
    intro B;
    induction B with
    | box B ihB =>
      intro hB;
      constructor;
      . intro hω;
        have hxB : x ⊩[M.toModel] □B := by
          have hl : toPseudoTail.embed N.root.1
              ⊩[(N.toModel.toPseudoTail N.root.1 (M.Val M.root.1)).toModel] (□B) :=
            Model.toPseudoTail.forces_box_of_root_forces_box hω;
          exact Model.toRootedModel.forces_same_at_root.mp (Model.toPseudoTail.forces_inl.mp hl);
        by_contra hroot;
        exact hx B (Finset.mem_filter.mpr ⟨by grind, hroot⟩) hxB;
      . intro hroot;
        rintro (w | j) Rωw;
        . apply Model.toPseudoTail.forces_inl.mpr;
          apply Model.toRootedModel.forces_same_at_cone_point.mpr;
          rcases w.2 with (hwx | hxw);
          . rw [hwx]; exact hroot _ Rrx;
          . exact hroot _ (IsTrans.trans _ _ _ Rrx hxw);
        . have hj : j < (⊤ : ℕ∞) := Model.toPseudoTail.rel_chainPoint_chainPoint.mp Rωw;
          obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hj.ne;
          apply (Model.toPseudoTail.root_forces_iff_forces_nat (M := N) (o := M.Val M.root.1)
            (S := A.subfmls) (fun B hB => Formula.subfmls_trans hB) hS B
            (Formula.subfmls_trans hB (by grind)) m).mp;
          apply Model.toRootedModel.forces_same_at_root.mpr;
          exact hroot x Rrx;
    | _ => grind;
  exact h₂ ((transport A (by grind)).mp hA);


/--
  Characterizations of `LogicD`: in terms of `GL`, of the two-layered sequent calculus for
  `D`, and of forcing in pseudo-tail models of finite `GL` models.

  - [KKIM25, Proposition 3.6]
-/
theorem provability_TFAE [DecidableEq α] :
  [
    A ∈ LogicD,
    ⊢ᵍ[D] (∅ ⟹[2] {A}),
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ r o,
      (M.toPseudoTail r o).root.1 ⊩[_] A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩[_] (⋀A.subfmlsD 🡒 A),
    ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] → ∀ r o,
      (M.toPseudoTail r o).root.1 ⊩[_] A,
    (⋀A.subfmlsD 🡒 A) ∈ LogicGL,
  ].TFAE := by
  tfae_have 1 → 3 := forces_pseudoTail_root_of_provable;
  tfae_have 3 → 4 := root_forces_subfmlsD_imp;
  tfae_have 4 ↔ 6 := iff_forces_root.symm;
  tfae_have 6 → 1 := fun h => Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_fconj_subfmlsD;
  tfae_have 3 → 2 := fun h =>
    ProvableGentzen.Kripke.completeness_finite
      (fun {κ} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL] tail o =>
        Model.World.forces_singleton_sequent.mpr (h M tail o));
  tfae_have 2 → 3 := by
    intro h κ _ M _ r o;
    exact Model.World.forces_singleton_sequent.mp
      (GentzenWithCutProvable.soundness (GentzenWithCutProvable.of_without_cut h) M _);
  tfae_have 3 → 5 := by
    intro h n _ M _ r o;
    exact Model.forces_toPseudoTail_reindex_root_iff.mp <|
      h (M.reindex (Equiv.ulift (α := Fin n)).symm) ((Equiv.ulift (α := Fin n)).symm r) o;
  tfae_have 5 → 3 := by
    intro h κ _ M _ r o;
    exact Model.forces_toPseudoTail_reindex_root_iff.mp <|
      h M.card M.toConcrete (Finite.equivFin κ r) o;
  tfae_finish;

theorem iff_provable_D_provable_GL [DecidableEq α] :
  A ∈ LogicD ↔ (⋀A.subfmlsD 🡒 A) ∈ LogicGL := provability_TFAE.out 1 6

theorem iff_provable_box_provable_GL [DecidableEq α] : □A ∈ LogicD ↔ A ∈ LogicGL := by
  constructor;
  . intro h;
    apply provable_of_valid;
    intro κ _ M _ x;
    have h₁ := forces_pseudoTail_root_of_provable h M x (fun _ => True);
    exact toPseudoTail.forces_inl.mp (h₁ (toPseudoTail.embed x) toPseudoTail.rel_chainPoint_embed);
  . intro h;
    exact provable_of_provable_GL (ProvableHilbert.nec h);

theorem iff_forces_pseudoTail_root [DecidableEq α] :
  A ∈ LogicD ↔ ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ r o,
    (M.toPseudoTail r o).root.1 ⊩[_] A :=
  provability_TFAE.out 1 3

theorem iff_forces_pseudoTail_root_concrete [DecidableEq α] :
  A ∈ LogicD ↔ ∀ (n : ℕ) [NeZero n] (M : Model (Fin n) α), [M.IsFiniteGL] → ∀ r o,
    (M.toPseudoTail r o).root.1 ⊩[_] A :=
  provability_TFAE.out 1 5

theorem not_mem_of_concrete_pseudoTail_root_not_forces [DecidableEq α] {n : ℕ} [NeZero n]
  (M : Model (Fin n) α) [M.IsFiniteGL] (r : M.World) (o : α → Prop)
  (h : (M.toPseudoTail r o).root.1 ⊮[_] A) : A ∉ LogicD :=
  fun hA => h <| iff_forces_pseudoTail_root_concrete.mp hA n M r o

theorem exists_not_forces_toPseudoTail_of_not_mem [DecidableEq α] {A : Formula α}
  (hA : A ∉ LogicD) :
  ∃ (κ : Type u) (_ : Nonempty κ) (M : Model κ α), M.IsFiniteGL ∧ ∃ (r : M.World)
    (o : α → Prop), ¬(M.toPseudoTail r o).root.1 ⊩[_] A := by
  have h := iff_forces_pseudoTail_root.not.mp hA;
  push Not at h;
  exact h;

lemma not_provable_map_some [DecidableEq α] {A : Formula α}
  (h : A ∉ LogicD) : (A.map some) ∉ LogicD := by
  intro hc;
  apply h;
  apply iff_forces_pseudoTail_root.mpr;
  intro κ _ M _ r o;
  have hall := iff_forces_pseudoTail_root.mp hc (κ := κ);
  have hfrc := hall (M.optionExtend) r
    (fun a => match a with | some a => o a | none => False);
  have e : ((M.optionExtend).toPseudoTail r
        (fun a => match a with | some a => o a | none => False)).root.1
        ⊩[((M.optionExtend).toPseudoTail r
          (fun a => match a with | some a => o a | none => False)).toModel] (A.map some)
      ↔ (M.toPseudoTail r o).root.1 ⊩[(M.toPseudoTail r o).toModel] A := by
    apply Iff.trans Model.forces_map;
    apply Model.forces_congr (by funext x y; rcases x with x | i <;> rcases y with y | j <;> rfl);
    intro x a;
    rcases x with x | i;
    . exact Iff.rfl;
    . by_cases hi : i = (⊤ : ℕ∞) <;> simp [hi];
  exact e.mp hfrc;

/-- The ProvabilityLogic analogue of `FFL.Modal.D.unprovable_T`. -/
lemma not_provable_axiomT [DecidableEq α] {a : α} : (□(#a) 🡒 #a : Formula α) ∉ LogicD :=
  -- The countermodel is the pseudo-tail of the one-point `GL` model, with `a` false only
  -- at the root.
  not_mem_of_concrete_pseudoTail_root_not_forces (Model.pointModel (fun _ => True)) 0
    (fun _ => False) (by grind)

end LogicD

lemma LogicD_ssubset_LogicS [Inhabited α] [DecidableEq α] : (LogicD : Logic α) ⊂ LogicS := by
  constructor;
  . exact LogicS_subset_LogicD;
  . apply Set.not_subset_iff_exists_mem_notMem.mpr;
    use (□#default 🡒 #default);
    constructor;
    . exact LogicS.provable_axiomT;
    . exact LogicD.not_provable_axiomT;

lemma LogicGL.not_provable_axiomP [DecidableEq α] : (∼□⊥ : Formula α) ∉ LogicGL :=
  -- The unique world of the one-point model has no successor, so `□⊥` holds vacuously.
  not_mem_of_concrete_not_forces (Model.pointModel (α := α) (fun _ => True)) (x := 0)
    (by grind)

lemma LogicGL_ssubset_LogicD [DecidableEq α] : (LogicGL : Logic α) ⊂ LogicD := by
  constructor;
  . exact fun A h => LogicD.provable_of_provable_GL h;
  . apply Set.not_subset_iff_exists_mem_notMem.mpr;
    use (∼□⊥);
    constructor;
    . exact LogicD.provable_axiomP;
    . exact not_provable_axiomP;

end
