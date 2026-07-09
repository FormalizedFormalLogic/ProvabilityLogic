module

public import SeqPL.Logic.SumQuasiNormal
public import SeqPL.Logic.S.Basic
public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.PseudoTail
public import SeqPL.Kripke.Rank

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
    · exact Logic.sumQuasiNormal.mem₂ ⟨⊥, rfl⟩;
    · exact Logic.sumQuasiNormal.mem₂ ⟨□A ⋎ □B, rfl⟩;


universe u
variable {α : Type u}

/-- Semantic membership in `GL` via finite model completeness. -/
lemma LogicGL.provable_of_valid [DecidableEq α] {A : Formula α}
    (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGL] → M ⊧ A) :
    A ∈ LogicGL :=
  LogicGL.iff_forces.mpr h


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

section

/-- The intrinsic definition of `LogicD` that avoids `subst` (used for
`LogicD.substlessInduction`). -/
protected inductive substless : Logic α
  | provable_GL {A} : A ∈ LogicGL → LogicD.substless A
  | axiomP : LogicD.substless (∼□⊥)
  | axiomD (A B) : LogicD.substless (□(□A ⋎ □B) 🡒 (□A ⋎ □B))
  | mdp {A B} : LogicD.substless (A 🡒 B) → LogicD.substless A → LogicD.substless B

private lemma substless.eq_LogicD : LogicD.substless (α := α) = LogicD := by
  ext A;
  constructor;
  · intro h;
    induction h with
    | provable_GL h => exact provable_of_provable_GL h;
    | axiomP => exact provable_axiomP;
    | axiomD A B => exact provable_axiomD;
    | mdp _ _ ihAB ihA => exact Logic.sumQuasiNormal.mdp ihAB ihA;
  · intro h;
    induction h with
    | mem₁ h => exact LogicD.substless.provable_GL h;
    | mem₂ h =>
      rcases h with (rfl | ⟨B, C, rfl⟩);
      · exact LogicD.substless.axiomP;
      · exact LogicD.substless.axiomD B C;
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

/-- Induction principle for `LogicD` avoiding `subst`: it suffices to handle the `GL`
fragment, axiom `P`, axiom `D`, and `mdp`. -/
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

/-! ### Semantic lemmas for `GL` (via finite model completeness) -/

open Model.World

private lemma GL_taut_trans [DecidableEq α] :
    ((A 🡒 B) 🡒 (B 🡒 C) 🡒 (A 🡒 C)) ∈ LogicGL := by
  apply LogicGL.provable_of_valid;
  grind;

private lemma GL_taut_or_mono [DecidableEq α] :
    ((A 🡒 B) 🡒 ((C ⋎ A) 🡒 (C ⋎ B))) ∈ LogicGL := by
  apply LogicGL.provable_of_valid;
  grind;

private lemma GL_box_fdisj_step [DecidableEq α] {Γ : FormulaFinset α} :
    (□(⋁(□(insert A Γ))) 🡒 □(□A ⋎ □(⋁(□Γ)))) ∈ LogicGL := by
  apply LogicGL.provable_of_valid;
  intro κ _ M _ x hx y Rxy;
  have hy := hx y Rxy;
  obtain ⟨C, hC, hyC⟩ := forces_fdisj.mp hy;
  simp only [FormulaFinset.box, Finset.mem_image, Finset.mem_insert] at hC;
  obtain ⟨B, (rfl | hBΓ), rfl⟩ := hC;
  · exact forces_or.mpr (Or.inl hyC);
  · apply forces_or.mpr;
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
  · exact forces_fdisj.mpr ⟨□A, by simp, h⟩;
  · obtain ⟨C, hC, hxC⟩ := forces_fdisj.mp h;
    exact forces_fdisj.mpr ⟨C, Finset.image_subset_image (Finset.subset_insert _ _) hC, hxC⟩;

end


lemma provable_of_provable_GL_imp [DecidableEq α]
    (hAB : (A 🡒 B) ∈ LogicGL) (hA : A ∈ LogicD) :
    B ∈ LogicD :=
  Logic.sumQuasiNormal.mdp (provable_of_provable_GL hAB) hA

lemma provable_imp_trans [DecidableEq α]
    (h₁ : (A 🡒 B) ∈ LogicD) (h₂ : (B 🡒 C) ∈ LogicD) :
    (A 🡒 C) ∈ LogicD :=
  Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mdp (provable_of_provable_GL GL_taut_trans) h₁) h₂

/-- The `n`-ary axiom `D`, `□(□A₁ ⋎ ⋯ ⋎ □Aₙ) 🡒 (□A₁ ⋎ ⋯ ⋎ □Aₙ)`, is provable in `LogicD`. -/
lemma provable_fdisj_axiomD [DecidableEq α] {Γ : FormulaFinset α} :
    (□(⋁(□Γ)) 🡒 ⋁(□Γ)) ∈ LogicD := by
  induction Γ using Finset.induction_on with
  | empty => simpa using provable_axiomP;
  | insert A Γ hAΓ ih =>
    have t₁ : (□(⋁(□(insert A Γ))) 🡒 □(□A ⋎ □(⋁(□Γ)))) ∈ LogicD :=
      provable_of_provable_GL GL_box_fdisj_step;
    have t₂ : (□(□A ⋎ □(⋁(□Γ))) 🡒 (□A ⋎ □(⋁(□Γ)))) ∈ LogicD := provable_axiomD;
    have t₃ : ((□A ⋎ □(⋁(□Γ))) 🡒 (□A ⋎ ⋁(□Γ))) ∈ LogicD :=
      provable_of_provable_GL_imp GL_taut_or_mono ih;
    have t₄ : ((□A ⋎ ⋁(□Γ)) 🡒 ⋁(□(insert A Γ))) ∈ LogicD :=
      provable_of_provable_GL GL_or_fdisj_insert;
    exact provable_imp_trans (provable_imp_trans (provable_imp_trans t₁ t₂) t₃) t₄;

/-- `D` proves every `TBB n` (`□^[n+1]⊥ 🡒 □^[n]⊥`); in particular `D` has trace `ω`. -/
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

/-- Every theorem of `LogicD` is forced at the root (ω) of the pseudo-tail model of any
finite GL model. -/
lemma forces_pseudoTail_root_of_provable [DecidableEq α] (h : A ∈ LogicD) :
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] →
      ∀ (r : M.World) (o : α → Prop), (M.toPseudoTail r o).root.1 ⊩ A := by
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
      · exact ⟨0, fun n _ => toPseudoTail.rel_chainPoint_embed⟩;
      · have hi : i < (⊤ : ℕ∞) := toPseudoTail.rel_chainPoint_chainPoint.mp hw;
        refine ⟨i.toNat, fun n hn => toPseudoTail.rel_chainPoint_chainPoint.mpr ?_⟩;
        calc i = ((i.toNat : ℕ) : ℕ∞) := (ENat.coe_toNat hi.ne).symm
          _ < ((n : ℕ) : ℕ∞) := by exact_mod_cast hn;
    obtain ⟨k₁, hk₁⟩ := key x Rrx;
    obtain ⟨k₂, hk₂⟩ := key y Rry;
    have hz : Forces (M := (M.toPseudoTail r o).toModel)
        (toPseudoTail.chainPoint ((k₁ + k₂ + 1 : ℕ) : ℕ∞)) (□B ⋎ □C) :=
      hbox _ (toPseudoTail.rel_chainPoint_chainPoint.mpr (ENat.coe_lt_top _));
    rcases forces_or.mp hz with (hzB | hzC);
    · exact hx (hzB x (hk₁ _ (by omega)));
    · exact hy (hzC y (hk₂ _ (by omega)));
  | mdp ihAB ihA => exact ihAB ihA;

open Classical in
/-- From validity at the root of pseudo-tail models, `⋀A.subfmlsD 🡒 A` is forced at the
root of every finite rooted GL model. -/
lemma root_forces_subfmlsD_imp [DecidableEq α]
    (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ r o,
      (M.toPseudoTail r o).root.1 ⊩ A) :
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩ (⋀A.subfmlsD 🡒 A) := by
  intro κ _ M _;
  by_contra hC;
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hC;
  replace h₁ : ∀ Γ ⊆ A.subfmls.prebox, M.root.1 ⊩ (□(⋁(□Γ)) 🡒 ⋁(□Γ)) := by
    intro Γ hΓ;
    exact forces_fconj.mp h₁ _
      (by simp only [Formula.subfmlsD, Finset.mem_image, Finset.mem_powerset]; exact ⟨Γ, hΓ, rfl⟩);
  -- Collect the subformulas `B` whose box `□B` is refuted at the root.
  let Δ := (A.subfmls.prebox).filter (fun (B : Formula α) => ¬(M.root.1 ⊩ □B));
  obtain ⟨x, Rrx, hx⟩ : ∃ x, M.root.1 ≺ x ∧ ∀ B ∈ Δ, ¬(x ⊩ □B) := by
    have hΔ₁ : M.root.1 ⊮ ⋁(□Δ) := by grind;
    have hΔ₂ : M.root.1 ⊮ □(⋁(□Δ)) := by grind;
    grind;
  -- The submodel point-generated by `x`.
  let N := M.toModel.toRootedModel x;
  have hS : ∀ B ∈ A.subfmls.prebox, N.root.1 ⊩ (□B 🡒 B) := by
    intro B hB;
    apply Model.toRootedModel.forces_same_at_root.mpr;
    grind;
  have hA := h N.toModel N.root.1 (M.Val M.root.1);
  -- For each subformula of `A`, forcing agrees between the pseudo-tail root (ω) and the
  -- root of the original model `M`.
  have transport : ∀ B, B ∈ A.subfmls →
      (Forces (M := (N.toModel.toPseudoTail N.root.1 (M.Val M.root.1)).toModel)
        (toPseudoTail.chainPoint ⊤) B ↔ M.root.1 ⊩ B) := by
    intro B;
    induction B with
    | box B ihB =>
      intro hB;
      constructor;
      · intro hω;
        have hxB : x ⊩ □B := by
          have hl : Forces (M := (N.toModel.toPseudoTail N.root.1 (M.Val M.root.1)).toModel)
              (toPseudoTail.embed N.root.1) (□B) :=
            Model.toPseudoTail.forces_box_of_root_forces_box hω;
          exact Model.toRootedModel.forces_same_at_root.mp (Model.toPseudoTail.forces_inl.mp hl);
        by_contra hroot;
        exact hx B (Finset.mem_filter.mpr ⟨by grind, hroot⟩) hxB;
      · intro hroot;
        rintro (w | j) Rωw;
        · apply Model.toPseudoTail.forces_inl.mpr;
          apply Model.toRootedModel.forces_same_at_cone_point.mpr;
          rcases w.2 with (hwx | hxw);
          · rw [hwx]; exact hroot _ Rrx;
          · exact hroot _ (IsTrans.trans _ _ _ Rrx hxw);
        · have hj : j < (⊤ : ℕ∞) := Model.toPseudoTail.rel_chainPoint_chainPoint.mp Rωw;
          obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hj.ne;
          apply (Model.toPseudoTail.root_forces_iff_forces_nat (M := N) (o := M.Val M.root.1)
            (S := A.subfmls) (fun B hB => Formula.subfmls_trans hB) hS B
            (Formula.subfmls_trans hB (by grind)) m).mp;
          apply Model.toRootedModel.forces_same_at_root.mpr;
          exact hroot x Rrx;
    | _ => grind;
  exact h₂ ((transport A (by grind)).mp hA);


/-- Characterization of `Logic D` in terms of `GL` (semantic proof via pseudo-tail models). -/
theorem provability_TFAE [DecidableEq α] : [
    A ∈ LogicD,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : Model κ α), [M.IsFiniteGL] → ∀ r o,
      (M.toPseudoTail r o).root.1 ⊩ A,
    ∀ {κ : Type u}, [Nonempty κ] → ∀ (M : RootedModel κ α), [M.IsFiniteGL] →
      M.root.1 ⊩ (⋀A.subfmlsD 🡒 A),
    (⋀A.subfmlsD 🡒 A) ∈ LogicGL
  ].TFAE := by
  tfae_have 1 → 2 := forces_pseudoTail_root_of_provable;
  tfae_have 2 → 3 := root_forces_subfmlsD_imp;
  tfae_have 3 ↔ 4 := LogicGL.iff_forces_root.symm;
  tfae_have 4 → 1 := fun h => Logic.sumQuasiNormal.mdp (provable_of_provable_GL h) provable_fconj_subfmlsD;
  tfae_finish;

theorem iff_provable_D_provable_GL [DecidableEq α] :
    A ∈ LogicD ↔ (⋀A.subfmlsD 🡒 A) ∈ LogicGL := provability_TFAE.out 0 3

/--
  The existential, contrapositive form of `provability_TFAE`'s clause 2: a formula not
  provable in `D` has a pseudo-tail model refuting it at the root.
-/
theorem exists_not_forces_toPseudoTail_of_not_mem [DecidableEq α] {A : Formula α}
    (hA : A ∉ LogicD) :
    ∃ (κ : Type u) (_ : Nonempty κ) (M : Model κ α), M.IsFiniteGL ∧ ∃ (r : M.World)
      (o : α → Prop), ¬(M.toPseudoTail r o).root.1 ⊩ A := by
  have h := provability_TFAE (A := A) |>.out 0 1 |>.not.mp hA;
  push Not at h;
  exact h;

/--
  Non-provability in `D` transfers along the fresh-atom embedding, semantically via
  pseudo-tail models.
-/
lemma not_provable_map_some [DecidableEq α] {A : Formula α}
    (h : A ∉ LogicD) : (A.map some) ∉ LogicD := by
  intro hc;
  apply h;
  apply LogicD.provability_TFAE.out 1 0 |>.mp;
  intro κ _ M _ r o;
  have hall := LogicD.provability_TFAE (A := A.map some) |>.out 0 1 |>.mp hc;
  have hfrc := hall (κ := κ) (M.optionExtend) r
    (fun a => match a with | some a => o a | none => False);
  have e : ((M.optionExtend).toPseudoTail r
        (fun a => match a with | some a => o a | none => False)).root.1 ⊩ (A.map some)
      ↔ (M.toPseudoTail r o).root.1 ⊩ A := by
    apply Iff.trans Model.forces_map;
    apply Model.forces_congr (by funext x y; rcases x with x | i <;> rcases y with y | j <;> rfl);
    intro x a;
    rcases x with x | i;
    · exact Iff.rfl;
    · by_cases hi : i = (⊤ : ℕ∞) <;> simp [hi];
  exact e.mp hfrc;

/-- The reflection axiom `T` (`□a 🡒 a` for an atom `a`) is not a theorem of `D`.
The SeqPL analogue of `LO.Modal.D.unprovable_T`. -/
lemma not_provable_axiomT [DecidableEq α] {a : α} : (□(#a) 🡒 #a : Formula α) ∉ LogicD := by
  -- Counterexample: the pseudo-tail model of the one-point GL model with empty relation
  -- and everywhere-true valuation, with the root (ω) valuation making `a` false. Every
  -- world accessible from the root forces `a`, so the root forces `□a`, yet the root
  -- itself refutes `a`.
  apply LogicD.provability_TFAE.out 0 1 |>.not.mpr;
  push Not;
  let M : Model PUnit.{u + 1} α := ⟨fun _ _ => False, fun _ _ => True⟩;
  haveI : M.IsFiniteGL :=
    { trans := fun _ _ _ hf _ => hf.elim
      irrefl := fun _ hf => hf
      finite := inferInstance };
  use PUnit.{u + 1}, inferInstance, M;
  constructor;
  · exact {
      trans := fun _ _ _ hf _ => hf.elim
      irrefl := fun _ hf => hf
      finite := inferInstance
    };
  · use PUnit.unit, fun _ => False;
    grind;

end LogicD

/-- `D` is a proper sublogic of `S`: it is contained in `S` (`LogicS_subset_LogicD`)
but does not prove the reflection axiom `T`, which `S` does. -/
lemma LogicD_ssubset_LogicS [Inhabited α] [DecidableEq α] : (LogicD : Logic α) ⊂ LogicS := by
  constructor;
  · exact LogicS_subset_LogicD;
  · apply Set.not_subset_iff_exists_mem_notMem.mpr;
    use (□#default 🡒 #default);
    constructor;
    · exact LogicS.provable_axiomT;
    · exact LogicD.not_provable_axiomT;

end
