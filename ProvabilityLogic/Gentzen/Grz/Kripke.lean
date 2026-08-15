module

public import ProvabilityLogic.Gentzen.Grz.Basic
public import ProvabilityLogic.Gentzen.GL.Kripke

@[expose]
public section

variable {κ : Type u} [Nonempty κ]
         {α : Type v} [DecidableEq α]
         {M : Model κ α}
         {A B : Formula α} {Γ Γ' Δ Δ' : FormulaFinset α}

namespace Model

lemma validate_gentzen_boxT [Std.Refl M.Rel] (h : M ⊧ (insert B Γ ⟹ Δ)) :
  M ⊧ (insert (□B) Γ ⟹ Δ) := by
  intro x hx;
  apply h x;
  intro C hC;
  rcases Finset.mem_insert.mp hC with rfl | hC;
  · exact Model.World.forces_box.mp (hx (□C) (Finset.mem_insert_self _ _)) x (Std.Refl.refl x);
  · exact hx C (Finset.mem_insert_of_mem hC);

section

variable {x : M.World}

omit [DecidableEq α] in
private lemma not_forces_box_of_not_forces [Std.Refl M.Rel] (h : x ⊮ A) : x ⊮ □A :=
  fun hx => h (hx x (Std.Refl.refl x))

end

open World in
lemma validate_gentzen_boxGrz [M.IsGrz] (h : M ⊧ (insert (□(A 🡒 □A)) Γ.box ⟹ {A})) :
  M ⊧ (Γ.box ⟹ {□A}) := by
  intro x;
  apply forces_ctx_singleton_sequent.mpr;
  intro hΓ;
  apply forces_box.mpr;
  intro y Rxy;
  by_contra hy;
  have h₁ : ∀ z, x ≺ z → ∀ C ∈ Γ.box, z ⊩ C := by
    intro z Rxz C hC;
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC;
    intro w Rzw;
    exact hΓ (□D) (Finset.mem_image_of_mem _ hD) w (_root_.trans Rxz Rzw);
  obtain ⟨v, ⟨Rxv, hv⟩, hmax⟩ :=
    WeaklyConverseWellFounded.has_max (r := M.Rel) {z | x ≺ z ∧ z ⊮ □A}
      ⟨y, Rxy, not_forces_box_of_not_forces hy⟩;
  replace hmax : ∀ z, x ≺ z → z ⊮ □A → v ≺ z → v = z := by
    intro z Rxz hz Rvz;
    by_contra hne;
    exact hmax z ⟨Rxz, hz⟩ ⟨Rvz, hne⟩;
  obtain ⟨w, Rvw, hw⟩ := not_forces_box.mp hv;
  obtain rfl : v = w :=
    hmax w (_root_.trans Rxv Rvw) (not_forces_box_of_not_forces hw) Rvw;
  refine hw $ forces_ctx_singleton_sequent.mp (h v) ?_;
  intro C hC;
  rcases Finset.mem_insert.mp hC with rfl | hC;
  · intro u Rvu hu;
    by_contra hnu;
    obtain rfl := hmax u (_root_.trans Rxv Rvu) hnu Rvu;
    exact hw hu;
  · exact h₁ v Rxv C hC;

end Model

namespace LogicGrz

abbrev trivial_Grz_model {α} : Model (Fin 1) α where
  Rel' := λ _ _ => True
  Val' := λ _ _ => False

instance : trivial_Grz_model (α := α) |>.IsFiniteGrz where
  finite   := inferInstance;
  refl     := by tauto;
  trans    := by tauto;
  antisymm := fun a b _ _ => Subsingleton.elim a b;

open LogicGL

noncomputable def _root_.Sequent.subfmlsGrz (S : Sequent α) : FormulaFinset α :=
  S.subfmls
    ∪ (FormulaFinset.prebox S.subfmls |>.image (λ C => C 🡒 □C))
    ∪ (FormulaFinset.prebox S.subfmls |>.image (λ C => □(C 🡒 □C)))

variable {S : Sequent α}

@[grind .]
lemma subfmls_subset_subfmlsGrz : S.subfmls ⊆ S.subfmlsGrz := by
  intro C hC;
  simp [Sequent.subfmlsGrz, hC];

@[grind =>]
lemma imp_mem_subfmlsGrz (h : A 🡒 B ∈ S.subfmlsGrz) : A ∈ S.subfmls ∧ B ∈ S.subfmls := by
  simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image] at h;
  rcases h with (h | ⟨C, hC, heq⟩) | ⟨C, hC, heq⟩;
  · grind;
  · obtain ⟨rfl, rfl⟩ : A = C ∧ B = □C := by grind;
    have hC : □A ∈ S.subfmls := FormulaFinset.iff_mem_prebox_mem.mp hC;
    exact ⟨Sequent.mem_subfmls_subfmls hC Formula.mem_subfmls_box, hC⟩;
  · exact absurd heq (by grind);

@[grind =>]
lemma box_mem_subfmlsGrz (h : □A ∈ S.subfmlsGrz) : A ∈ S.subfmlsGrz := by
  simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image] at h;
  rcases h with (h | ⟨C, _, heq⟩) | ⟨C, hC, heq⟩;
  · exact subfmls_subset_subfmlsGrz (Sequent.mem_subfmls_subfmls h Formula.mem_subfmls_box);
  · exact absurd heq (by grind);
  · obtain rfl : A = C 🡒 □C := by grind;
    simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image];
    exact Or.inl (Or.inr ⟨C, hC, rfl⟩);

@[grind =>]
lemma grzCompanions_mem_subfmlsGrz (h : □A ∈ S.subfmls) :
  (A 🡒 □A) ∈ S.subfmlsGrz ∧ □(A 🡒 □A) ∈ S.subfmlsGrz := by
  have h : A ∈ FormulaFinset.prebox S.subfmls := FormulaFinset.iff_mem_prebox_mem.mpr h;
  constructor;
  · simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image];
    exact Or.inl (Or.inr ⟨A, h, rfl⟩);
  · simp only [Sequent.subfmlsGrz, Finset.mem_union, Finset.mem_image];
    exact Or.inr ⟨A, h, rfl⟩;

/--
  A `LogicGrz.ProofGentzen`-unprovable sequent saturated for `impL`/`impR`, closed under the
  reflexivity rule `boxT` on its antecedent, and bounded by the subformula closure of a base
  sequent `BS`. The bound is deliberately asymmetric: the antecedent may range over the enlarged
  `BS.subfmlsGrz` but the succedent stays within the plain `BS.subfmls`, so that a boxed formula
  `□A` in the succedent is guaranteed to have its Grz companion `A 🡒 □A` inside `BS.subfmlsGrz`.
-/
structure ExpandedSequent (BS : Sequent α) extends Sequent α where
  saturated   : toSequent.Saturated
  boxT_closed : ∀ {A : Formula α}, □A ∈ toSequent.ant → A ∈ toSequent.ant
  ant_subset  : toSequent.ant ⊆ BS.subfmlsGrz
  suc_subset  : toSequent.suc ⊆ BS.subfmls
  unprovable  : ⊬ᵍ[Grz] toSequent

namespace ExpandedSequent

attribute [grind .] ExpandedSequent.saturated ExpandedSequent.boxT_closed
  ExpandedSequent.ant_subset ExpandedSequent.suc_subset ExpandedSequent.unprovable

variable {BS : Sequent α} {S : ExpandedSequent BS} {A : Formula α}

@[grind .]
lemma not_mem_both : ¬(A ∈ S.1.1 ∧ A ∈ S.1.2) := by
  push Not;
  intro h₁ h₂;
  apply S.unprovable;
  exact ProvableGentzen.union' _ h₁ h₂;

@[grind .] lemma not_mem_bot_ant : ⊥ ∉ S.1.1 := by grind;
@[grind =>] lemma of_mem_imp_ant (h : A 🡒 B ∈ S.1.1 := by grind) : A ∈ S.1.2 ∨ B ∈ S.1.1 := S.saturated.impL h
@[grind =>] lemma of_mem_imp_suc (h : A 🡒 B ∈ S.1.2 := by grind) : A ∈ S.1.1 ∧ B ∈ S.1.2 := S.saturated.impR h

open Classical in
/--
  One step of the Lindenbaum-style saturation for `LogicGrz.ProofGentzen`: process the given
  list of formulas, saturating the sequent for `impL`, `impR` and `boxT` while preserving
  `LogicGrz.ProofGentzen`-unprovability.
-/
@[grind]
noncomputable def lindenbaum_indexed (S₀ : Sequent α) (S₀_unprovable : ⊬ᵍ[Grz] S₀) : FormulaList α → { S : Sequent α // ⊬ᵍ[Grz] S }
| [] => ⟨S₀, S₀_unprovable⟩
| (A 🡒 B) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed S₀ S₀_unprovable Γ;
  if h : (A 🡒 B) ∈ S.1 then
    if h : ⊬ᵍ[Grz] ((S.1) ⟹ (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
    else ⟨((insert B S.1) ⟹ S.2), by
      push Not at h;
      contrapose! hS;
      have := ProvableGentzen.impL h hS;
      rwa [(show insert (A 🡒 B) S.1 = S.1 by grind)] at this;
    ⟩
  else if h : (A 🡒 B) ∈ S.2 then ⟨
    ((insert A S.1) ⟹ (insert B S.2)),
    by
      contrapose! hS;
      have := ProvableGentzen.impR hS;
      rwa [(show insert (A 🡒 B) S.2 = S.2 by grind)] at this;
  ⟩
  else ⟨S, hS⟩
| (□A) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed S₀ S₀_unprovable Γ;
  if h : (□A) ∈ S.1 then ⟨
    ((insert A S.1) ⟹ S.2),
    by
      contrapose! hS;
      have := ProvableGentzen.boxT hS;
      rwa [(show insert (□A) S.1 = S.1 by grind)] at this;
  ⟩
  else ⟨S, hS⟩
| _ :: Γ => lindenbaum_indexed S₀ S₀_unprovable Γ

variable {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[Grz] S₀} {Γ : FormulaList α}

/-- Every step of `lindenbaum_indexed` only ever extends `S₀`. -/
lemma subset_lindenbaum_indexed : S₀ ⊆ (lindenbaum_indexed S₀ S₀_unprovable Γ).1 := by
  induction Γ with
  | nil =>
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons A Γ ih =>
    match A with
    | #a | ⊥ => exact ih
    | A 🡒 B =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2.trans (Finset.subset_insert _ _)⟩
      · exact ⟨ih.1, ih.2⟩;
    | □A =>
      dsimp only [lindenbaum_indexed];
      split_ifs;
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2⟩;

variable {BS : Sequent α}

/--
  Two-sided invariant of `lindenbaum_indexed`: if the antecedent of `S₀` stays inside
  `BS.subfmlsGrz` and its succedent inside `BS.subfmls`, so do those of the resulting sequent.
  The bound is asymmetric like `ExpandedSequent` itself; each membership is derived from the
  invariant already established for the shorter list together with the closure lemmas for
  `Sequent.subfmlsGrz`, so no side condition on `Γ` is needed.
-/
lemma bounds_lindenbaum_indexed (S₀_ant : S₀.ant ⊆ BS.subfmlsGrz) (S₀_suc : S₀.suc ⊆ BS.subfmls) :
  (lindenbaum_indexed S₀ S₀_unprovable Γ).1.ant ⊆ BS.subfmlsGrz ∧
  (lindenbaum_indexed S₀ S₀_unprovable Γ).1.suc ⊆ BS.subfmls := by
  induction Γ with
  | nil => exact ⟨S₀_ant, S₀_suc⟩
  | cons C Γ ih =>
    match C with
    | #a | ⊥ => exact ih
    | A 🡒 B =>
      dsimp only [lindenbaum_indexed];
      split_ifs with h1 h2 h3;
      · exact ⟨Finset.insert_subset (subfmls_subset_subfmlsGrz (imp_mem_subfmlsGrz (ih.1 h1)).2) ih.1, ih.2⟩;
      · exact ⟨ih.1, Finset.insert_subset (imp_mem_subfmlsGrz (ih.1 h1)).1 ih.2⟩;
      · exact ⟨
          Finset.insert_subset (subfmls_subset_subfmlsGrz (Sequent.mem_subfmls_subfmls (ih.2 h3) Formula.mem_subfmls_imp_left)) ih.1,
          Finset.insert_subset (Sequent.mem_subfmls_subfmls (ih.2 h3) Formula.mem_subfmls_imp_right) ih.2
        ⟩;
      · exact ih;
    | □A =>
      dsimp only [lindenbaum_indexed];
      split_ifs with h;
      · exact ⟨Finset.insert_subset (box_mem_subfmlsGrz (ih.1 h)) ih.1, ih.2⟩;
      · exact ih;

/--
  `impL`-saturation part of `saturated_lindenbaum_indexed`: the antecedent of the saturated
  sequent is closed under the `impL` rule for implications from `Γ`.
-/
lemma saturated_impL_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  ∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.ant → A ∈ S.1.suc ∨ B ∈ S.1.ant := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil =>
    intro _ A;
    intros;
    simp_all;
  | cons x Γ' ih =>
    intro hΓ;
    rw [List.pairwise_cons] at hΓ;
    obtain ⟨hhead, htail⟩ := hΓ;
    replace ih : ∀ {A B : Formula α}, A 🡒 B ∈ Γ' →
      A 🡒 B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant →
      A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc ∨ B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant := ih htail;
    match x with
    | #a | ⊥ =>
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      refine ih ?_ hx;
      rcases List.mem_cons.mp hmem with h | h;
      · simp at h;
      · exact h;
    | C 🡒 D =>
      have hunp : ⊬ᵍ[Grz] (lindenbaum_indexed S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 h2 h3 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];
    | □C =>
      have hunp : ⊬ᵍ[Grz] (lindenbaum_indexed S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];

/--
  `impR`-saturation part of `saturated_lindenbaum_indexed`: the succedent of the saturated
  sequent is closed under the `impR` rule for implications from `Γ`.
-/
lemma saturated_impR_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  ∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.suc → A ∈ S.1.ant ∧ B ∈ S.1.suc := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil =>
    intro _ A;
    intros;
    simp_all;
  | cons x Γ' ih =>
    intro hΓ;
    rw [List.pairwise_cons] at hΓ;
    obtain ⟨hhead, htail⟩ := hΓ;
    replace ih : ∀ {A B : Formula α}, A 🡒 B ∈ Γ' →
      A 🡒 B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc →
      A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant ∧ B ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.suc := ih htail;
    match x with
    | #a | ⊥ =>
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      refine ih ?_ hx;
      rcases List.mem_cons.mp hmem with h | h;
      · simp at h;
      · exact h;
    | C 🡒 D =>
      have hunp : ⊬ᵍ[Grz] (lindenbaum_indexed S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 h2 h3 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];
    | □C =>
      have hunp : ⊬ᵍ[Grz] (lindenbaum_indexed S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A B hmem hx;
      split_ifs at hx ⊢ with h1 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];

/--
  `boxT`-saturation part of `saturated_lindenbaum_indexed`: the antecedent of the saturated
  sequent is closed under the `boxT` rule for boxed formulas from `Γ`.
-/
lemma saturated_boxT_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  ∀ {A : Formula α}, □A ∈ Γ → □A ∈ S.1.ant → A ∈ S.1.ant := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil =>
    intro _ A;
    intros;
    simp_all;
  | cons x Γ' ih =>
    intro hΓ;
    rw [List.pairwise_cons] at hΓ;
    obtain ⟨hhead, htail⟩ := hΓ;
    replace ih : ∀ {A : Formula α}, □A ∈ Γ' →
      □A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant →
      A ∈ (lindenbaum_indexed S₀ S₀_unprovable Γ').1.ant := ih htail;
    match x with
    | #a | ⊥ =>
      dsimp only [lindenbaum_indexed];
      intro A hmem hx;
      refine ih ?_ hx;
      rcases List.mem_cons.mp hmem with h | h;
      · simp at h;
      · exact h;
    | C 🡒 D =>
      have hunp : ⊬ᵍ[Grz] (lindenbaum_indexed S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A hmem hx;
      split_ifs at hx ⊢ with h1 h2 h3 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];
    | □C =>
      have hunp : ⊬ᵍ[Grz] (lindenbaum_indexed S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed S₀ S₀_unprovable Γ').2;
      dsimp only [lindenbaum_indexed];
      intro A hmem hx;
      split_ifs at hx ⊢ with h1 <;>
        simp_all only [List.mem_cons] <;>
        grind [ProvableGentzen.union'];

/--
  Saturation of the Lindenbaum construction: the resulting sequent is simultaneously
  `impL`-, `impR`- and `boxT`-saturated for the formulas listed in `Γ`.
-/
lemma saturated_lindenbaum_indexed (hΓ : (Γ.map (·.complexity)).SortedLE) :
  let S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.ant → A ∈ S.1.suc ∨ B ∈ S.1.ant) ∧
  (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.suc → A ∈ S.1.ant ∧ B ∈ S.1.suc) ∧
  (∀ {A : Formula α}, □A ∈ Γ → □A ∈ S.1.ant → A ∈ S.1.ant) :=
  ⟨saturated_impL_lindenbaum_indexed hΓ,
   saturated_impR_lindenbaum_indexed hΓ,
   saturated_boxT_lindenbaum_indexed hΓ⟩

/--
  Lindenbaum-style saturation for `LogicGrz.ProofGentzen`: every unprovable sequent bounded by
  the subformula closure of `BS` extends to a saturated, `boxT`-closed, unprovable sequent whose
  bounds against `BS` are still asymmetric. Runs `lindenbaum_indexed` once over
  `BS.subfmlsGrz` sorted by complexity.
-/
noncomputable def lindenbaum {BS : Sequent α} [Fact (⊬ᵍ[Grz] BS)] (S₀ : Sequent α)
  (S₀_unprovable : ⊬ᵍ[Grz] S₀) (S₀_ant : S₀.ant ⊆ BS.subfmlsGrz) (S₀_suc : S₀.suc ⊆ BS.subfmls) :
  ExpandedSequent BS :=
  letI Γ := BS.subfmlsGrz.toList.insertionSort (·.complexity ≤ ·.complexity);
  letI S := lindenbaum_indexed S₀ S₀_unprovable Γ;
  haveI hΓsorted : (Γ.map (·.complexity)).SortedLE := by
    rw [List.map_insertionSort (f := Formula.complexity) (l := BS.subfmlsGrz.toList) (r := λ A B => ((A.complexity) ≤ (B.complexity))) (s := (· ≤ ·)) (by grind)];
    exact List.sortedLE_insertionSort (l := BS.subfmlsGrz.toList.map (·.complexity));
  haveI hbounds : S.1.ant ⊆ BS.subfmlsGrz ∧ S.1.suc ⊆ BS.subfmls := bounds_lindenbaum_indexed S₀_ant S₀_suc;
  {
    toSequent  := S.1,
    unprovable := S.2,
    ant_subset := hbounds.1,
    suc_subset := hbounds.2,
    saturated := {
      impL := by
        intro A B h;
        apply saturated_impL_lindenbaum_indexed hΓsorted ?_ h;
        exact List.mem_insertionSort _ |>.mpr $ Finset.mem_toList.mpr $ hbounds.1 h;
      impR := by
        intro A B h;
        apply saturated_impR_lindenbaum_indexed hΓsorted ?_ h;
        exact List.mem_insertionSort _ |>.mpr $ Finset.mem_toList.mpr $ subfmls_subset_subfmlsGrz (hbounds.2 h);
    },
    boxT_closed := by
      intro A h;
      apply saturated_boxT_lindenbaum_indexed hΓsorted ?_ h;
      exact List.mem_insertionSort _ |>.mpr $ Finset.mem_toList.mpr $ hbounds.1 h;
  }

lemma subset_lindenbaum {BS : Sequent α} [Fact (⊬ᵍ[Grz] BS)] {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ[Grz] S₀}
  {S₀_ant : S₀.ant ⊆ BS.subfmlsGrz} {S₀_suc : S₀.suc ⊆ BS.subfmls} :
  S₀ ⊆ (lindenbaum S₀ S₀_unprovable S₀_ant S₀_suc).1 := subset_lindenbaum_indexed

/-- Two `ExpandedSequent`s agree once their underlying antecedent and succedent agree. -/
lemma ext {S T : ExpandedSequent BS} (ha : S.toSequent.ant = T.toSequent.ant) (hs : S.toSequent.suc = T.toSequent.suc) : S = T := by
  obtain ⟨⟨ΓS, ΔS⟩, _⟩ := S;
  obtain ⟨⟨ΓT, ΔT⟩, _⟩ := T;
  grind;

instance : Finite (ExpandedSequent BS) := by
  apply Finite.of_injective
    (β := {x : Finset (Formula α) // x ∈ BS.subfmlsGrz.powerset} × {x : Finset (Formula α) // x ∈ BS.subfmls.powerset})
    (fun S : ExpandedSequent BS => (⟨S.toSequent.ant, Finset.mem_powerset.mpr S.ant_subset⟩,
               ⟨S.toSequent.suc, Finset.mem_powerset.mpr S.suc_subset⟩))
  intro S T h;
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact ext h.1 h.2

instance [Fact (⊬ᵍ[Grz] BS)] : Nonempty (ExpandedSequent BS) :=
  ⟨lindenbaum BS (Fact.elim inferInstance)
    (Finset.subset_union_left.trans Sequent.subset_self_subfmls |>.trans subfmls_subset_subfmlsGrz)
    (Finset.subset_union_right.trans Sequent.subset_self_subfmls)⟩

end ExpandedSequent


namespace ProvableGentzen.Kripke

variable {BS : Sequent α} [Fact (⊬ᵍ[Grz] BS)]

/--
The canonical finite countermodel of an unprovable `Grz` sequent `BS`: worlds are the expanded
sequents built over `BS`, an atom holds at a world exactly when it sits in its antecedent, and
one world precedes another when its `□`-preimage antecedent is contained in the other's, with
the containment forced into equality once it also holds in the reverse direction. Unlike the
`GL` countermodel this relation is reflexive; the reversed-containment clause is exactly what
forces antisymmetry.
-/
@[grind]
def countermodelOf (BS : Sequent α) [Fact (⊬ᵍ[Grz] BS)] : Model (ExpandedSequent BS) α where
  Val' x a := #a ∈ x.1.1
  Rel' x y := (x.1.1.prebox ⊆ y.1.1.prebox) ∧ ((y.1.1.prebox ⊆ x.1.1.prebox) → x = y)

instance : (countermodelOf BS).IsFiniteGrz where
  finite := inferInstance
  refl := fun x => ⟨Finset.Subset.refl _, fun _ => rfl⟩
  trans := by
    intro x y z hxy hyz;
    refine ⟨hxy.1.trans hyz.1, fun h => ?_⟩;
    obtain rfl : x = y := hxy.2 (hyz.1.trans h);
    exact hyz.2 h;
  antisymm := fun _ _ hxy hyx => hxy.2 hyx.1

variable {x : (countermodelOf BS).World} {A : Formula α}

/--
Truth lemma for the `Grz` countermodel: membership in the antecedent of an expanded sequent
forces the formula, and membership in the succedent refutes it. -/
lemma truthlemma :
  (A ∈ x.1.1 → x ⊩ A) ∧ (A ∈ x.1.2 → ¬x ⊩ A) := by
  induction A generalizing x with
  | atom a =>
    constructor
    · intro h; exact h
    · intro h hf; exact ExpandedSequent.not_mem_both ⟨hf, h⟩
  | bot =>
    constructor
    · intro h; exact absurd h ExpandedSequent.not_mem_bot_ant
    · intro _ hf; exact hf
  | imp A B ihA ihB =>
    constructor
    · intro h hsA
      rcases x.saturated.impL h with hA | hB
      · exact absurd hsA (ihA.2 hA)
      · exact ihB.1 hB
    · intro h hf
      obtain ⟨hA, hB⟩ := x.saturated.impR h
      exact (ihB.2 hB) (hf (ihA.1 hA))
  | box A ih =>
    refine ⟨?_, ?_⟩;
    · intro h y Rxy;
      have hA : A ∈ x.1.1.prebox := FormulaFinset.iff_mem_prebox_mem.mpr h;
      exact ih.1 (y.boxT_closed (FormulaFinset.iff_mem_prebox_mem.mp (Rxy.1 hA)));
    · intro h;
      apply Model.World.not_forces_box.mpr;
      by_cases hAsuc : A ∈ x.1.2;
      · exact ⟨x, ⟨Finset.Subset.refl _, fun _ => rfl⟩, ih.2 hAsuc⟩;
      · let y : ExpandedSequent BS :=
          ExpandedSequent.lindenbaum
            (insert (□(A 🡒 □A)) (x.1.1.prebox.box) ⟹ {A})
            (by
              intro hprov;
              have hb : ⊢ᵍ[Grz] (x.1.1.prebox.box ⟹ {□A}) := ProvableGentzen.boxGrz hprov;
              exact x.unprovable (ProvableGentzen.wk hb
                (show x.1.1.prebox.box ⊆ x.1.1 by grind)
                (show ({□A} : FormulaFinset α) ⊆ x.1.2 by grind));
            )
            (by
              intro C hC;
              simp only [Finset.mem_insert] at hC;
              rcases hC with rfl | hC;
              · exact (grzCompanions_mem_subfmlsGrz (x.suc_subset h)).2;
              · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC;
                exact x.ant_subset (FormulaFinset.iff_mem_prebox_mem.mp hB);
            )
            (by
              intro C hC;
              simp only [Finset.mem_singleton] at hC;
              subst hC;
              exact Sequent.mem_subfmls_subfmls (x.suc_subset h) Formula.mem_subfmls_box;
            );
        refine ⟨y, ⟨?_, ?_⟩, ih.2 (ExpandedSequent.subset_lindenbaum.2 (Finset.mem_singleton_self A))⟩;
        · intro B hB;
          exact FormulaFinset.iff_mem_prebox_mem.mpr $
            ExpandedSequent.subset_lindenbaum.1 (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hB));
        · intro hyx;
          exfalso;
          have h1 : □(A 🡒 □A) ∈ y.1.1 := ExpandedSequent.subset_lindenbaum.1 (Finset.mem_insert_self _ _);
          have h3 : (A 🡒 □A) ∈ x.1.1.prebox := hyx (FormulaFinset.iff_mem_prebox_mem.mpr h1);
          have h5 : (A 🡒 □A) ∈ x.1.1 := x.boxT_closed (FormulaFinset.iff_mem_prebox_mem.mp h3);
          rcases ExpandedSequent.of_mem_imp_ant h5 with h6 | h6;
          · exact hAsuc h6;
          · exact ExpandedSequent.not_mem_both ⟨h6, h⟩;

lemma truthlemma_ant : A ∈ x.1.1 → x ⊩ A := truthlemma.1
lemma truthlemma_suc : A ∈ x.1.2 → ¬x ⊩ A := truthlemma.2

/-- Kripke completeness of the cut-free `LogicGrz.ProofGentzen`: a sequent valid in every
finite `Grz` model is provable. -/
theorem completeness {S : Sequent α} (h : ∀ {κ : Type v}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGrz] → M ⊧ S) : ⊢ᵍ[Grz] S := by
  contrapose! h;
  have : Fact (⊬ᵍ[Grz] S) := ⟨iff_unprovableGentzen_isEmpty_ProofGentzen.mpr h⟩;
  use (ExpandedSequent S), inferInstance, (countermodelOf S);
  constructor;
  . infer_instance;
  . dsimp [Model.ValidateSequent, Model.World.ForcesSequent];
    push Not;
    use (ExpandedSequent.lindenbaum S (Fact.elim inferInstance)
      (Finset.subset_union_left.trans Sequent.subset_self_subfmls |>.trans subfmls_subset_subfmlsGrz)
      (Finset.subset_union_right.trans Sequent.subset_self_subfmls));
    constructor;
    . intro C hC; exact truthlemma_ant $ ExpandedSequent.subset_lindenbaum.1 hC;
    . intro D hD; exact truthlemma_suc $ ExpandedSequent.subset_lindenbaum.2 hD;

open Model in
/-- Kripke soundness of the cut-free `LogicGrz.ProofGentzen`: every provable sequent is valid in
every `Grz` model. -/
theorem soundness {S : Sequent α} (h : ⊢ᵍ[Grz] S) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGrz] → M ⊧ S := by
  intro κ _ M _;
  induction h with
  | axm A => exact validate_gentzen_axm
  | botL => exact validate_gentzen_botL
  | wkL _ _ ih => exact validate_gentzen_wkL ih
  | wkR _ _ ih => exact validate_gentzen_wkR ih
  | impL _ _ ih₁ ih₂ => exact validate_gentzen_impL ih₁ ih₂
  | impR _ ih => exact validate_gentzen_impR ih
  | boxT _ ih => exact Model.validate_gentzen_boxT ih
  | boxGrz _ ih => exact Model.validate_gentzen_boxGrz ih

theorem finite_soundness {S : Sequent α} (h : ⊢ᵍ[Grz] S) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGrz] → M ⊧ S :=
  λ _ _ M [M.IsFiniteGrz] => soundness h M

end Kripke

@[simp, grind .]
theorem not_provable_empty : ⊬ᵍ[Grz] (∅ ⟹ ∅ : Sequent α) := by
  by_contra! h;
  have : (0 : trivial_Grz_model.World) ⊩ (∅ ⟹ ∅) := Kripke.finite_soundness h trivial_Grz_model 0;
  grind;

end ProvableGentzen

end LogicGrz

end
