module

public import ProvabilityLogic.Gentzen.GLPoint3.Basic
public import ProvabilityLogic.Gentzen.Kripke
public import ProvabilityLogic.Kripke.ULift

@[expose]
public section

/-!
Kripke semantics for `LogicGLPoint3`: soundness of `boxGLPoint3` (`Model.validate_gentzen_boxGLPoint3`)
and Gentzen completeness (`ProvableGentzen.Kripke.completeness`), obtained by building a finite
rooted countermodel from a `GLPoint3.Chain` of `LogicGLPoint3` expanded sequents.

The overall structure mirrors the `GL` development in `ProvabilityLogic.Gentzen.Kripke`:
* `GLPoint3.ExpandedSequent`/`GLPoint3.ExpandedSequent.lindenbaum` saturate an unprovable sequent,
  exactly as `ProvabilityLogic.Gentzen.ExpandedSequent` does for `GL`.
* `GLPoint3.exists_unprovable_split` is the step lemma dual to `Model.exists_linear_witness`: it
  produces the nonempty split `S` witnessing the failure of one `boxGLPoint3` premise.
* `GLPoint3.Chain` records a finite chain of expanded sequents built by repeatedly saturating
  along such splits (`GLPoint3.exists_chain`), replacing the single fresh world used by the `GL`
  countermodel: `boxGL` only ever needs one witness, `boxGLPoint3` needs a whole chain because of
  linearity.
* `GLPoint3.Chain.chainModel` turns a chain into a genuinely linear finite `LogicGLPoint3` model, and
  `GLPoint3.Chain.truthLemma` is the truth lemma for it.
* `ProvableGentzen.Kripke.completeness` assembles all of the above into Gentzen completeness.
-/

variable {κ : Type u} [Nonempty κ]
         {α : Type v} [DecidableEq α]
         {M : Model κ α}

namespace Model

variable {x : M.World} {D : Formula α}

/-- On a linear (`LogicGLPoint3`) frame, if `x` refutes `□A` for every `A ∈ Δ`, some successor `w`
of `x` refutes exactly a nonempty `S ⊆ Δ`, while forcing `□A` for every `A ∈ S` and refuting
`□A` for every `A ∈ Δ \ S`. This is the witness driving the soundness of `boxGLPoint3`: at `w`
the premise sequent for `S` is falsified. -/
lemma exists_linear_witness [M.IsGLPoint3] :
  ∀ {Δ : FormulaFinset α}, Δ.Nonempty → (∀ A ∈ Δ, x ⊮ □A) →
  ∃ w, x ≺ w ∧ ∃ S ⊆ Δ, S.Nonempty ∧ (∀ A ∈ S, w ⊮ A ∧ w ⊩ □A) ∧ (∀ A ∈ Δ \ S, w ⊮ □A) := by
  intro Δ;
  induction Δ using Finset.strongInductionOn with
  | _ Δ ih =>
  intro hΔne hx;
  obtain ⟨D, hD⟩ := hΔne;
  -- The successor of `x` refuting `D` deepest along `≺` also forces `□D`.
  have terminalBoxRefuter (D : Formula α) (hxD : x ⊮ □D) :
    ∃ z, x ≺ z ∧ z ⊮ D ∧ z ⊩ □D := by
    obtain ⟨z₀, hxz₀, hz₀⟩ := Model.World.not_forces_box.mp hxD;
    obtain ⟨z, ⟨hxz, hzD⟩, hzterm⟩ := M.terminalOf {z | x ≺ z ∧ z ⊮ D} ⟨z₀, hxz₀, hz₀⟩;
    refine ⟨z, hxz, hzD, fun z' hzz' => ?_⟩;
    by_contra hz'D;
    exact hzterm z' ⟨_root_.trans hxz hzz', hz'D⟩ hzz';
  by_cases hΔ' : (Δ.erase D).Nonempty;
  · obtain ⟨w', hxw', S', hS'sub, hS'ne, hS', hDS'⟩ :=
      ih (Δ.erase D) (Finset.erase_ssubset hD) hΔ' (fun A hA => hx A (Finset.mem_of_mem_erase hA));
    by_cases hD1 : w' ⊮ □D;
    · -- `D` joins the already-refuted complement, `S'` is unchanged.
      refine ⟨w', hxw', S', hS'sub.trans (Finset.erase_subset _ _), hS'ne, hS', fun A hA => ?_⟩;
      rcases Finset.mem_sdiff.mp hA with ⟨hAΔ, hAS'⟩;
      by_cases hAD : A = D;
      · subst hAD; exact hD1;
      · exact hDS' A (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hAD, hAΔ⟩, hAS'⟩);
    · push Not at hD1;
      by_cases hD2 : w' ⊮ D;
      · -- `w'` also refutes `D`, so `D` joins `S'`.
        refine ⟨w', hxw', insert D S',
          Finset.insert_subset_iff.mpr ⟨hD, hS'sub.trans (Finset.erase_subset _ _)⟩,
          ⟨D, Finset.mem_insert_self _ _⟩, fun A hA => ?_, fun A hA => ?_⟩;
        · rcases Finset.mem_insert.mp hA with rfl | hA;
          · exact ⟨hD2, hD1⟩;
          · exact hS' A hA;
        · apply hDS' A;
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or] at hA ⊢;
          tauto;
      · -- `w'` forces `D`: descend past `w'` to a deeper world refuting `D` (and everything else).
        push Not at hD2;
        obtain ⟨z, hxz, hzD, hzBoxD⟩ := terminalBoxRefuter D (hx D hD);
        have hzw' : z ≺ w' := by
          rcases Model.linear hxw' hxz with h1 | h2 | h3;
          · exact absurd (hD1 z h1) hzD;
          · rw [h2] at hD2; exact absurd hD2 hzD;
          · exact h3;
        refine ⟨z, hxz, {D}, Finset.singleton_subset_iff.mpr hD, ⟨D, Finset.mem_singleton_self _⟩,
          fun A hA => by rw [Finset.mem_singleton] at hA; subst hA; exact ⟨hzD, hzBoxD⟩, ?_⟩;
        rw [Finset.sdiff_singleton_eq_erase];
        intro A hA;
        by_cases hAS' : A ∈ S';
        · exact fun hzA => (hS' A hAS').1 (hzA w' hzw');
        · obtain ⟨t, hw't, htA⟩ := Model.World.not_forces_box.mp (hDS' A (Finset.mem_sdiff.mpr ⟨hA, hAS'⟩));
          exact fun hzA => htA (hzA t (_root_.trans hzw' hw't));
  · -- Base case: `Δ = {D}`.
    have hΔeq : Δ = {D} := by
      rw [Finset.not_nonempty_iff_eq_empty] at hΔ';
      ext A;
      simp only [Finset.mem_singleton];
      constructor;
      · intro hA;
        by_contra hAD;
        exact absurd (Finset.mem_erase.mpr ⟨hAD, hA⟩) (hΔ' ▸ Finset.notMem_empty A);
      · rintro rfl; exact hD;
    subst hΔeq;
    obtain ⟨z, hxz, hzD, hzBoxD⟩ := terminalBoxRefuter D (hx D (Finset.mem_singleton_self _));
    exact ⟨z, hxz, {D}, subset_refl _, ⟨D, Finset.mem_singleton_self _⟩,
      fun A hA => by rw [Finset.mem_singleton] at hA; subst hA; exact ⟨hzD, hzBoxD⟩,
      fun A hA => by simp at hA⟩;

variable {Γ Δ : FormulaFinset α} {A : Formula α}

open Model.World in
/-- Soundness of `boxGLPoint3`: on a linear (`LogicGLPoint3`) model, if every premise sequent
`□Γ, Γ, □S ⟹ S, □(Δ \ S)` (`S ⊆ Δ` nonempty) is valid, so is the conclusion `□Γ ⟹ □Δ`. -/
lemma validate_gentzen_boxGLPoint3 [M.IsGLPoint3] (hΔ : Δ.Nonempty)
  (h : ∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty → M ⊧ ((Γ.box ∪ Γ ∪ S.box) ⟹ (S ∪ (Δ \ S).box))) :
  M ⊧ (Γ.box ⟹ Δ.box) := by
  intro x hxante;
  by_contra hcon;
  push Not at hcon;
  have hx : ∀ A ∈ Δ, x ⊮ □A := fun A hA => hcon (□A) (Finset.mem_image_of_mem _ hA);
  obtain ⟨w, hxw, S, hSsub, hSne, hSforces, hcompl⟩ := exists_linear_witness hΔ hx;
  have hwante : ∀ C ∈ Γ.box ∪ Γ ∪ S.box, w ⊩ C := by
    intro C hC;
    rcases Finset.mem_union.mp hC with hC | hCS;
    rcases Finset.mem_union.mp hC with hCΓbox | hCΓ;
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hCΓbox;
      exact fun y hwy => hxante (□B) (Finset.mem_image_of_mem _ hB) y (_root_.trans hxw hwy);
    · exact hxante (□C) (Finset.mem_image_of_mem _ hCΓ) w hxw;
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hCS;
      exact (hSforces B hB).2;
  obtain ⟨D, hD, hwD⟩ := h S hSsub hSne w hwante;
  rcases Finset.mem_union.mp hD with hDS | hDbox;
  · exact (hSforces D hDS).1 hwD;
  · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hDbox;
    exact hcompl B hB hwD;

end Model

namespace GLPoint3

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : Sequent α} :
    (⊬ᵍ³ S) ↔ (IsEmpty (⊢ᵍ³! S)) := by simp [ProvableGentzen]

/-- A `LogicGLPoint3`-unprovable, saturated, `BS.subfmls`-bounded sequent. This is the `LogicGLPoint3` analogue of
`ProvabilityLogic.Gentzen.ExpandedSequent`, built from `⊢ᵍ³` instead of `⊢ᵍ`. `Sequent.Saturated` itself is
shared with the `GL` development. -/
structure ExpandedSequent (BS : Sequent α) extends Sequent α where
  saturated      : toSequent.Saturated
  subset_subfmls : toSequent.1 ∪ toSequent.2 ⊆ BS.subfmls
  unprovable     : ⊬ᵍ³ toSequent

namespace ExpandedSequent

attribute [grind .] ExpandedSequent.saturated ExpandedSequent.subset_subfmls ExpandedSequent.unprovable

def widen {BS₀ BS₁ : Sequent α} (S : ExpandedSequent BS₀) (hBS : BS₀ ⊆ BS₁) : ExpandedSequent BS₁ where
  toSequent      := S.toSequent
  saturated      := S.saturated
  unprovable     := S.unprovable
  subset_subfmls := by
    trans BS₀.subfmls
    · exact S.subset_subfmls
    · intro A
      simp [Sequent.subfmls, Finset.mem_union, FormulaFinset.subfmls]
      rintro (⟨B, hB₁, hB₂⟩ | ⟨B, hB₁, hB₂⟩)
      · left
        use B
        constructor
        · exact hBS.1 hB₁
        · assumption
      · right
        use B
        constructor
        · exact hBS.2 hB₁
        · assumption

variable {BS : Sequent α} {S : ExpandedSequent BS} {A : Formula α}

@[grind .]
lemma not_mem_both : ¬(A ∈ S.1.1 ∧ A ∈ S.1.2) := by
  push Not
  intro h₁ h₂
  apply S.unprovable
  exact ProvableGentzen.union' _ h₁ h₂

@[grind .] lemma not_mem_bot_ant : ⊥ ∉ S.1.1 := by grind
@[grind =>] lemma of_mem_imp_ant (h : A 🡒 B ∈ S.1.1 := by grind) : A ∈ S.1.2 ∨ B ∈ S.1.1 := S.saturated.impL h
@[grind =>] lemma of_mem_imp_suc (h : A 🡒 B ∈ S.1.2 := by grind) : A ∈ S.1.1 ∧ B ∈ S.1.2 := S.saturated.impR h

section

variable {BS : Sequent α}

open Classical in
/-- `LogicGLPoint3` analogue of `ProvabilityLogic.Gentzen.ExpandedSequent.lindenbaum_indexed`, expanding `S₀` one
formula at a time (following the list `Γ`) while keeping it `⊢ᵍ³`-unprovable. -/
@[grind]
noncomputable def lindenbaum_indexed (BS : Sequent α) (BS_unprovable : ⊬ᵍ³ BS)
    (S₀ : Sequent α) (S₀_unprovable : ⊬ᵍ³ S₀) : FormulaList α → { S : Sequent α // ⊬ᵍ³ S }
| [] => ⟨S₀, S₀_unprovable⟩
| (A 🡒 B) :: Γ =>
  let ⟨S, hS⟩ := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ
  if h : (A 🡒 B) ∈ S.1 then
    if h : ⊬ᵍ³ ((S.1) ⟹ (insert A S.2)) then ⟨(S.1) ⟹ (insert A S.2), h⟩
    else ⟨((insert B S.1) ⟹ S.2), by
      push Not at h
      contrapose! hS
      have := ProvableGentzen.impL h hS
      rwa [(show insert (A 🡒 B) S.1 = S.1 by grind)] at this
    ⟩
  else if h : (A 🡒 B) ∈ S.2 then ⟨
    ((insert A S.1) ⟹ (insert B S.2)),
    by
      contrapose! hS
      have := ProvableGentzen.impR hS
      rwa [(show insert (A 🡒 B) S.2 = S.2 by grind)] at this
  ⟩
  else ⟨S, hS⟩
| _ :: Γ => lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ

lemma subset_lindenbaum_indexed {BS_unprovable : ⊬ᵍ³ BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ³ S₀}
    {Γ : FormulaList α} :
    S₀ ⊆ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1 := by
  induction Γ with
  | nil =>
    exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | cons A Γ ih =>
    match A with
    | #a | □A | ⊥ => exact ih
    | A 🡒 B =>
      dsimp only [lindenbaum_indexed]
      split_ifs
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2⟩
      · exact ⟨ih.1, ih.2.trans (Finset.subset_insert _ _)⟩
      · exact ⟨ih.1.trans (Finset.subset_insert _ _), ih.2.trans (Finset.subset_insert _ _)⟩
      · exact ⟨ih.1, ih.2⟩

lemma subfmls_lindenbaum_indexed
    {BS_unprovable : ⊬ᵍ³ BS}
    {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ³ S₀} (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls)
    {Γ : FormulaList α} (hΓ : ∀ C ∈ Γ, C ∈ BS.subfmls) :
    (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1 ∪
      (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2 ⊆ BS.subfmls := by
  induction Γ with
  | nil => exact S₀sub
  | cons A Γ ih =>
    replace ih := ih (by grind)
    match A with
    | #a | □A | ⊥ => exact ih
    | (A 🡒 B) =>
      dsimp only [lindenbaum_indexed]
      have : (A 🡒 B) ∈ BS.subfmls := hΓ _ (by simp)
      have : A ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind
      have : B ∈ BS.subfmls := Sequent.mem_subfmls_subfmls (B := A 🡒 B) ‹_› $ by grind
      split_ifs
      all_goals
      . intro
        grind

lemma saturated_lindenbaum_indexed
    {BS_unprovable : ⊬ᵍ³ BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ³ S₀}
    {Γ : FormulaList α} (hΓ : (Γ.map (·.complexity)).SortedLE) :
    let S := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ
    (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.1 → A ∈ S.1.2 ∨ B ∈ S.1.1) ∧
    (∀ {A B : Formula α}, A 🡒 B ∈ Γ → A 🡒 B ∈ S.1.2 → A ∈ S.1.1 ∧ B ∈ S.1.2) := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hΓ
  revert hΓ
  induction Γ with
  | nil => intro _; constructor <;> intro A B hmem _ <;> simp at hmem
  | cons x Γ' ih =>
    intro hΓ
    rw [List.pairwise_cons] at hΓ
    obtain ⟨hhead, htail⟩ := hΓ
    obtain ⟨ihL, ihR⟩ := ih htail
    match x with
    | #a | □C | ⊥ =>
      constructor
      · intro A B hmem hx
        refine ihL ?_ hx
        rcases List.mem_cons.mp hmem with h | h
        · simp at h
        · exact h
      · intro A B hmem hx
        refine ihR ?_ hx
        rcases List.mem_cons.mp hmem with h | h
        · simp at h
        · exact h
    | C 🡒 D =>
      have hunp : ⊬ᵍ³ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ').1 :=
        (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ').2
      dsimp only [lindenbaum_indexed]
      split_ifs with h1 h2 h3 <;>
        refine ⟨?_, ?_⟩ <;>
        intro A B hmem hx <;>
        simp only [List.mem_cons] at hmem <;>
        grind [ProvableGentzen.union']

lemma lindenbaum_indexed_saturated_impL_of_sorted_complexity
    {BS_unprovable : ⊬ᵍ³ BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ³ S₀}
    {Γ : FormulaList α} (hΓ : (Γ.map (·.complexity)).SortedLE)
    (h₁ : A 🡒 B ∈ Γ) (h₂ : A 🡒 B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1) :
    A ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2 ∨
      B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1 :=
  (saturated_lindenbaum_indexed hΓ).1 h₁ h₂

lemma lindenbaum_indexed_saturated_impL
    {BS_unprovable : ⊬ᵍ³ BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ³ S₀}
    {Γ : FormulaList α} (h : A 🡒 B ∈ Γ) :
    letI S := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable
      (Γ.insertionSort (·.complexity ≤ ·.complexity))
    (A 🡒 B ∈ S.1.1) → A ∈ S.1.2 ∨ B ∈ S.1.1 := by
  apply lindenbaum_indexed_saturated_impL_of_sorted_complexity
  · rw [List.map_insertionSort (f := Formula.complexity) (l := Γ)
      (r := λ A B => ((A.complexity) ≤ (B.complexity))) (s := (· ≤ ·)) (by grind)]
    exact List.sortedLE_insertionSort (l := Γ.map (·.complexity))
  · apply List.mem_insertionSort _ |>.mpr h

lemma lindenbaum_indexed_saturated_impR_of_sorted_complexity
    {BS_unprovable : ⊬ᵍ³ BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ³ S₀}
    {Γ : FormulaList α} (hΓ : (Γ.map (·.complexity)).SortedLE)
    (h₁ : A 🡒 B ∈ Γ) (h₂ : A 🡒 B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2) :
    A ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.1 ∧
      B ∈ (lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable Γ).1.2 :=
  (saturated_lindenbaum_indexed hΓ).2 h₁ h₂

lemma lindenbaum_indexed_saturated_impR
    {BS_unprovable : ⊬ᵍ³ BS} {S₀ : Sequent α} {S₀_unprovable : ⊬ᵍ³ S₀}
    {Γ : FormulaList α} (h : A 🡒 B ∈ Γ) :
    letI S := lindenbaum_indexed BS BS_unprovable S₀ S₀_unprovable
      (Γ.insertionSort (·.complexity ≤ ·.complexity))
    (A 🡒 B ∈ S.1.2) → A ∈ S.1.1 ∧ B ∈ S.1.2 := by
  apply lindenbaum_indexed_saturated_impR_of_sorted_complexity
  · rw [List.map_insertionSort (f := Formula.complexity) (l := Γ)
      (r := λ A B => ((A.complexity) ≤ (B.complexity))) (s := (· ≤ ·)) (by grind)]
    exact List.sortedLE_insertionSort (l := Γ.map (·.complexity))
  · apply List.mem_insertionSort _ |>.mpr h

/-- `LogicGLPoint3` analogue of `ProvabilityLogic.Gentzen.ExpandedSequent.lindenbaum`: saturate `S₀` into a full
`ExpandedSequent BS`, listing `BS.subfmls` in increasing complexity order. -/
noncomputable def lindenbaum
    {BS : Sequent α} [BS_unprovable : Fact (⊬ᵍ³ BS)] (S₀ : Sequent α) (S₀_unprovable : ⊬ᵍ³ S₀)
    (S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls) : ExpandedSequent BS :=
  letI S := lindenbaum_indexed BS (Fact.elim inferInstance) S₀ S₀_unprovable $
    BS.subfmls.toList.insertionSort (·.complexity ≤ ·.complexity)
  haveI : ∀ C ∈ BS.subfmls.toList.insertionSort (fun A B => A.complexity ≤ B.complexity),
      C ∈ BS.subfmls := by
    intro _ hB
    exact Finset.mem_toList.mp $ List.mem_insertionSort _ |>.mp hB
  {
    toSequent := S.1,
    unprovable := S.2,
    subset_subfmls := subfmls_lindenbaum_indexed ‹_› ‹_›
    saturated := {
      impL := by
        intro A B h
        apply lindenbaum_indexed_saturated_impL ?_ h
        exact Finset.mem_toList.mpr $ subfmls_lindenbaum_indexed ‹_› ‹_› $ Finset.mem_union.mpr $ Or.inl h
      impR := by
        intro A B h
        apply lindenbaum_indexed_saturated_impR ?_ h
        exact Finset.mem_toList.mpr $ subfmls_lindenbaum_indexed ‹_› ‹_› $ Finset.mem_union.mpr $ Or.inr h
    }
  }

lemma subset_lindenbaum {BS : Sequent α} [BS_unprovable : Fact (⊬ᵍ³ BS)] {S₀ : Sequent α}
    {S₀_unprovable : ⊬ᵍ³ S₀} {S₀sub : S₀.1 ∪ S₀.2 ⊆ BS.subfmls} :
    S₀ ⊆ (lindenbaum S₀ S₀_unprovable S₀sub).1 := subset_lindenbaum_indexed

end

-- `Subsingleton S.Saturated` is already provided globally by `ProvabilityLogic.Gentzen.Kripke` (the `GL`
-- development), since `Sequent.Saturated` itself is shared between `GL` and `GL.3`.

lemma ext {S T : ExpandedSequent BS} (ha : S.toSequent.ant = T.toSequent.ant)
    (hs : S.toSequent.suc = T.toSequent.suc) : S = T := by
  obtain ⟨⟨ΓS, ΔS⟩, _⟩ := S
  obtain ⟨⟨ΓT, ΔT⟩, _⟩ := T
  grind

instance [Fact (⊬ᵍ³ BS)] : Nonempty (ExpandedSequent BS) :=
  ⟨lindenbaum BS (Fact.elim inferInstance) (by grind)⟩

end ExpandedSequent

/-! ### Chains of `LogicGLPoint3` expanded sequents

This file fixes the *interface* only: the data structure `GLPoint3.Chain` recording a finite
chain `x₀, …, x_n : ExpandedSequent BS` together with the witnesses `S₀, …, S_{n-1}` and the
invariants (inv0)–(inv4) from the completeness plan (Step D). No existence proof is given here;
that is `GLPoint3.exists_chain`, proved below. Downstream lemmas (propagation lemmas, the chain
model, the truth lemma) are meant to consume only the fields of `Chain` and the two projections
`ExpandedSequent.Γ`/`ExpandedSequent.Θ` below. -/

namespace ExpandedSequent

variable {BS : Sequent α}

/-- The "front boxed antecedent" of an expanded sequent `x`: the set of `A` with `□A ∈ x.ant`. -/
noncomputable def Γ (x : ExpandedSequent BS) : FormulaFinset α := x.toSequent.ant.prebox

/-- The "front boxed succedent" of an expanded sequent `x`: the set of `A` with `□A ∈ x.suc`. -/
noncomputable def Θ (x : ExpandedSequent BS) : FormulaFinset α := x.toSequent.suc.prebox

end ExpandedSequent

/-- A finite chain of `LogicGLPoint3` expanded sequents witnessing the unprovability of `S₀` relative to
`BS`, as constructed in the `LogicGLPoint3` completeness plan.

The chain has `n + 1` worlds `seq 0, …, seq n`, connected by `n` steps. Step `i : Fin n` moves
from `seq i.castSucc` to `seq i.succ` using the nonempty split `S i ⊆ (seq i.castSucc).Θ` supplied
by `GLPoint3.exists_unprovable_split`. The chain terminates when `(seq (Fin.last n)).Θ = ∅`
(inv4), which forces all boxed succedent formulas to eventually be discharged along the chain
(this is exhibited by the propagation lemmas of `GLPoint3.Chain`, not here).

Only the data and the invariants are recorded; existence of such a chain (for suitable `BS`,
`S₀`) is the content of `GLPoint3.exists_chain`, proved separately from this interface. -/
structure Chain (BS : Sequent α) (S₀ : Sequent α) where
  /-- The length of the chain: there are `n + 1` worlds and `n` steps. -/
  n : ℕ
  /-- The worlds of the chain, `seq 0, …, seq n`. -/
  seq : Fin (n + 1) → ExpandedSequent BS
  /-- The nonempty split chosen at each step `i`, out of `(seq i.castSucc).Θ`. -/
  split : Fin n → FormulaFinset α
  /-- (inv0) The seed sequent `S₀` is included in the first world of the chain. -/
  subset_head : S₀ ⊆ (seq 0).toSequent
  /-- (inv1) The front boxed antecedent `Γᵢ`, its unboxing, and the boxed split `Sᵢ.box` all carry
  over into the antecedent of the next world. -/
  subset_ant_succ : ∀ i : Fin n,
    (seq i.castSucc).Γ.box ∪ (seq i.castSucc).Γ ∪ (split i).box ⊆ (seq i.succ).toSequent.ant
  /-- (inv2) The split `Sᵢ` itself, together with the boxed remainder `(Θᵢ \ Sᵢ).box`, carries
  over into the succedent of the next world. -/
  subset_suc_succ : ∀ i : Fin n,
    split i ⊆ (seq i.succ).toSequent.suc ∧
      ((seq i.castSucc).Θ \ split i).box ⊆ (seq i.succ).toSequent.suc
  /-- (inv3) The split `Sᵢ` is a nonempty subset of `Θᵢ := (seq i.castSucc).Θ`. -/
  subset_split : ∀ i : Fin n, split i ⊆ (seq i.castSucc).Θ ∧ (split i).Nonempty
  /-- (inv4) The chain terminates: the last world has no front boxed succedent formulas left. -/
  eq_last_Θ : (seq (Fin.last n)).Θ = ∅

variable {Γ Δ : FormulaFinset α}

/-- `Γ.prebox.box ⊆ Γ`: unboxing a `prebox` recovers a subset of the original finset. -/
private lemma prebox_box_subset (Γ : FormulaFinset α) : Γ.prebox.box ⊆ Γ := by
  intro A hA;
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA;
  exact FormulaFinset.iff_mem_prebox_mem.mp hB;

/-- The step lemma dual to `Model.exists_linear_witness`: if a boxed sequent `Γ ⟹ Δ` (in
their `prebox` form) is unprovable and `Δ.prebox` is nonempty, then some nonempty
`S ⊆ Δ.prebox` makes the corresponding `boxGLPoint3` premise unprovable. -/
theorem exists_unprovable_split (hΔ : Δ.prebox.Nonempty) (hunprov : ⊬ᵍ³ (Γ ⟹ Δ)) :
    ∃ S ⊆ Δ.prebox, S.Nonempty ∧
      ⊬ᵍ³ ((Γ.prebox.box ∪ Γ.prebox ∪ S.box) ⟹ (S ∪ (Δ.prebox \ S).box)) := by
  by_contra h;
  push Not at h;
  exact hunprov
    (ProvableGentzen.wk (ProvableGentzen.boxGLPoint3 hΔ h)
      (prebox_box_subset Γ) (prebox_box_subset Δ));

namespace ExpandedSequent

variable {BS : Sequent α}

/-! ### Basic subformula-closure facts about `Γ` and `Θ` -/

/-- `x.Γ` is bounded by `BS.subfmls`: if `□A ∈ x.ant`, then `A` is a subformula of `□A ∈ BS.subfmls`. -/
lemma Γ_subset_subfmls (x : ExpandedSequent BS) : x.Γ ⊆ BS.subfmls := by
  intro A hA
  have hbox : □A ∈ x.toSequent.ant := FormulaFinset.iff_mem_prebox_mem.mp hA
  have hbox_sub : □A ∈ BS.subfmls := x.subset_subfmls (Finset.mem_union_left _ hbox)
  exact Sequent.mem_subfmls_subfmls hbox_sub Formula.mem_subfmls_box

/-- `x.Θ` is bounded by `BS.subfmls`, dually to `Γ_subset_subfmls`. -/
lemma Θ_subset_subfmls (x : ExpandedSequent BS) : x.Θ ⊆ BS.subfmls := by
  intro A hA
  have hbox : □A ∈ x.toSequent.suc := FormulaFinset.iff_mem_prebox_mem.mp hA
  have hbox_sub : □A ∈ BS.subfmls := x.subset_subfmls (Finset.mem_union_right _ hbox)
  exact Sequent.mem_subfmls_subfmls hbox_sub Formula.mem_subfmls_box

/-- Reboxing `x.Γ` lands back inside `x.ant`. -/
lemma Γ_box_subset_ant (x : ExpandedSequent BS) : x.Γ.box ⊆ x.toSequent.ant := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  exact FormulaFinset.iff_mem_prebox_mem.mp hA

/-- Reboxing `x.Θ` lands back inside `x.suc`, dually to `Γ_box_subset_ant`. -/
lemma Θ_box_subset_suc (x : ExpandedSequent BS) : x.Θ.box ⊆ x.toSequent.suc := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  exact FormulaFinset.iff_mem_prebox_mem.mp hA

/-- The `x.ant`/`x.suc` inclusions coming from `x.subset_subfmls`. -/
lemma ant_subset_subfmls (x : ExpandedSequent BS) : x.toSequent.ant ⊆ BS.subfmls :=
  fun _ hA => x.subset_subfmls (Finset.mem_union_left _ hA)

lemma suc_subset_subfmls (x : ExpandedSequent BS) : x.toSequent.suc ⊆ BS.subfmls :=
  fun _ hA => x.subset_subfmls (Finset.mem_union_right _ hA)

/-- The key termination-measure lemma: a split `S ⊆ x.Θ` never meets `x.Γ`. Otherwise some `□A`
would sit in both `x.ant` and `x.suc`, contradicting `not_mem_both`. -/
lemma inter_split_Γ_eq_empty {x : ExpandedSequent BS} {S : FormulaFinset α} (hS : S ⊆ x.Θ) :
    S ∩ x.Γ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro A hA
  obtain ⟨hAS, hAΓ⟩ := Finset.mem_inter.mp hA
  have h1 : □A ∈ x.toSequent.suc := FormulaFinset.iff_mem_prebox_mem.mp (hS hAS)
  have h2 : □A ∈ x.toSequent.ant := FormulaFinset.iff_mem_prebox_mem.mp hAΓ
  exact ExpandedSequent.not_mem_both ⟨h2, h1⟩

end ExpandedSequent

/-- Auxiliary form of `exists_chain`: given any starting world `x` (not necessarily saturating
`S₀`), build a chain of `ExpandedSequent BS` starting at `x` and terminating once the front boxed
succedent becomes empty. Proved by strong induction on the termination measure
`(BS.subfmls \ x.Γ).card`, which strictly decreases at every step since the chosen split `S` is
disjoint from `x.Γ` but ends up inside the next world's `Γ`. -/
theorem exists_chain_from_aux {BS : Sequent α} (hBS : ⊬ᵍ³ BS) :
    ∀ m : ℕ, ∀ x : ExpandedSequent BS, (BS.subfmls \ x.Γ).card ≤ m →
      ∃ (n : ℕ) (seq : Fin (n + 1) → ExpandedSequent BS) (split : Fin n → FormulaFinset α),
        seq 0 = x ∧
        (∀ i : Fin n,
          (seq i.castSucc).Γ.box ∪ (seq i.castSucc).Γ ∪ (split i).box ⊆
            (seq i.succ).toSequent.ant) ∧
        (∀ i : Fin n, split i ⊆ (seq i.succ).toSequent.suc ∧
          ((seq i.castSucc).Θ \ split i).box ⊆ (seq i.succ).toSequent.suc) ∧
        (∀ i : Fin n, split i ⊆ (seq i.castSucc).Θ ∧ (split i).Nonempty) ∧
        (seq (Fin.last n)).Θ = ∅ := by
  haveI : Fact (⊬ᵍ³ BS) := Fact.mk hBS
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hx
    by_cases hΘ : x.Θ = ∅
    · exact ⟨0, fun _ => x, Fin.elim0, rfl, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        hΘ⟩
    · have hΘne : x.Θ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hΘ
      obtain ⟨S, hSsub, hSne, hunprov⟩ := exists_unprovable_split hΘne x.unprovable
      set prem : Sequent α := (x.Γ.box ∪ x.Γ ∪ S.box) ⟹ (S ∪ (x.Θ \ S).box) with hprem_def
      have hprem_unprov : ⊬ᵍ³ prem := hunprov
      have hant_sub := x.ant_subset_subfmls
      have hsuc_sub := x.suc_subset_subfmls
      have h1 : x.Γ.box ⊆ BS.subfmls := x.Γ_box_subset_ant.trans hant_sub
      have h2 : x.Γ ⊆ BS.subfmls := x.Γ_subset_subfmls
      have h3 : S.box ⊆ BS.subfmls :=
        (Finset.image_subset_image hSsub).trans (x.Θ_box_subset_suc.trans hsuc_sub)
      have h4 : S ⊆ BS.subfmls := hSsub.trans x.Θ_subset_subfmls
      have h5 : (x.Θ \ S).box ⊆ BS.subfmls :=
        (Finset.image_subset_image Finset.sdiff_subset).trans (x.Θ_box_subset_suc.trans hsuc_sub)
      have hprem_sub : prem.ant ∪ prem.suc ⊆ BS.subfmls :=
        Finset.union_subset (Finset.union_subset (Finset.union_subset h1 h2) h3)
          (Finset.union_subset h4 h5)
      set y : ExpandedSequent BS := ExpandedSequent.lindenbaum prem hprem_unprov hprem_sub
        with hy_def
      have hy_sub : prem ⊆ y.toSequent := ExpandedSequent.subset_lindenbaum
      have hS_Γ : S ⊆ y.Γ := by
        intro A hA
        have hbox : □A ∈ S.box := Finset.mem_image_of_mem _ hA
        have hbox_prem : □A ∈ prem.ant := Finset.mem_union_right _ hbox
        exact FormulaFinset.iff_mem_prebox_mem.mpr (hy_sub.ant_subset hbox_prem)
      have hxΓ_Γ : x.Γ ⊆ y.Γ := by
        intro A hA
        have hbox : □A ∈ x.Γ.box := Finset.mem_image_of_mem _ hA
        have hbox_prem : □A ∈ prem.ant := Finset.mem_union_left _ (Finset.mem_union_left _ hbox)
        exact FormulaFinset.iff_mem_prebox_mem.mpr (hy_sub.ant_subset hbox_prem)
      have hdisj : S ∩ x.Γ = ∅ := ExpandedSequent.inter_split_Γ_eq_empty hSsub
      obtain ⟨A, hAS⟩ := hSne
      have hAy : A ∈ y.Γ := hS_Γ hAS
      have hAx : A ∉ x.Γ := by
        intro hc
        have : A ∈ S ∩ x.Γ := Finset.mem_inter.mpr ⟨hAS, hc⟩
        rw [hdisj] at this
        exact absurd this (Finset.notMem_empty A)
      have hssub : x.Γ ⊂ y.Γ := (Finset.ssubset_iff_of_subset hxΓ_Γ).mpr ⟨A, hAy, hAx⟩
      have hxΓ_sub : x.Γ ⊆ BS.subfmls := x.Γ_subset_subfmls
      have hyΓ_sub : y.Γ ⊆ BS.subfmls := y.Γ_subset_subfmls
      have e1 : (BS.subfmls \ x.Γ).card = BS.subfmls.card - x.Γ.card :=
        Finset.card_sdiff_of_subset hxΓ_sub
      have e2 : (BS.subfmls \ y.Γ).card = BS.subfmls.card - y.Γ.card :=
        Finset.card_sdiff_of_subset hyΓ_sub
      have e3 : x.Γ.card < y.Γ.card := Finset.card_lt_card hssub
      have e4 : y.Γ.card ≤ BS.subfmls.card := Finset.card_le_card hyΓ_sub
      have hcard : (BS.subfmls \ y.Γ).card < (BS.subfmls \ x.Γ).card := by omega
      have hcard_lt_m : (BS.subfmls \ y.Γ).card < m := lt_of_lt_of_le hcard hx
      obtain ⟨n', seq', split', hseq0', hant', hsuc', hspl', hlast'⟩ :=
        ih _ hcard_lt_m y (le_refl _)
      refine ⟨n' + 1, Fin.cons x seq', Fin.cons S split', Fin.cons_zero _ _, ?_, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.cases with
        | zero =>
          simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
          rw [hseq0']
          exact hy_sub.ant_subset
        | succ i =>
          simp only [← Fin.succ_castSucc, Fin.cons_succ]
          exact hant' i
      · intro i
        induction i using Fin.cases with
        | zero =>
          simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
          rw [hseq0']
          exact ⟨Finset.subset_union_left.trans hy_sub.suc_subset,
            Finset.subset_union_right.trans hy_sub.suc_subset⟩
        | succ i =>
          simp only [← Fin.succ_castSucc, Fin.cons_succ]
          exact hsuc' i
      · intro i
        induction i using Fin.cases with
        | zero =>
          simp only [Fin.castSucc_zero, Fin.cons_zero]
          exact ⟨hSsub, A, hAS⟩
        | succ i =>
          simp only [← Fin.succ_castSucc, Fin.cons_succ]
          exact hspl' i
      · rw [show Fin.last (n' + 1) = (Fin.last n').succ from (Fin.succ_last n').symm,
          Fin.cons_succ]
        exact hlast'

/-- The main existence theorem: any `S₀` unprovable and bounded by `BS.subfmls` (with `BS` itself
unprovable) sits at the head of a `Chain BS S₀`. -/
theorem exists_chain {BS S₀ : Sequent α} (hBS : ⊬ᵍ³ BS) (hS₀ : ⊬ᵍ³ S₀)
    (hsub : S₀.ant ∪ S₀.suc ⊆ BS.subfmls) :
    Nonempty (Chain BS S₀) := by
  haveI : Fact (⊬ᵍ³ BS) := Fact.mk hBS
  set x₀ : ExpandedSequent BS := ExpandedSequent.lindenbaum S₀ hS₀ hsub with hx₀_def
  obtain ⟨n, seq, split, hseq0, hant, hsuc, hspl, hlast⟩ :=
    exists_chain_from_aux hBS ((BS.subfmls \ x₀.Γ).card) x₀ (le_refl _)
  refine ⟨⟨n, seq, split, ?_, hant, hsuc, hspl, hlast⟩⟩
  rw [hseq0]
  exact ExpandedSequent.subset_lindenbaum

namespace Chain

variable {BS S₀ : Sequent α}

/-- The Kripke model built from a `LogicGLPoint3` chain: the worlds are the chain's indices
`Fin (c.n + 1)`, related by the strict order `<`, and an atom is forced at `i` iff it
belongs to the antecedent of the `i`-th expanded sequent of the chain. -/
def chainModel (c : Chain BS S₀) : Model (Fin (c.n + 1)) α where
  Rel' i j := i < j
  Val' i a := #a ∈ (c.seq i).toSequent.ant

instance (c : Chain BS S₀) : c.chainModel.IsFiniteGLPoint3 where
  finite := inferInstance
  trans := fun _ _ _ => lt_trans
  irrefl := fun _ => lt_irrefl _
  linear := fun {_ y z} _ _ => lt_trichotomy y z

/-- The chain model is rooted at world `0`, the first expanded sequent of the chain. -/
def chainRootedModel (c : Chain BS S₀) : RootedModel (Fin (c.n + 1)) α :=
  ⟨c.chainModel, 0, fun _ hx => Fin.pos_of_ne_zero hx⟩

variable (c : Chain BS S₀)

/-! ### Monotonicity of the front boxed antecedent `Γ` along the chain -/

/-- One-step version: `Γᵢ` is included in the antecedent of the next world `xᵢ₊₁`. -/
private lemma Γ_subset_ant_succ (i : Fin c.n) :
    (c.seq i.castSucc).Γ ⊆ (c.seq i.succ).toSequent.ant := by
  intro A hA;
  exact c.subset_ant_succ i (by simp [ExpandedSequent.Γ] at hA ⊢; grind);

/-- One-step version: `Γᵢ ⊆ Γᵢ₊₁`, i.e. the front boxed antecedent only grows along a step. -/
private lemma Γ_subset_Γ_succ (i : Fin c.n) :
    (c.seq i.castSucc).Γ ⊆ (c.seq i.succ).Γ := by
  intro A hA;
  have hbox : □A ∈ (c.seq i.castSucc).Γ.box := Finset.mem_image_of_mem _ hA;
  have : □A ∈ (c.seq i.succ).toSequent.ant := c.subset_ant_succ i (by simp; grind);
  exact FormulaFinset.iff_mem_prebox_mem.mpr this;

theorem Γ_subset_of_le {i j : Fin (c.n + 1)} (hij : i ≤ j) :
    (c.seq i).Γ ⊆ (c.seq j).Γ := by
  have main : ∀ k, i.val ≤ k → ∀ hk : k < c.n + 1, (c.seq i).Γ ⊆ (c.seq ⟨k, hk⟩).Γ := by
    intro k hle;
    induction k, hle using Nat.le_induction with
    | base => intro _; exact fun A hA => hA;
    | succ k hle ih =>
      intro hk;
      have hkn : k < c.n := by omega;
      have hstep := c.Γ_subset_Γ_succ ⟨k, hkn⟩;
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hstep;
      exact fun A hA => hstep (ih (by omega) hA);
  exact main j.val hij j.isLt;

theorem Γ_subset_ant_of_lt {i j : Fin (c.n + 1)} (hij : i < j) :
    (c.seq i).Γ ⊆ (c.seq j).toSequent.ant := by
  have hval : i.val < j.val := hij;
  have hjval : j.val - 1 < c.n := by omega;
  have hjeq : j = (⟨j.val - 1, hjval⟩ : Fin c.n).succ := by
    apply Fin.ext; simp; omega;
  have h1 := c.Γ_subset_of_le (i := i) (j := (⟨j.val - 1, hjval⟩ : Fin c.n).castSucc)
    (by simp [Fin.le_def]; omega);
  have h2 := c.Γ_subset_ant_succ ⟨j.val - 1, hjval⟩;
  rw [hjeq];
  exact h1.trans h2;

/-! ### Eventual discharge of the front boxed succedent `Θ` along the chain -/

theorem exists_suc_of_mem_Θ {i : Fin (c.n + 1)} {A : Formula α} (hA : A ∈ (c.seq i).Θ) :
    ∃ j, i < j ∧ A ∈ (c.seq j).toSequent.suc := by
  suffices h : ∀ k : ℕ, ∀ i : Fin (c.n + 1), c.n - i.val = k → A ∈ (c.seq i).Θ →
      ∃ j, i < j ∧ A ∈ (c.seq j).toSequent.suc by
    exact h (c.n - i.val) i rfl hA;
  intro k;
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hk hA;
    -- `Θᵢ` is nonempty, so `i` cannot be the last world of the chain (inv4).
    have hlast : i.val ≠ c.n := by
      intro hcontra;
      have hi_last : i = Fin.last c.n := Fin.ext (by simpa using hcontra);
      rw [hi_last, c.eq_last_Θ] at hA;
      simp at hA;
    have hilt : i.val < c.n := by have := i.isLt; omega;
    -- View `i` as `i'.castSucc` for `i' : Fin c.n`, so that the step invariants apply.
    by_cases hAS : A ∈ c.split ⟨i.val, hilt⟩;
    · -- `A` is discharged directly at the next world.
      exact ⟨(⟨i.val, hilt⟩ : Fin c.n).succ, (⟨i.val, hilt⟩ : Fin c.n).castSucc_lt_succ,
        (c.subset_suc_succ ⟨i.val, hilt⟩).1 hAS⟩;
    · -- `□A` survives to the next world; recurse with a strictly smaller measure.
      have hAdiff : A ∈ (c.seq i).Θ \ c.split ⟨i.val, hilt⟩ := Finset.mem_sdiff.mpr ⟨hA, hAS⟩;
      have hboxmem : □A ∈ (c.seq (⟨i.val, hilt⟩ : Fin c.n).succ).toSequent.suc :=
        (c.subset_suc_succ ⟨i.val, hilt⟩).2 (Finset.mem_image_of_mem _ hAdiff);
      have hAnext : A ∈ (c.seq (⟨i.val, hilt⟩ : Fin c.n).succ).Θ :=
        FormulaFinset.iff_mem_prebox_mem.mpr hboxmem;
      have hkey : c.n - (⟨i.val, hilt⟩ : Fin c.n).succ.val < k := by
        simp only [Fin.succ_mk]; omega;
      obtain ⟨j, hij', hAj⟩ :=
        ih (c.n - (⟨i.val, hilt⟩ : Fin c.n).succ.val) hkey
          (⟨i.val, hilt⟩ : Fin c.n).succ rfl hAnext;
      exact ⟨j, ((⟨i.val, hilt⟩ : Fin c.n).castSucc_lt_succ).trans hij', hAj⟩;

/-- The truth lemma for the chain model: at each world `seq i` of the chain, the antecedent is
forced and the succedent is refuted, by induction on the complexity of `A`.

The atom/`⊥`/imp cases mirror the `GL` truth lemma
(`ProvabilityLogic.Gentzen.ExpandedSequent.Kripke.truthlemma`); the box case is simpler than the `GL` version
since it is discharged via the propagation lemmas above instead of constructing a fresh world on
the spot. -/
theorem truthLemma (c : Chain BS S₀) (A : Formula α) (i : Fin (c.n + 1)) :
    (A ∈ (c.seq i).toSequent.ant → Model.World.Forces (M := c.chainModel) i A) ∧
    (A ∈ (c.seq i).toSequent.suc → ¬ Model.World.Forces (M := c.chainModel) i A) := by
  induction A generalizing i with
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
    · intro h
      rw [Model.World.forces_imp]
      rcases ExpandedSequent.of_mem_imp_ant h with h' | h'
      · exact Or.inl ((ihA i).2 h')
      · exact Or.inr ((ihB i).1 h')
    · intro h
      apply Model.World.not_forces_imp.mpr
      obtain ⟨hA, hB⟩ := ExpandedSequent.of_mem_imp_suc h
      exact ⟨(ihA i).1 hA, (ihB i).2 hB⟩
  | box A ih =>
    constructor
    · intro h
      rw [Model.World.forces_box]
      intro j hij
      have hAΓ : A ∈ (c.seq i).Γ := FormulaFinset.iff_mem_prebox_mem.mpr h
      have := c.Γ_subset_ant_of_lt hij hAΓ
      exact (ih j).1 this
    · intro h
      apply Model.World.not_forces_box.mpr
      have hAΘ : A ∈ (c.seq i).Θ := FormulaFinset.iff_mem_prebox_mem.mpr h
      obtain ⟨j, hij, hAj⟩ := c.exists_suc_of_mem_Θ hAΘ
      exact ⟨j, hij, (ih j).2 hAj⟩

end Chain

namespace ProvableGentzen

namespace Kripke

/-- The rooted, finite version of `LogicGLPoint3` Gentzen completeness: any `⊢ᵍ³`-unprovable sequent `S`
has a finite rooted `LogicGLPoint3` countermodel, refuting `S` right at the root. This is the essential
statement, since `GLPoint3.iff_forces_root` only ever assumes forcing at the root of a model. -/
theorem exists_finite_countermodel {S : Sequent α} (h : ⊬ᵍ³ S) :
    ∃ (n : ℕ) (M : RootedModel (Fin (n + 1)) α) (_ : M.toModel.IsFiniteGLPoint3),
      (∀ A ∈ S.ant, M.root.1 ⊩ A) ∧ (∀ A ∈ S.suc, ¬ M.root.1 ⊩ A) := by
  obtain ⟨c⟩ := GLPoint3.exists_chain h h Sequent.subset_self_subfmls
  refine ⟨c.n, c.chainRootedModel, (inferInstanceAs c.chainModel.IsFiniteGLPoint3), ?_, ?_⟩
  · intro A hA
    exact (c.truthLemma A 0).1 (c.subset_head.ant_subset hA)
  · intro A hA
    exact (c.truthLemma A 0).2 (c.subset_head.suc_subset hA)

/-- Gentzen completeness for `LogicGLPoint3`: a sequent valid in every finite `LogicGLPoint3` model is provable.
Proved by contraposition, from the rooted finite countermodel of `exists_finite_countermodel`. -/
theorem completeness {S : Sequent α}
    (h : ∀ {κ : Type}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ S) :
    ⊢ᵍ³ S := by
  by_contra hS
  obtain ⟨n, M, hFin, hant, hsuc⟩ := exists_finite_countermodel hS
  haveI := hFin
  obtain ⟨D, hD, hDforces⟩ := h M.toModel M.root.1 hant
  exact hsuc D hD hDforces

/-- `completeness`, generalized to `LogicGLPoint3` models whose world type lives in an arbitrary
universe `w`, not just `Type 0`. Obtained from `completeness` by `ULift`-lifting the
`Fin (n + 1)` countermodel it produces into `Type w` via `Model.uLift`. -/
theorem completeness_universe {S : Sequent α}
    (h : ∀ {κ : Type w}, [Nonempty κ] → ∀ M : Model κ α, [M.IsFiniteGLPoint3] → M ⊧ S) :
    ⊢ᵍ³ S := by
  apply completeness;
  intro κ _ M _ x hant;
  obtain ⟨D, hD, hDforces⟩ := h M.uLift.{w} (ULift.up x)
    (fun C hC => Model.forces_uLift_iff.mpr (hant C hC));
  exact ⟨D, hD, Model.forces_uLift_iff.mp hDforces⟩

end Kripke

end ProvableGentzen

end GLPoint3

end
