module

public import ProvabilityLogic.Kripke.Basic
public import ProvabilityLogic.LabelledGentzen.GL.Basic
public import ProvabilityLogic.Gentzen.GL.Kripke

/-!
Kripke semantics for the labelled sequent calculus `G3KGL` (`⊢ˡᵍ[GL]`), and its embedding
to and from the label-free Gentzen calculus for `GL` (`ProvableGentzen`/`⊢ᵍ[GL]`).

- [Neg14, Definition 5.3, Theorem 5.4]
-/

@[expose]
public section

variable {κ : Type u} [Nonempty κ]
         {α : Type v}
         {M : Model κ α}


namespace Model

abbrev LabelMap (M : Model κ α) := Label → M.World

@[grind]
def ValidateLabelled (M : Model κ α) (L : M.LabelMap) (S : LabelledSequent α) : Prop :=
  (∀ p ∈ S.rel, L p.1 ≺ L p.2) →
  (∀ ℓA ∈ S.ant, L ℓA.label ⊩[_] ℓA.formula) →
  ∃ ℓA ∈ S.suc, L ℓA.label ⊩[_] ℓA.formula

notation:50 M " ⊧ˡ[" L "] " S:51 => Model.ValidateLabelled M L S

variable {L : M.LabelMap} {R R' : Finset LabelRel} {ℓΓ ℓΓ' ℓΔ ℓΔ' : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

lemma validate_labelled_axm : M ⊧ˡ[L] (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) := by
  intro _ h;
  exact ⟨x ∶ A, by grind, h _ (by grind)⟩;

lemma validate_labelled_botL : M ⊧ˡ[L] (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) := by
  intro _ h;
  have := h (x ∶ (⊥ : Formula α)) (by grind);
  grind;

lemma validate_labelled_wkRel (h : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hR : R ⊆ R') : M ⊧ˡ[L] (R' ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  intro hrel hant;
  exact h (λ p hp => hrel p (hR hp)) hant;

lemma validate_labelled_wkAnt (h : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hΓ : ℓΓ ⊆ ℓΓ') : M ⊧ˡ[L] (R ⸴ ℓΓ' ⟹ˡ ℓΔ) := by
  intro hrel hant;
  exact h hrel (λ ℓA hlf => hant ℓA (hΓ hlf));

lemma validate_labelled_wkSuc (h : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ ℓΔ)) (hΔ : ℓΔ ⊆ ℓΔ') : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ ℓΔ') := by
  intro hrel hant;
  obtain ⟨ℓA, hlf, h⟩ := h hrel hant;
  exact ⟨ℓA, hΔ hlf, h⟩;

section WithDecidableEq

variable [DecidableEq α]

lemma validate_labelled_impL
  (h₁ : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A) ℓΔ))
  (h₂ : M ⊧ˡ[L] (R ⸴ insert (x ∶ B) ℓΓ ⟹ˡ ℓΔ))
  : M ⊧ˡ[L] (R ⸴ insert (x ∶ A 🡒 B) ℓΓ ⟹ˡ ℓΔ) := by
  intro hrel hant;
  replace h₁ := h₁ hrel;
  replace h₂ := h₂ hrel;
  simp only [Finset.mem_insert, forall_eq_or_imp] at hant;
  grind;

lemma validate_labelled_impR
  (h : M ⊧ˡ[L] (R ⸴ insert (x ∶ A) ℓΓ ⟹ˡ insert (x ∶ B) ℓΔ))
  : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ A 🡒 B) ℓΔ) := by
  intro hrel hant;
  by_cases hA : L x ⊩[_] A;
  . obtain ⟨ℓA, hlf, hf⟩ := h hrel (by grind);
    rcases Finset.mem_insert.mp hlf with rfl | hlf;
    . exact ⟨x ∶ A 🡒 B, by grind, by grind⟩;
    . exact ⟨ℓA, by grind, hf⟩;
  . exact ⟨x ∶ A 🡒 B, by grind, by grind⟩;

lemma validate_labelled_boxL
  (hxy : (x, y) ∈ R) (hxA : (x ∶ □A) ∈ ℓΓ)
  (h : M ⊧ˡ[L] (R ⸴ insert (y ∶ A) ℓΓ ⟹ˡ ℓΔ))
  : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  intro hrel hant;
  apply h hrel;
  intro ℓA hlf;
  rcases Finset.mem_insert.mp hlf with rfl | hlf;
  . exact hant (x ∶ □A) hxA (L y) (hrel (x, y) hxy);
  . exact hant ℓA hlf;

end WithDecidableEq

section WithDecidableEqBoxRLob

variable [DecidableEq α]

open LabelledSequent in
lemma validate_labelled_boxRLob [M.IsGL]
  (hfresh : y ∉ (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ).labels)
  (h : ∀ L : M.LabelMap, M ⊧ˡ[L] (insert (x, y) R ⸴ insert (y ∶ □A) ℓΓ ⟹ˡ insert (y ∶ A) ℓΔ))
  : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) := by
  intro hrel hant;
  by_contra hC;
  push Not at hC;
  have hyx : y ≠ x := by
    rintro rfl;
    exact hfresh $ mem_labels_of_mem_suc (ℓA := y ∶ □A) (by grind);
  have hxA : L x ⊮[_] □A := hC (x ∶ □A) (by grind);
  obtain ⟨z, Rxz, hz⟩ := Model.World.not_forces_box.mp hxA;
  obtain ⟨t, ⟨Rxt, hntA⟩, ht⟩ := M.terminalOf {w | L x ≺ w ∧ w ⊮[_] A} ⟨z, Rxz, hz⟩;
  have hrel' : ∀ p ∈ (insert (x, y) R : Finset LabelRel),
      Function.update L y t p.1 ≺ Function.update L y t p.2 := by
    rintro p hp;
    rcases Finset.mem_insert.mp hp with rfl | hp';
    . show Function.update L y t x ≺ Function.update L y t y;
      rw [Function.update_self, Function.update_of_ne (Ne.symm hyx)];
      exact Rxt;
    . have h₁ : p.1 ≠ y := by
        intro heq;
        apply hfresh;
        have := fst_mem_labels_of_mem_rel (S := R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) hp';
        rwa [heq] at this;
      have h₂ : p.2 ≠ y := by
        intro heq;
        apply hfresh;
        have := snd_mem_labels_of_mem_rel (S := R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) hp';
        rwa [heq] at this;
      simpa [Function.update_of_ne h₁, Function.update_of_ne h₂] using hrel p hp';
  have hant' : ∀ ℓA ∈ insert (y ∶ □A) ℓΓ,
      Function.update L y t ℓA.label ⊩[_] ℓA.formula := by
    rintro ℓA hlf;
    rcases Finset.mem_insert.mp hlf with rfl | hlf';
    . show Function.update L y t y ⊩[_] □A;
      rw [Function.update_self];
      intro u Rtu;
      by_contra hu;
      exact ht u ⟨_root_.trans Rxt Rtu, hu⟩ Rtu;
    . have hly : ℓA.label ≠ y := by
        intro hly;
        apply hfresh;
        have := mem_labels_of_mem_ant (S := R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) hlf';
        rwa [hly] at this;
      rw [Function.update_of_ne hly];
      exact hant ℓA hlf';
  obtain ⟨ℓA, hlf, hf⟩ := h (Function.update L y t) hrel' hant';
  rcases Finset.mem_insert.mp hlf with rfl | hlf';
  . apply hntA;
    have : Function.update L y t y ⊩[_] A := hf;
    rwa [Function.update_self] at this;
  . have hly : ℓA.label ≠ y := by
      intro hly;
      apply hfresh;
      have := mem_labels_of_mem_suc (S := R ⸴ ℓΓ ⟹ˡ insert (x ∶ □A) ℓΔ) (ℓA := ℓA) (by grind);
      rwa [hly] at this;
    apply hC ℓA (by grind);
    rwa [Function.update_of_ne hly] at hf;

end WithDecidableEqBoxRLob

lemma validate_labelled_irref [Std.Irrefl M.Rel] (hxx : (x, x) ∈ R) : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  intro hrel _;
  exact absurd (hrel (x, x) hxx) (Std.Irrefl.irrefl _);

lemma validate_labelled_trans [IsTrans _ M.Rel]
  (hxy : (x, y) ∈ R) (hyz : (y, z) ∈ R)
  (h : M ⊧ˡ[L] (insert (x, z) R ⸴ ℓΓ ⟹ˡ ℓΔ))
  : M ⊧ˡ[L] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  intro hrel hant;
  apply h ?_ hant;
  intro p hp;
  rcases Finset.mem_insert.mp hp with rfl | hp;
  . exact _root_.trans (hrel (x, y) hxy) (hrel (y, z) hyz);
  . exact hrel p hp;

end Model


namespace LogicGL.ProvableLabelledGentzen

namespace Kripke

open Model in
/--
Soundness of `G3KGL` with respect to Kripke semantics on `GL` models.

- [Neg14, Theorem 5.4]
-/
theorem soundness [DecidableEq α] {S : LabelledSequent α} (h : ⊢ˡᵍ[GL] S) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGL] → ∀ L : M.LabelMap, M ⊧ˡ[L] S := by
  intro κ _ M _ L;
  induction h generalizing L with
  | axm x A => exact validate_labelled_axm;
  | botL x => exact validate_labelled_botL;
  | wkRel _ hR ih => exact validate_labelled_wkRel (ih L) hR;
  | wkAnt _ hΓ ih => exact validate_labelled_wkAnt (ih L) hΓ;
  | wkSuc _ hΔ ih => exact validate_labelled_wkSuc (ih L) hΔ;
  | impL _ _ ih₁ ih₂ => exact validate_labelled_impL (ih₁ L) (ih₂ L);
  | impR _ ih => exact validate_labelled_impR (ih L);
  | boxL hxy hxA _ ih => exact validate_labelled_boxL hxy hxA (ih L);
  | boxRLob hfresh _ ih => exact validate_labelled_boxRLob hfresh ih;
  | irref hxx => exact validate_labelled_irref hxx;
  | trans hxy hyz _ ih => exact validate_labelled_trans hxy hyz (ih L);

theorem soundness_formula [DecidableEq α] {x : Label} {A : Formula α} (h : ⊢ˡᵍ[GL] (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGL] → M.Validate A := by
  intro κ _ M _ w;
  obtain ⟨ℓA, hlf, hf⟩ := soundness h M (λ _ => w) (by grind) (by grind);
  grind;

end Kripke

end LogicGL.ProvableLabelledGentzen


section

variable {α : Type u} [DecidableEq α]

def Sequent.toLabelled (z : Label) (S : Sequent α) : LabelledSequent α :=
  ∅ ⸴ S.ant.image (z ∶ ·) ⟹ˡ S.suc.image (z ∶ ·)


variable {R : Finset LabelRel} {ℓΓ ℓΔ ℓΘ : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

namespace LogicGL

namespace ProvableLabelledGentzen

lemma transMany (T : Finset Label) (hzy : (z, y) ∈ R) (hT : ∀ x ∈ T, (x, z) ∈ R)
  (π : ⊢ˡᵍ[GL] ((R ∪ T.image (·, y)) ⸴ ℓΓ ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  induction T using Finset.induction generalizing R with
  | empty => simpa using π;
  | insert x T hxT ih =>
    apply trans (hxy := hT x (by simp)) (hyz := hzy);
    apply ih (by grind) (by grind);
    apply wkRel π;
    intro p hp;
    simp only [Finset.image_insert, Finset.mem_union, Finset.mem_insert] at hp ⊢;
    grind;

lemma boxLMany (T : Finset (Label × Formula α)) (hT : ∀ p ∈ T, (p.1, y) ∈ R ∧ (p.1 ∶ □p.2) ∈ ℓΓ)
  (π : ⊢ˡᵍ[GL] (R ⸴ (ℓΓ ∪ T.image (fun p => y ∶ p.2)) ⟹ˡ ℓΔ)) : ⊢ˡᵍ[GL] (R ⸴ ℓΓ ⟹ˡ ℓΔ) := by
  induction T using Finset.induction generalizing ℓΓ with
  | empty => simpa using π;
  | insert p T hpT ih =>
    apply boxL (hT p (by simp)).1 (hT p (by simp)).2;
    apply ih (fun q hq =>
      ⟨(hT q (Finset.mem_insert_of_mem hq)).1,
        Finset.mem_insert_of_mem (hT q (Finset.mem_insert_of_mem hq)).2⟩);
    apply wkAnt π;
    intro ℓA hf;
    simp only [Finset.image_insert, Finset.mem_union, Finset.mem_insert] at hf ⊢;
    grind;

end ProvableLabelledGentzen

end LogicGL

def LabelledFormula.boxTarget (y : Label) (R : Finset LabelRel) :
  LabelledFormula α → Option (Label × Formula α)
  | ⟨x, □B⟩ => if (x, y) ∈ R then some (x, B) else none
  | _ => none

omit [DecidableEq α] in
@[grind =]
lemma LabelledFormula.boxTarget_eq_some {ℓA : LabelledFormula α} {p : Label × Formula α} :
  ℓA.boxTarget y R = some p ↔ ℓA = (p.1 ∶ □p.2) ∧ (p.1, y) ∈ R := by
  obtain ⟨x', A'⟩ := ℓA;
  obtain ⟨x, B⟩ := p;
  (cases A' <;> simp [LabelledFormula.boxTarget]);
  grind;

namespace LogicGL

def boxTargets (y : Label) (R : Finset LabelRel) (ℓΘ : Finset (LabelledFormula α)) :
  Finset (Label × Formula α) :=
  ℓΘ.filterMap (LabelledFormula.boxTarget y R) (by
    intro ℓA ℓB p hf hf';
    rw [Option.mem_def, LabelledFormula.boxTarget_eq_some] at hf hf';
    grind)

omit [DecidableEq α] in
@[simp, grind =]
lemma mem_boxTargets : (x, B) ∈ boxTargets y R ℓΘ ↔ (x, y) ∈ R ∧ (x ∶ □B) ∈ ℓΘ := by
  simp only [boxTargets, Finset.mem_filterMap, LabelledFormula.boxTarget_eq_some];
  grind;


namespace ProvableGentzen

lemma toLabelledGentzenAux {S : Sequent α} (h : ⊢ᵍ[GL] S) :
  ∀ (z : Label) (R : Finset LabelRel) (ℓΘ : Finset (LabelledFormula α)),
  (∀ B ∈ S.ant, (z ∶ B) ∈ ℓΘ ∨ ∃ x C, B = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ ℓΘ) →
  ⊢ˡᵍ[GL] (R ⸴ ℓΘ ⟹ˡ S.suc.image (z ∶ ·)) := by
  induction h using ProvableGentzen.rec with
  | axm A =>
    intro z R ℓΘ H;
    simp only [Finset.image_singleton];
    if hzA : (z ∶ A) ∈ ℓΘ then
      exact ProvableLabelledGentzen.union z A hzA (by simp);
    else
      have hA : ∃ x C, A = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ ℓΘ := (H A (by simp)).resolve_left hzA;
      clear hzA H;
      cases A with
      | box C =>
        have hex : ∃ x : Label, (x, z) ∈ R ∧ (x ∶ □C) ∈ ℓΘ := by grind;
        obtain ⟨w, hwz, hwC⟩ := hex;
        exact ProvableLabelledGentzen.loop w z C hwz hwC (by simp);
      | atom a => simp at hA;
      | bot => simp at hA;
      | imp B C => simp at hA;
  | botL =>
    intro z R ℓΘ H;
    have hz : (z ∶ (⊥ : Formula α)) ∈ ℓΘ := by have := H ⊥ (by simp); grind;
    exact ProvableLabelledGentzen.botL_mem z hz;
  | wkL h h' ih =>
    intro z R ℓΘ H;
    exact ih z R ℓΘ (fun B hB => H B (h' hB));
  | wkR h h' ih =>
    intro z R ℓΘ H;
    exact ProvableLabelledGentzen.wkSuc (ih z R ℓΘ H) (Finset.image_subset_image h');
  | @impL Γ Δ A B h₁ h₂ ih₁ ih₂ =>
    intro z R ℓΘ H;
    have hAB : (z ∶ A 🡒 B) ∈ ℓΘ := by have := H (A 🡒 B) (by simp); grind;
    have h₁ := ih₁ z R ℓΘ (fun C hC => H C (Finset.mem_insert_of_mem hC));
    have h₂ := ih₂ z R (insert (z ∶ B) ℓΘ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C (Finset.mem_insert_of_mem hC); grind;
    );
    rw [(show ℓΘ = insert (z ∶ A 🡒 B) ℓΘ by grind)];
    simp only [Finset.image_insert] at h₁;
    exact ProvableLabelledGentzen.impL h₁ h₂;
  | @impR Γ Δ A B h ih =>
    intro z R ℓΘ H;
    have h := ih z R (insert (z ∶ A) ℓΘ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C hC; grind;
    );
    simp only [Finset.image_insert] at h ⊢;
    exact ProvableLabelledGentzen.impR h;
  | @boxGL Γ A h ih =>
    intro z R ℓΘ H;
    simp only [Finset.image_singleton];
    rw [← insert_empty_eq];
    apply ProvableLabelledGentzen.boxRLob (x := z) (A := A)
      (y := (R ⸴ ℓΘ ⟹ˡ insert (z ∶ □A) ∅).freshLabel) (hfresh := LabelledSequent.freshLabel_notMem);
    generalize (R ⸴ ℓΘ ⟹ˡ insert (z ∶ □A) ∅).freshLabel = y;
    apply ProvableLabelledGentzen.transMany (z := z) (y := y)
      (T := (R.filter (fun p => p.2 = z)).image Prod.fst)
      (by grind) (by intro x hx; simp at hx; grind);
    set R' := insert (z, y) R ∪ ((R.filter (fun p => p.2 = z)).image Prod.fst).image (·, y)
      with hR';
    apply ProvableLabelledGentzen.boxLMany (y := y) (T := boxTargets y R' (insert (y ∶ □A) ℓΘ))
      (by rintro ⟨x, B⟩ hp; exact mem_boxTargets.mp hp);
    have hzy : (z, y) ∈ R' := by grind;
    have hsat : ∀ x, (x, z) ∈ R → (x, y) ∈ R' := by
      intro x hxz;
      apply Finset.mem_union_right;
      have h₁ : (x, z) ∈ R.filter (fun p => p.2 = z) := Finset.mem_filter.mpr ⟨hxz, rfl⟩;
      have h₂ : x ∈ (R.filter (fun p => p.2 = z)).image Prod.fst := Finset.mem_image_of_mem _ h₁;
      exact Finset.mem_image_of_mem _ h₂;
    have h := ih y R'
      (insert (y ∶ □A) ℓΘ ∪ (boxTargets y R' (insert (y ∶ □A) ℓΘ)).image (fun p => y ∶ p.2))
      (fun E hE => by
        rcases Finset.mem_insert.mp hE with rfl | hE;
        . exact Or.inl (by grind);
        . rcases Finset.mem_union.mp hE with hEΓ | hEbox;
          . left;
            apply Finset.mem_union_right;
            rcases H (□E) (Finset.mem_image_of_mem _ hEΓ) with hzE | ⟨x, C, hEC, hxz, hxC⟩;
            . exact Finset.mem_image_of_mem _ (mem_boxTargets.mpr ⟨hzy, by grind⟩);
            . obtain rfl : E = C := by grind;
              exact Finset.mem_image_of_mem _ (mem_boxTargets.mpr ⟨hsat x hxz, by grind⟩);
          . obtain ⟨B, hBΓ, rfl⟩ := Finset.mem_image.mp hEbox;
            right;
            rcases H (□B) hEbox with hzB | ⟨x, C, hBC, hxz, hxC⟩;
            . exact ⟨z, B, rfl, hzy, by grind⟩;
            . obtain rfl : B = C := by grind;
              exact ⟨x, B, rfl, hsat x hxz, by grind⟩;
      );
    simp only [Finset.image_singleton] at h;
    rw [insert_empty_eq];
    exact h;

lemma toLabelledGentzen (z : Label) {S : Sequent α} (h : ⊢ᵍ[GL] S) : ⊢ˡᵍ[GL] (S.toLabelled z) :=
  toLabelledGentzenAux h z ∅ (S.ant.image (z ∶ ·)) (fun _ hB => Or.inl (Finset.mem_image_of_mem _ hB))

end ProvableGentzen


theorem ProvableLabelledGentzen.toGentzen {x : Label} {A : Formula α}
  (h : ⊢ˡᵍ[GL] (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) : ⊢ᵍ[GL] (∅ ⟹ {A}) := by
  apply ProvableGentzen.Kripke.completeness;
  intro κ _ M _ w;
  exact Model.World.forces_singleton_sequent.mpr
    (ProvableLabelledGentzen.Kripke.soundness_formula h M w);

theorem iff_provableGentzen_provableLabelledGentzen {x : Label} {A : Formula α} :
  ⊢ᵍ[GL] (∅ ⟹ {A}) ↔ ⊢ˡᵍ[GL] (∅ ⸴ ∅ ⟹ˡ {x ∶ A}) := by
  constructor;
  . intro h;
    simpa [Sequent.toLabelled] using ProvableGentzen.toLabelledGentzen x h;
  . exact ProvableLabelledGentzen.toGentzen;

end LogicGL

end

end
