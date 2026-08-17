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
  (∀ lf ∈ S.ant, L lf.label ⊩[_] lf.formula) →
  ∃ lf ∈ S.suc, L lf.label ⊩[_] lf.formula

notation:50 M " ⊧ˡ[" L "] " S:51 => Model.ValidateLabelled M L S

variable {L : M.LabelMap} {R R' : Finset LabelRel} {Γ Γ' Δ Δ' : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

lemma validate_labelled_axm : M ⊧ˡ[L] (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) := by
  intro _ h;
  exact ⟨x ∶ A, by grind, h _ (by grind)⟩;

lemma validate_labelled_botL : M ⊧ˡ[L] (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) := by
  intro _ h;
  have := h (x ∶ (⊥ : Formula α)) (by grind);
  grind;

lemma validate_labelled_wkRel (h : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ)) (hR : R ⊆ R') : M ⊧ˡ[L] (R' ⸴ Γ ⟹ˡ Δ) := by
  intro hrel hant;
  exact h (λ p hp => hrel p (hR hp)) hant;

lemma validate_labelled_wkAnt (h : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ)) (hΓ : Γ ⊆ Γ') : M ⊧ˡ[L] (R ⸴ Γ' ⟹ˡ Δ) := by
  intro hrel hant;
  exact h hrel (λ lf hlf => hant lf (hΓ hlf));

lemma validate_labelled_wkSuc (h : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ)) (hΔ : Δ ⊆ Δ') : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ') := by
  intro hrel hant;
  obtain ⟨lf, hlf, h⟩ := h hrel hant;
  exact ⟨lf, hΔ hlf, h⟩;

section WithDecidableEq

variable [DecidableEq α]

lemma validate_labelled_impL
  (h₁ : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ))
  (h₂ : M ⊧ˡ[L] (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ))
  : M ⊧ˡ[L] (R ⸴ insert (x ∶ A 🡒 B) Γ ⟹ˡ Δ) := by
  intro hrel hant;
  replace h₁ := h₁ hrel;
  replace h₂ := h₂ hrel;
  simp only [Finset.mem_insert, forall_eq_or_imp] at hant;
  grind;

lemma validate_labelled_impR
  (h : M ⊧ˡ[L] (R ⸴ insert (x ∶ A) Γ ⟹ˡ insert (x ∶ B) Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ insert (x ∶ A 🡒 B) Δ) := by
  intro hrel hant;
  by_cases hA : L x ⊩[_] A;
  . obtain ⟨lf, hlf, hf⟩ := h hrel (by grind);
    rcases Finset.mem_insert.mp hlf with rfl | hlf;
    . exact ⟨x ∶ A 🡒 B, by grind, by grind⟩;
    . exact ⟨lf, by grind, hf⟩;
  . exact ⟨x ∶ A 🡒 B, by grind, by grind⟩;

lemma validate_labelled_boxL
  (hxy : (x, y) ∈ R) (hxA : (x ∶ □A) ∈ Γ)
  (h : M ⊧ˡ[L] (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ) := by
  intro hrel hant;
  apply h hrel;
  intro lf hlf;
  rcases Finset.mem_insert.mp hlf with rfl | hlf;
  . exact hant (x ∶ □A) hxA (L y) (hrel (x, y) hxy);
  . exact hant lf hlf;

end WithDecidableEq

section WithDecidableEqBoxRLob

variable [DecidableEq α]

open LabelledSequent in
lemma validate_labelled_boxRLob [M.IsGL]
  (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels)
  (h : ∀ L : M.LabelMap, M ⊧ˡ[L] (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) := by
  intro hrel hant;
  by_contra hC;
  push Not at hC;
  have hyx : y ≠ x := by
    rintro rfl;
    exact hfresh $ mem_labels_of_mem_suc (lf := y ∶ □A) (by grind);
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
        have := fst_mem_labels_of_mem_rel (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) hp';
        rwa [heq] at this;
      have h₂ : p.2 ≠ y := by
        intro heq;
        apply hfresh;
        have := snd_mem_labels_of_mem_rel (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) hp';
        rwa [heq] at this;
      simpa [Function.update_of_ne h₁, Function.update_of_ne h₂] using hrel p hp';
  have hant' : ∀ lf ∈ insert (y ∶ □A) Γ,
      Function.update L y t lf.label ⊩[_] lf.formula := by
    rintro lf hlf;
    rcases Finset.mem_insert.mp hlf with rfl | hlf';
    . show Function.update L y t y ⊩[_] □A;
      rw [Function.update_self];
      intro u Rtu;
      by_contra hu;
      exact ht u ⟨_root_.trans Rxt Rtu, hu⟩ Rtu;
    . have hly : lf.label ≠ y := by
        intro hly;
        apply hfresh;
        have := mem_labels_of_mem_ant (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) hlf';
        rwa [hly] at this;
      rw [Function.update_of_ne hly];
      exact hant lf hlf';
  obtain ⟨lf, hlf, hf⟩ := h (Function.update L y t) hrel' hant';
  rcases Finset.mem_insert.mp hlf with rfl | hlf';
  . apply hntA;
    have : Function.update L y t y ⊩[_] A := hf;
    rwa [Function.update_self] at this;
  . have hly : lf.label ≠ y := by
      intro hly;
      apply hfresh;
      have := mem_labels_of_mem_suc (S := R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) (lf := lf) (by grind);
      rwa [hly] at this;
    apply hC lf (by grind);
    rwa [Function.update_of_ne hly] at hf;

end WithDecidableEqBoxRLob

lemma validate_labelled_irref [Std.Irrefl M.Rel] (hxx : (x, x) ∈ R) : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ) := by
  intro hrel _;
  exact absurd (hrel (x, x) hxx) (Std.Irrefl.irrefl _);

lemma validate_labelled_trans [IsTrans _ M.Rel]
  (hxy : (x, y) ∈ R) (hyz : (y, z) ∈ R)
  (h : M ⊧ˡ[L] (insert (x, z) R ⸴ Γ ⟹ˡ Δ))
  : M ⊧ˡ[L] (R ⸴ Γ ⟹ˡ Δ) := by
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
  intro κ _ M _;
  induction h with
  | axm x A => exact λ _ => validate_labelled_axm;
  | botL x => exact λ _ => validate_labelled_botL;
  | wkRel _ hR ih => exact λ L => validate_labelled_wkRel (ih L) hR;
  | wkAnt _ hΓ ih => exact λ L => validate_labelled_wkAnt (ih L) hΓ;
  | wkSuc _ hΔ ih => exact λ L => validate_labelled_wkSuc (ih L) hΔ;
  | impL _ _ ih₁ ih₂ => exact λ L => validate_labelled_impL (ih₁ L) (ih₂ L);
  | impR _ ih => exact λ L => validate_labelled_impR (ih L);
  | boxL hxy hxA _ ih => exact λ L => validate_labelled_boxL hxy hxA (ih L);
  | boxRLob hfresh _ ih => exact λ L => validate_labelled_boxRLob hfresh ih;
  | irref hxx => exact λ _ => validate_labelled_irref hxx;
  | trans hxy hyz _ ih => exact λ L => validate_labelled_trans hxy hyz (ih L);

theorem soundness_formula [DecidableEq α] {x : Label} {A : Formula α} (h : ⊢ˡᵍ[GL] (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) :
  ∀ {κ}, [Nonempty κ] → ∀ M : Model κ α, [M.IsGL] → M.Validate A := by
  intro κ _ M _ w;
  obtain ⟨lf, hlf, hf⟩ := soundness h M (λ _ => w) (by grind) (by grind);
  grind;

end Kripke

end LogicGL.ProvableLabelledGentzen


section

variable {α : Type u} [DecidableEq α]

def Sequent.toLabelled (z : Label) (S : Sequent α) : LabelledSequent α :=
  ∅ ⸴ S.ant.image (z ∶ ·) ⟹ˡ S.suc.image (z ∶ ·)


variable {R : Finset LabelRel} {Γ Δ Θ : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

namespace LogicGL

namespace ProvableLabelledGentzen

lemma transMany (T : Finset Label) (hzy : (z, y) ∈ R) (hT : ∀ x ∈ T, (x, z) ∈ R)
  (π : ⊢ˡᵍ[GL] ((R ∪ T.image (·, y)) ⸴ Γ ⟹ˡ Δ)) : ⊢ˡᵍ[GL] (R ⸴ Γ ⟹ˡ Δ) := by
  induction T using Finset.induction generalizing R with
  | empty => simpa using π;
  | insert x T hxT ih =>
    apply trans (hxy := hT x (by simp)) (hyz := hzy);
    apply ih (by grind) (by grind);
    apply wkRel π;
    intro p hp;
    simp only [Finset.image_insert, Finset.mem_union, Finset.mem_insert] at hp ⊢;
    grind;

lemma boxLMany (T : Finset (Label × Formula α)) (hT : ∀ p ∈ T, (p.1, y) ∈ R ∧ (p.1 ∶ □p.2) ∈ Γ)
  (π : ⊢ˡᵍ[GL] (R ⸴ (Γ ∪ T.image (fun p => y ∶ p.2)) ⟹ˡ Δ)) : ⊢ˡᵍ[GL] (R ⸴ Γ ⟹ˡ Δ) := by
  induction T using Finset.induction generalizing Γ with
  | empty => simpa using π;
  | insert p T hpT ih =>
    apply boxL (hT p (by simp)).1 (hT p (by simp)).2;
    apply ih (fun q hq =>
      ⟨(hT q (Finset.mem_insert_of_mem hq)).1,
        Finset.mem_insert_of_mem (hT q (Finset.mem_insert_of_mem hq)).2⟩);
    apply wkAnt π;
    intro f hf;
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
lemma LabelledFormula.boxTarget_eq_some {f : LabelledFormula α} {p : Label × Formula α} :
  f.boxTarget y R = some p ↔ f = (p.1 ∶ □p.2) ∧ (p.1, y) ∈ R := by
  obtain ⟨x', A'⟩ := f;
  obtain ⟨x, B⟩ := p;
  (cases A' <;> simp [LabelledFormula.boxTarget]);
  grind;

namespace LogicGL

def boxTargets (y : Label) (R : Finset LabelRel) (Θ : Finset (LabelledFormula α)) :
  Finset (Label × Formula α) :=
  Θ.filterMap (LabelledFormula.boxTarget y R) (by
    intro f f' p hf hf';
    rw [Option.mem_def, LabelledFormula.boxTarget_eq_some] at hf hf';
    grind)

omit [DecidableEq α] in
@[simp, grind =]
lemma mem_boxTargets : (x, B) ∈ boxTargets y R Θ ↔ (x, y) ∈ R ∧ (x ∶ □B) ∈ Θ := by
  simp only [boxTargets, Finset.mem_filterMap, LabelledFormula.boxTarget_eq_some];
  grind;


namespace ProvableGentzen

lemma toLabelledGentzenAux {S : Sequent α} (h : ⊢ᵍ[GL] S) :
  ∀ (z : Label) (R : Finset LabelRel) (Θ : Finset (LabelledFormula α)),
  (∀ B ∈ S.ant, (z ∶ B) ∈ Θ ∨ ∃ x C, B = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ) →
  ⊢ˡᵍ[GL] (R ⸴ Θ ⟹ˡ S.suc.image (z ∶ ·)) := by
  induction h using ProvableGentzen.rec with
  | axm A =>
    intro z R Θ H;
    simp only [Finset.image_singleton];
    if hzA : (z ∶ A) ∈ Θ then
      exact ProvableLabelledGentzen.union z A hzA (by simp);
    else
      have hA : ∃ x C, A = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ := (H A (by simp)).resolve_left hzA;
      clear hzA H;
      cases A with
      | box C =>
        have hex : ∃ x : Label, (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ := by grind;
        obtain ⟨w, hwz, hwC⟩ := hex;
        exact ProvableLabelledGentzen.loop w z C hwz hwC (by simp);
      | atom a => simp at hA;
      | bot => simp at hA;
      | imp B C => simp at hA;
  | botL =>
    intro z R Θ H;
    have hz : (z ∶ (⊥ : Formula α)) ∈ Θ := by have := H ⊥ (by simp); grind;
    exact ProvableLabelledGentzen.botL_mem z hz;
  | wkL h h' ih =>
    intro z R Θ H;
    exact ih z R Θ (fun B hB => H B (h' hB));
  | wkR h h' ih =>
    intro z R Θ H;
    exact ProvableLabelledGentzen.wkSuc (ih z R Θ H) (Finset.image_subset_image h');
  | @impL Γ Δ A B h₁ h₂ ih₁ ih₂ =>
    intro z R Θ H;
    have hAB : (z ∶ A 🡒 B) ∈ Θ := by have := H (A 🡒 B) (by simp); grind;
    have h₁ := ih₁ z R Θ (fun C hC => H C (Finset.mem_insert_of_mem hC));
    have h₂ := ih₂ z R (insert (z ∶ B) Θ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C (Finset.mem_insert_of_mem hC); grind;
    );
    rw [(show Θ = insert (z ∶ A 🡒 B) Θ by grind)];
    simp only [Finset.image_insert] at h₁;
    exact ProvableLabelledGentzen.impL h₁ h₂;
  | @impR Γ Δ A B h ih =>
    intro z R Θ H;
    have h := ih z R (insert (z ∶ A) Θ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C hC; grind;
    );
    simp only [Finset.image_insert] at h ⊢;
    exact ProvableLabelledGentzen.impR h;
  | @boxGL Γ A h ih =>
    intro z R Θ H;
    simp only [Finset.image_singleton];
    rw [← insert_empty_eq];
    apply ProvableLabelledGentzen.boxRLob (x := z) (A := A)
      (y := (R ⸴ Θ ⟹ˡ insert (z ∶ □A) ∅).freshLabel) (hfresh := LabelledSequent.freshLabel_notMem);
    generalize (R ⸴ Θ ⟹ˡ insert (z ∶ □A) ∅).freshLabel = y;
    apply ProvableLabelledGentzen.transMany (z := z) (y := y)
      (T := (R.filter (fun p => p.2 = z)).image Prod.fst)
      (by grind) (by intro x hx; simp at hx; grind);
    set R' := insert (z, y) R ∪ ((R.filter (fun p => p.2 = z)).image Prod.fst).image (·, y)
      with hR';
    apply ProvableLabelledGentzen.boxLMany (y := y) (T := boxTargets y R' (insert (y ∶ □A) Θ))
      (by rintro ⟨x, B⟩ hp; exact mem_boxTargets.mp hp);
    have hzy : (z, y) ∈ R' := by grind;
    have hsat : ∀ x, (x, z) ∈ R → (x, y) ∈ R' := by
      intro x hxz;
      apply Finset.mem_union_right;
      have h₁ : (x, z) ∈ R.filter (fun p => p.2 = z) := Finset.mem_filter.mpr ⟨hxz, rfl⟩;
      have h₂ : x ∈ (R.filter (fun p => p.2 = z)).image Prod.fst := Finset.mem_image_of_mem _ h₁;
      exact Finset.mem_image_of_mem _ h₂;
    have h := ih y R'
      (insert (y ∶ □A) Θ ∪ (boxTargets y R' (insert (y ∶ □A) Θ)).image (fun p => y ∶ p.2))
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
