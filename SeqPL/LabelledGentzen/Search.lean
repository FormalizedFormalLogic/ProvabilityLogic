module

public import SeqPL.LabelledGentzen.Basic
public import Mathlib.Data.Finset.Prod
meta import SeqPL.LabelledGentzen.Basic

@[expose]
public section

/-!
Saturation for proof search in the labelled sequent calculus `G3KGL`.

`saturate` exhaustively applies the propositional rules (`impL`/`impR`), the
relational rule `Trans` and the modal rule `L□` (each keeping its principal
formula, so that every step only *adds* labelled formulas or relational atoms),
until either the sequent is closed by `axm`/`botL`/`Irref`, or a fixed point is
reached.  Saturated open sequents satisfy the Hintikka-style closure conditions
recorded in `LabelledSequent.Saturated`; the remaining boxed formulas in the
succedent are exactly the targets for `R□^Löb` in the outer proof search.

Termination is measured by the number of facts still missing from the finite
universe determined by the labels and the subformula closure of the sequent,
both of which are invariant under saturation steps.
-/

variable {α : Type u} [DecidableEq α]

namespace LabelledSequent

variable {S : LabelledSequent α} {Rf : Finset (Label × Label)} {Γf Δf : Finset (LabelledFormula α)}
variable {lf : LabelledFormula α} {p : Label × Label} {x y z : Label} {A B : Formula α}

/-- The subformula closure of all formulas occurring in `S`. -/
@[grind]
def sf (S : LabelledSequent α) : FormulaFinset α := (S.ant ∪ S.suc).biUnion (·.formula.subfmls)

@[grind =>]
lemma mem_sf_of_mem_ant (h : lf ∈ S.ant) : lf.formula ∈ S.sf := by
  simp only [sf, Finset.mem_biUnion];
  exact ⟨lf, by grind, Formula.mem_subfmls_self⟩;

@[grind =>]
lemma mem_sf_of_mem_suc (h : lf ∈ S.suc) : lf.formula ∈ S.sf := by
  simp only [sf, Finset.mem_biUnion];
  exact ⟨lf, by grind, Formula.mem_subfmls_self⟩;

@[grind =>]
lemma subfmls_subset_sf (h : A ∈ S.sf) : A.subfmls ⊆ S.sf := by
  intro C hC;
  simp only [sf, Finset.mem_biUnion] at h ⊢;
  obtain ⟨lf, hlf, hA⟩ := h;
  exact ⟨lf, hlf, Formula.subfmls_trans hA hC⟩;

@[grind =>]
lemma mem_sf_of_imp_left (h : (A 🡒 B) ∈ S.sf) : A ∈ S.sf :=
  subfmls_subset_sf h Formula.mem_subfmls_imp_left

@[grind =>]
lemma mem_sf_of_imp_right (h : (A 🡒 B) ∈ S.sf) : B ∈ S.sf :=
  subfmls_subset_sf h Formula.mem_subfmls_imp_right

@[grind =>]
lemma mem_sf_of_box (h : (□A) ∈ S.sf) : A ∈ S.sf :=
  subfmls_subset_sf h Formula.mem_subfmls_box

omit [DecidableEq α] in
@[grind =>]
lemma mem_labels_of_mem_ant (h : lf ∈ S.ant) : lf.label ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma mem_labels_of_mem_suc (h : lf ∈ S.suc) : lf.label ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma fst_mem_labels_of_mem_rel (h : p ∈ S.rel) : p.1 ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

omit [DecidableEq α] in
@[grind =>]
lemma snd_mem_labels_of_mem_rel (h : p ∈ S.rel) : p.2 ∈ S.labels := by
  simp only [labels, Finset.mem_union, Finset.mem_image];
  grind;

/-- The finite universe of labelled formulas available to saturation. -/
@[grind]
def lfUniv (S : LabelledSequent α) : Finset (LabelledFormula α) :=
  S.labels.biUnion (fun x => S.sf.image (x ∶ ·))

lemma mem_lfUniv (hl : x ∈ S.labels) (hf : A ∈ S.sf) : (x ∶ A) ∈ S.lfUniv := by
  simp only [lfUniv, Finset.mem_biUnion, Finset.mem_image];
  exact ⟨x, hl, A, hf, rfl⟩;

lemma ant_subset_lfUniv : S.ant ⊆ S.lfUniv :=
  fun _ h => mem_lfUniv (mem_labels_of_mem_ant h) (mem_sf_of_mem_ant h)

lemma suc_subset_lfUniv : S.suc ⊆ S.lfUniv :=
  fun _ h => mem_lfUniv (mem_labels_of_mem_suc h) (mem_sf_of_mem_suc h)

omit [DecidableEq α] in
lemma rel_subset_labelsProduct : S.rel ⊆ S.labels ×ˢ S.labels := fun _ h =>
  Finset.mem_product.mpr ⟨fst_mem_labels_of_mem_rel h, snd_mem_labels_of_mem_rel h⟩

/-- Termination measure for `saturate`: the number of labelled formulas and
relational atoms still missing from the finite universe of the sequent. -/
def saturationMeasure (S : LabelledSequent α) : ℕ :=
  (S.lfUniv.card - S.ant.card) + (S.lfUniv.card - S.suc.card) +
  ((S.labels ×ˢ S.labels).card - S.rel.card)

/-! ### Invariance of `labels` and `sf` under saturation steps -/

lemma labels_insert_ant :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).labels = insert lf.label (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  ext w;
  simp only [labels, Finset.image_insert, Finset.mem_union, Finset.mem_insert];
  tauto;

lemma labels_insert_suc :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).labels = insert lf.label (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  ext w;
  simp only [labels, Finset.image_insert, Finset.mem_union, Finset.mem_insert];
  tauto;

omit [DecidableEq α] in
lemma labels_insert_rel :
  (insert p Rf ⸴ Γf ⟹ˡ Δf).labels = insert p.1 (insert p.2 (Rf ⸴ Γf ⟹ˡ Δf).labels) := by
  ext w;
  simp only [labels, Finset.image_insert, Finset.mem_union, Finset.mem_insert];
  tauto;

lemma labels_insert_ant_of_mem (h : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  rw [labels_insert_ant, Finset.insert_eq_self.mpr h];

lemma labels_insert_suc_of_mem (h : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  rw [labels_insert_suc, Finset.insert_eq_self.mpr h];

omit [DecidableEq α] in
lemma labels_insert_rel_of_mem (h1 : p.1 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (h2 : p.2 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) :
  (insert p Rf ⸴ Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  rw [labels_insert_rel, Finset.insert_eq_self.mpr h2, Finset.insert_eq_self.mpr h1];

lemma sf_insert_ant :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).sf = lf.formula.subfmls ∪ (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  simp [sf, Finset.insert_union, Finset.biUnion_insert];

lemma sf_insert_suc :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).sf = lf.formula.subfmls ∪ (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  simp [sf, Finset.union_insert, Finset.biUnion_insert];

lemma sf_insert_rel : (insert p Rf ⸴ Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := rfl

lemma sf_insert_ant_of_mem (h : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  rw [sf_insert_ant, Finset.union_eq_right.mpr (subfmls_subset_sf h)];

lemma sf_insert_suc_of_mem (h : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  rw [sf_insert_suc, Finset.union_eq_right.mpr (subfmls_subset_sf h)];

lemma lfUniv_congr {S S' : LabelledSequent α} (hlab : S.labels = S'.labels) (hsf : S.sf = S'.sf) :
  S.lfUniv = S'.lfUniv := by
  rw [lfUniv, lfUniv, hlab, hsf];

/-! ### Decrease of `saturationMeasure` under saturation steps -/

lemma saturationMeasure_insert_ant_lt
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) (hnew : lf ∉ Γf) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hlab := labels_insert_ant_of_mem (Δf := Δf) hl;
  have hsf := sf_insert_ant_of_mem hf;
  have hU := lfUniv_congr hlab hsf;
  have hsub : insert lf Γf ⊆ (Rf ⸴ Γf ⟹ˡ Δf).lfUniv :=
    hU ▸ ant_subset_lfUniv (S := Rf ⸴ insert lf Γf ⟹ˡ Δf);
  have hcard := Finset.card_le_card hsub;
  simp only [saturationMeasure, hU, hlab, Finset.card_insert_of_notMem hnew] at hcard ⊢;
  omega;

lemma saturationMeasure_insert_ant_le
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ insert lf Γf ⟹ˡ Δf).saturationMeasure ≤ (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  by_cases hnew : lf ∈ Γf;
  · rw [Finset.insert_eq_self.mpr hnew];
  · exact (saturationMeasure_insert_ant_lt hl hf hnew).le;

lemma saturationMeasure_insert_suc_lt
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) (hnew : lf ∉ Δf) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hlab := labels_insert_suc_of_mem (Γf := Γf) hl;
  have hsf := sf_insert_suc_of_mem hf;
  have hU := lfUniv_congr hlab hsf;
  have hsub : insert lf Δf ⊆ (Rf ⸴ Γf ⟹ˡ Δf).lfUniv :=
    hU ▸ suc_subset_lfUniv (S := Rf ⸴ Γf ⟹ˡ insert lf Δf);
  have hcard := Finset.card_le_card hsub;
  simp only [saturationMeasure, hU, hlab, Finset.card_insert_of_notMem hnew] at hcard ⊢;
  omega;

lemma saturationMeasure_insert_suc_le
  (hl : lf.label ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hf : lf.formula ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf) :
  (Rf ⸴ Γf ⟹ˡ insert lf Δf).saturationMeasure ≤ (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  by_cases hnew : lf ∈ Δf;
  · rw [Finset.insert_eq_self.mpr hnew];
  · exact (saturationMeasure_insert_suc_lt hl hf hnew).le;

lemma saturationMeasure_insert_rel_lt
  (h1 : p.1 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (h2 : p.2 ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels) (hnew : p ∉ Rf) :
  (insert p Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hlab := labels_insert_rel_of_mem (Γf := Γf) (Δf := Δf) h1 h2;
  have hU := lfUniv_congr hlab (sf_insert_rel (p := p));
  have hsub : insert p Rf ⊆ (Rf ⸴ Γf ⟹ˡ Δf).labels ×ˢ (Rf ⸴ Γf ⟹ˡ Δf).labels := by
    have := rel_subset_labelsProduct (S := insert p Rf ⸴ Γf ⟹ˡ Δf);
    rwa [hlab] at this;
  have hcard := Finset.card_le_card hsub;
  simp only [saturationMeasure, hU, hlab, Finset.card_insert_of_notMem hnew] at hcard ⊢;
  omega;

/-! ### Rule-level measure lemmas -/

lemma saturationMeasure_impR (h : (x ∶ A 🡒 B) ∈ Δf) (hnew : (x ∶ A) ∉ Γf ∨ (x ∶ B) ∉ Δf) :
  (Rf ⸴ insert (x ∶ A) Γf ⟹ˡ insert (x ∶ B) Δf).saturationMeasure <
  (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure := by
  have hAB : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf := mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) h;
  have hABm : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).sf :=
    mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  have hx : x ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels := mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) h;
  have hxm : x ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).labels :=
    mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  rcases hnew with hA | hB;
  · exact lt_of_lt_of_le
      (saturationMeasure_insert_ant_lt hxm (mem_sf_of_imp_left hABm) hA)
      (saturationMeasure_insert_suc_le hx (mem_sf_of_imp_right hAB));
  · exact lt_of_le_of_lt
      (saturationMeasure_insert_ant_le hxm (mem_sf_of_imp_left hABm))
      (saturationMeasure_insert_suc_lt hx (mem_sf_of_imp_right hAB) hB);

lemma saturationMeasure_impL_left (h : (x ∶ A 🡒 B) ∈ Γf) (hnew : (x ∶ A) ∉ Δf) :
  (Rf ⸴ Γf ⟹ˡ insert (x ∶ A) Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_suc_lt
    (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)
    (mem_sf_of_imp_left (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h)) hnew

lemma saturationMeasure_impL_right (h : (x ∶ A 🡒 B) ∈ Γf) (hnew : (x ∶ B) ∉ Γf) :
  (Rf ⸴ insert (x ∶ B) Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_ant_lt
    (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)
    (mem_sf_of_imp_right (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h)) hnew

lemma saturationMeasure_boxL (hR : (x, y) ∈ Rf) (h : (x ∶ □A) ∈ Γf) (hnew : (y ∶ A) ∉ Γf) :
  (Rf ⸴ insert (y ∶ A) Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_ant_lt
    (snd_mem_labels_of_mem_rel (p := (x, y)) hR)
    (mem_sf_of_box (mem_sf_of_mem_ant (lf := x ∶ □A) h)) hnew

lemma saturationMeasure_trans (hxy : (x, y) ∈ Rf) (hyz : (y, z) ∈ Rf) (hnew : (x, z) ∉ Rf) :
  (insert (x, z) Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure < (Rf ⸴ Γf ⟹ˡ Δf).saturationMeasure :=
  saturationMeasure_insert_rel_lt
    (fst_mem_labels_of_mem_rel (p := (x, y)) hxy)
    (snd_mem_labels_of_mem_rel (p := (y, z)) hyz) hnew

/-! ### Rule-level invariance lemmas (for propagating `labels`/`sf` through `saturate`) -/

lemma labels_impR (h : (x ∶ A 🡒 B) ∈ Δf) :
  (Rf ⸴ insert (x ∶ A) Γf ⟹ˡ insert (x ∶ B) Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels := by
  have hxm : x ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).labels :=
    mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  have hx : x ∈ (Rf ⸴ Γf ⟹ˡ Δf).labels := mem_labels_of_mem_suc (lf := x ∶ A 🡒 B) h;
  rw [labels_insert_ant_of_mem (lf := x ∶ A) hxm, labels_insert_suc_of_mem (lf := x ∶ B) hx];

lemma sf_impR (h : (x ∶ A 🡒 B) ∈ Δf) :
  (Rf ⸴ insert (x ∶ A) Γf ⟹ˡ insert (x ∶ B) Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf := by
  have hABm : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ insert (x ∶ B) Δf).sf :=
    mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) (Finset.mem_insert_of_mem h);
  have hAB : (A 🡒 B) ∈ (Rf ⸴ Γf ⟹ˡ Δf).sf := mem_sf_of_mem_suc (lf := x ∶ A 🡒 B) h;
  rw [sf_insert_ant_of_mem (lf := x ∶ A) (mem_sf_of_imp_left hABm),
    sf_insert_suc_of_mem (lf := x ∶ B) (mem_sf_of_imp_right hAB)];

lemma labels_impL_left (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ Γf ⟹ˡ insert (x ∶ A) Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_suc_of_mem (lf := x ∶ A) (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)

lemma sf_impL_left (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ Γf ⟹ˡ insert (x ∶ A) Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf :=
  sf_insert_suc_of_mem (lf := x ∶ A) (mem_sf_of_imp_left (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h))

lemma labels_impL_right (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ insert (x ∶ B) Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_ant_of_mem (lf := x ∶ B) (mem_labels_of_mem_ant (lf := x ∶ A 🡒 B) h)

lemma sf_impL_right (h : (x ∶ A 🡒 B) ∈ Γf) :
  (Rf ⸴ insert (x ∶ B) Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf :=
  sf_insert_ant_of_mem (lf := x ∶ B) (mem_sf_of_imp_right (mem_sf_of_mem_ant (lf := x ∶ A 🡒 B) h))

lemma labels_boxL (hR : (x, y) ∈ Rf) :
  (Rf ⸴ insert (y ∶ A) Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_ant_of_mem (lf := y ∶ A) (snd_mem_labels_of_mem_rel (p := (x, y)) hR)

lemma sf_boxL (h : (x ∶ □A) ∈ Γf) :
  (Rf ⸴ insert (y ∶ A) Γf ⟹ˡ Δf).sf = (Rf ⸴ Γf ⟹ˡ Δf).sf :=
  sf_insert_ant_of_mem (lf := y ∶ A) (mem_sf_of_box (mem_sf_of_mem_ant (lf := x ∶ □A) h))

omit [DecidableEq α] in
lemma labels_trans (hxy : (x, y) ∈ Rf) (hyz : (y, z) ∈ Rf) :
  (insert (x, z) Rf ⸴ Γf ⟹ˡ Δf).labels = (Rf ⸴ Γf ⟹ˡ Δf).labels :=
  labels_insert_rel_of_mem
    (fst_mem_labels_of_mem_rel (p := (x, y)) hxy)
    (snd_mem_labels_of_mem_rel (p := (y, z)) hyz)

/-- A labelled sequent is *saturated* when it is not closed by `axm`/`botL`/`Irref` and
it satisfies the Hintikka-style closure conditions for `impL`, `impR`, `Trans` and `L□`
(principal formulas are kept, so implications may still occur, but they are decomposed). -/
structure Saturated (S : LabelledSequent α) : Prop where
  not_axm : ∀ lf ∈ S.ant, lf ∉ S.suc
  not_bot : ∀ x : Label, (x ∶ (⊥ : Formula α)) ∉ S.ant
  not_irref : ∀ x : Label, (x, x) ∉ S.rel
  imp_ant : ∀ x A B, (x ∶ A 🡒 B) ∈ S.ant → (x ∶ A) ∈ S.suc ∨ (x ∶ B) ∈ S.ant
  imp_suc : ∀ x A B, (x ∶ A 🡒 B) ∈ S.suc → (x ∶ A) ∈ S.ant ∧ (x ∶ B) ∈ S.suc
  rel_trans : ∀ x y z, (x, y) ∈ S.rel → (y, z) ∈ S.rel → (x, z) ∈ S.rel
  box_ant : ∀ x y A, (x, y) ∈ S.rel → (x ∶ □A) ∈ S.ant → (y ∶ A) ∈ S.ant

end LabelledSequent


namespace ProofLabelledGentzen

variable {R : Finset (Label × Label)} {Γ Δ : Finset (LabelledFormula α)} {x : Label} {A B : Formula α}

/-- `impR` with the principal formula kept in the succedent. -/
def impR_mem (h : (x ∶ A 🡒 B) ∈ Δ)
  (p : ⊢ˡ! (R ⸴ insert (x ∶ A) Γ ⟹ˡ insert (x ∶ B) Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  rw [show Δ = insert (x ∶ A 🡒 B) Δ by grind];
  exact impR p;

/-- `impL` with the principal formula kept in the antecedent. -/
def impL_mem (h : (x ∶ A 🡒 B) ∈ Γ)
  (p : ⊢ˡ! (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (q : ⊢ˡ! (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  rw [show Γ = insert (x ∶ A 🡒 B) Γ by grind];
  exact impL p q;

end ProofLabelledGentzen


/-- The labelled sequent determined by list-representations of its components.
Used to keep the leaves of `saturate` computably enumerable (extracting elements
from a `Finset` is noncomputable). -/
abbrev LabelledSequent.ofLists
  (L : List (Label × Label) × List (LabelledFormula α) × List (LabelledFormula α)) : LabelledSequent α :=
  L.1.toFinset ⸴ L.2.1.toFinset ⟹ˡ L.2.2.toFinset

/-- The result of saturating a labelled sequent `S`: either a proof of `S`, or a
finite list of saturated open sequents (the leaves of the saturation tree, given by
list-representations of their components for computability) together with a way of
recovering a proof of `S` from proofs of all of them.  The leaves have the same
labels and the same subformula closure as `S`. -/
inductive SaturationResult (S : LabelledSequent α) : Type u
  | closed (π : ⊢ˡ! S) : SaturationResult S
  | stuck (leaves : List (List (Label × Label) × List (LabelledFormula α) × List (LabelledFormula α)))
      (hsat : ∀ L ∈ leaves, (LabelledSequent.ofLists L).Saturated)
      (hlab : ∀ L ∈ leaves, (LabelledSequent.ofLists L).labels = S.labels)
      (hsf : ∀ L ∈ leaves, (LabelledSequent.ofLists L).sf = S.sf)
      (k : (∀ L ∈ leaves, ⊢ˡ! (LabelledSequent.ofLists L)) → ⊢ˡ! S) : SaturationResult S

namespace SaturationResult

variable {S S' S₁ S₂ : LabelledSequent α}

/-- Transports a `SaturationResult` along a one-premise derivation step. -/
def map (f : ⊢ˡ! S → ⊢ˡ! S') (hlab : S.labels = S'.labels) (hsf : S.sf = S'.sf) :
  SaturationResult S → SaturationResult S'
  | closed π => closed (f π)
  | stuck leaves hsat hl hs k =>
      stuck leaves hsat
        (fun T hT => (hl T hT).trans hlab)
        (fun T hT => (hs T hT).trans hsf)
        (fun ps => f (k ps))

/-- Transports two `SaturationResult`s along a two-premise derivation step. -/
def map₂ (f : ⊢ˡ! S₁ → ⊢ˡ! S₂ → ⊢ˡ! S')
  (hlab₁ : S₁.labels = S'.labels) (hsf₁ : S₁.sf = S'.sf)
  (hlab₂ : S₂.labels = S'.labels) (hsf₂ : S₂.sf = S'.sf) :
  SaturationResult S₁ → SaturationResult S₂ → SaturationResult S'
  | closed π₁, closed π₂ => closed (f π₁ π₂)
  | closed π₁, stuck l₂ hsat₂ hl₂ hs₂ k₂ =>
      stuck l₂ hsat₂
        (fun T hT => (hl₂ T hT).trans hlab₂)
        (fun T hT => (hs₂ T hT).trans hsf₂)
        (fun ps => f π₁ (k₂ ps))
  | stuck l₁ hsat₁ hl₁ hs₁ k₁, closed π₂ =>
      stuck l₁ hsat₁
        (fun T hT => (hl₁ T hT).trans hlab₁)
        (fun T hT => (hs₁ T hT).trans hsf₁)
        (fun ps => f (k₁ ps) π₂)
  | stuck l₁ hsat₁ hl₁ hs₁ k₁, stuck l₂ hsat₂ hl₂ hs₂ k₂ =>
      stuck (l₁ ++ l₂)
        (fun T hT => (List.mem_append.mp hT).elim (hsat₁ T) (hsat₂ T))
        (fun T hT => (List.mem_append.mp hT).elim
          (fun h => (hl₁ T h).trans hlab₁) (fun h => (hl₂ T h).trans hlab₂))
        (fun T hT => (List.mem_append.mp hT).elim
          (fun h => (hs₁ T h).trans hsf₁) (fun h => (hs₂ T h).trans hsf₂))
        (fun ps => f
          (k₁ (fun T hT => ps T (List.mem_append_left _ hT)))
          (k₂ (fun T hT => ps T (List.mem_append_right _ hT))))

end SaturationResult


/-! ### Finders for applicable saturation steps -/

section finders

variable (R : List (Label × Label)) (Γ Δ : List (LabelledFormula α))

/-- Finds an implication in the succedent whose `impR`-decomposition is still missing. -/
def impRTarget? : Option (Label × Formula α × Formula α) :=
  Δ.findSome? fun lf =>
    match lf with
    | ⟨x, A 🡒 B⟩ => if (x ∶ A) ∈ Γ ∧ (x ∶ B) ∈ Δ then none else some (x, A, B)
    | _ => none

/-- Finds an implication in the antecedent whose `impL`-decomposition is still missing. -/
def impLTarget? : Option (Label × Formula α × Formula α) :=
  Γ.findSome? fun lf =>
    match lf with
    | ⟨x, A 🡒 B⟩ => if (x ∶ A) ∈ Δ ∨ (x ∶ B) ∈ Γ then none else some (x, A, B)
    | _ => none

/-- Finds a relational atom `(x, y)` and a boxed formula `x : □A` whose `L□`-instance `y : A`
is still missing. -/
def boxLTarget? : Option (Label × Label × Formula α) :=
  R.findSome? fun p =>
    Γ.findSome? fun lf =>
      match lf with
      | ⟨x, □A⟩ => if x = p.1 ∧ (p.2 ∶ A) ∉ Γ then some (p.1, p.2, A) else none
      | _ => none

/-- Finds relational atoms `(x, y)` and `(y, z)` whose transitive consequence `(x, z)`
is still missing. -/
def transTarget? : Option (Label × Label × Label) :=
  R.findSome? fun p =>
    R.findSome? fun q =>
      if q.1 = p.2 ∧ (p.1, q.2) ∉ R then some (p.1, p.2, q.2) else none

end finders

section finders

variable {R : List (Label × Label)} {Γ Δ : List (LabelledFormula α)} {x y z : Label} {A B : Formula α}

lemma impRTarget?_some (h : impRTarget? Γ Δ = some (x, A, B)) :
  (x ∶ A 🡒 B) ∈ Δ.toFinset ∧ ((x ∶ A) ∉ Γ.toFinset ∨ (x ∶ B) ∉ Δ.toFinset) := by
  obtain ⟨lf, hmem, hlf⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

lemma impRTarget?_none (h : impRTarget? Γ Δ = none) (hm : (x ∶ A 🡒 B) ∈ Δ.toFinset) :
  (x ∶ A) ∈ Γ.toFinset ∧ (x ∶ B) ∈ Δ.toFinset := by
  unfold impRTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have := h (x ∶ A 🡒 B) (List.mem_toFinset.mp hm);
  grind [List.mem_toFinset];

lemma impLTarget?_some (h : impLTarget? Γ Δ = some (x, A, B)) :
  (x ∶ A 🡒 B) ∈ Γ.toFinset ∧ (x ∶ A) ∉ Δ.toFinset ∧ (x ∶ B) ∉ Γ.toFinset := by
  obtain ⟨lf, hmem, hlf⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

lemma impLTarget?_none (h : impLTarget? Γ Δ = none) (hm : (x ∶ A 🡒 B) ∈ Γ.toFinset) :
  (x ∶ A) ∈ Δ.toFinset ∨ (x ∶ B) ∈ Γ.toFinset := by
  unfold impLTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have := h (x ∶ A 🡒 B) (List.mem_toFinset.mp hm);
  grind [List.mem_toFinset];

lemma boxLTarget?_some (h : boxLTarget? R Γ = some (x, y, A)) :
  (x, y) ∈ R.toFinset ∧ (x ∶ □A) ∈ Γ.toFinset ∧ (y ∶ A) ∉ Γ.toFinset := by
  obtain ⟨p, hp, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨lf, hlf, h2⟩ := List.exists_of_findSome?_eq_some h1;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

lemma boxLTarget?_none (h : boxLTarget? R Γ = none)
  (hR : (x, y) ∈ R.toFinset) (hm : (x ∶ □A) ∈ Γ.toFinset) : (y ∶ A) ∈ Γ.toFinset := by
  unfold boxLTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have h1 := h (x, y) (List.mem_toFinset.mp hR);
  rw [List.findSome?_eq_none_iff] at h1;
  have h2 := h1 (x ∶ □A) (List.mem_toFinset.mp hm);
  grind [List.mem_toFinset];

lemma transTarget?_some (h : transTarget? R = some (x, y, z)) :
  (x, y) ∈ R.toFinset ∧ (y, z) ∈ R.toFinset ∧ (x, z) ∉ R.toFinset := by
  obtain ⟨p, hp, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨q, hq, h2⟩ := List.exists_of_findSome?_eq_some h1;
  grind [List.mem_toFinset];

lemma transTarget?_none (h : transTarget? R = none)
  (hxy : (x, y) ∈ R.toFinset) (hyz : (y, z) ∈ R.toFinset) : (x, z) ∈ R.toFinset := by
  unfold transTarget? at h;
  rw [List.findSome?_eq_none_iff] at h;
  have h1 := h (x, y) (List.mem_toFinset.mp hxy);
  rw [List.findSome?_eq_none_iff] at h1;
  have h2 := h1 (y, z) (List.mem_toFinset.mp hyz);
  grind [List.mem_toFinset];

end finders


/-! ### The saturation procedure -/

/-- Saturates the labelled sequent `R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset`, exhaustively
applying `impL`/`impR`/`L□`/`Trans` (keeping principal formulas) until the sequent is
closed by `axm`/`botL`/`Irref` or saturated. -/
def saturate (R : List (Label × Label)) (Γ Δ : List (LabelledFormula α)) :
  SaturationResult (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset) :=
  match h₁ : Γ.find? (fun lf => decide (lf ∈ Δ)) with
  | some lf =>
    .closed <| ProofLabelledGentzen.union lf.label lf.formula
      (List.mem_toFinset.mpr (List.mem_of_find?_eq_some h₁))
      (by
        have h := List.find?_some h₁;
        simp only [decide_eq_true_eq] at h;
        exact List.mem_toFinset.mpr h)
  | none =>
  match h₂ : Γ.find? (fun lf : LabelledFormula α => decide (lf.formula = (⊥ : Formula α))) with
  | some lf =>
    .closed <| ProofLabelledGentzen.botL_mem lf.label
      (by
        have h := List.find?_some h₂;
        simp only [decide_eq_true_eq] at h;
        have hm : (lf.label ∶ lf.formula) ∈ Γ.toFinset :=
          List.mem_toFinset.mpr (List.mem_of_find?_eq_some h₂);
        rwa [h] at hm)
  | none =>
  match h₃ : R.find? (fun p => decide (p.1 = p.2)) with
  | some p =>
    .closed <| ProofLabelledGentzen.irref p.1
      (by
        have h := List.find?_some h₃;
        simp only [decide_eq_true_eq] at h;
        have hm : (p.1, p.2) ∈ R.toFinset := List.mem_toFinset.mpr (List.mem_of_find?_eq_some h₃);
        rwa [← h] at hm)
  | none =>
  match h₄ : impRTarget? Γ Δ with
  | some (x, A, B) =>
    (saturate R ((x ∶ A) :: Γ) ((x ∶ B) :: Δ)).map
      (fun π => ProofLabelledGentzen.impR_mem (impRTarget?_some h₄).1 (by simpa using π))
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_impR (impRTarget?_some h₄).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_impR (impRTarget?_some h₄).1)
  | none =>
  match h₅ : impLTarget? Γ Δ with
  | some (x, A, B) =>
    SaturationResult.map₂
      (fun π₁ π₂ => ProofLabelledGentzen.impL_mem (impLTarget?_some h₅).1
        (by simpa using π₁) (by simpa using π₂))
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_impL_left (impLTarget?_some h₅).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_impL_left (impLTarget?_some h₅).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_impL_right (impLTarget?_some h₅).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_impL_right (impLTarget?_some h₅).1)
      (saturate R Γ ((x ∶ A) :: Δ))
      (saturate R ((x ∶ B) :: Γ) Δ)
  | none =>
  match h₆ : boxLTarget? R Γ with
  | some (x, y, A) =>
    (saturate R ((y ∶ A) :: Γ) Δ).map
      (fun π => ProofLabelledGentzen.boxL x y A
        (boxLTarget?_some h₆).1 (boxLTarget?_some h₆).2.1 (by simpa using π))
      (by simp only [List.toFinset_cons]; exact LabelledSequent.labels_boxL (boxLTarget?_some h₆).1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_boxL (boxLTarget?_some h₆).2.1)
  | none =>
  match h₇ : transTarget? R with
  | some (x, y, z) =>
    (saturate ((x, z) :: R) Γ Δ).map
      (fun π => ProofLabelledGentzen.trans x y z
        (transTarget?_some h₇).1 (transTarget?_some h₇).2.1 (by simpa using π))
      (by
        simp only [List.toFinset_cons];
        exact LabelledSequent.labels_trans (transTarget?_some h₇).1 (transTarget?_some h₇).2.1)
      (by simp only [List.toFinset_cons]; exact LabelledSequent.sf_insert_rel)
  | none =>
    .stuck [(R, Γ, Δ)]
      (by
        intro T hT;
        rw [List.mem_singleton] at hT;
        subst hT;
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩;
        · have := List.find?_eq_none.mp h₁; grind [List.mem_toFinset];
        · have := List.find?_eq_none.mp h₂; grind [List.mem_toFinset];
        · have := List.find?_eq_none.mp h₃; grind [List.mem_toFinset];
        · exact fun x A B hm => impLTarget?_none h₅ hm;
        · exact fun x A B hm => impRTarget?_none h₄ hm;
        · exact fun x y z hxy hyz => transTarget?_none h₇ hxy hyz;
        · exact fun x y A hR hm => boxLTarget?_none h₆ hR hm)
      (by intro T hT; rw [List.mem_singleton] at hT; subst hT; rfl)
      (by intro T hT; rw [List.mem_singleton] at hT; subst hT; rfl)
      (fun ps => ps _ (List.mem_singleton_self _))
termination_by (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).saturationMeasure
decreasing_by
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_impR (impRTarget?_some h₄).1 (impRTarget?_some h₄).2;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_impL_left (impLTarget?_some h₅).1 (impLTarget?_some h₅).2.1;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_impL_right (impLTarget?_some h₅).1 (impLTarget?_some h₅).2.2;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_boxL
      (boxLTarget?_some h₆).1 (boxLTarget?_some h₆).2.1 (boxLTarget?_some h₆).2.2;
  · simp only [List.toFinset_cons];
    exact LabelledSequent.saturationMeasure_trans
      (transTarget?_some h₇).1 (transTarget?_some h₇).2.1 (transTarget?_some h₇).2.2;


/-! ### The outer proof search -/

section finders

variable (processed : Finset (Formula α)) (R : List (Label × Label)) (Γ Δ : List (LabelledFormula α))

/-- Finds a *looping* boxed formula (cf. `[Neg14]` Lemma 5.2): some `x ∶ □A` in the
succedent together with a predecessor `w` of `x` carrying `w ∶ □A` in the antecedent. -/
def loopTarget? : Option (Label × Label × Formula α) :=
  Δ.findSome? fun lf =>
    match lf with
    | ⟨x, □A⟩ => R.findSome? fun p =>
        if p.2 = x ∧ (p.1 ∶ □A) ∈ Γ then some (p.1, x, A) else none
    | _ => none

/-- Finds a boxed formula in the succedent not yet processed by `R□^Löb` on the current branch. -/
def lobTarget? : Option (Label × Formula α) :=
  Δ.findSome? fun lf =>
    match lf with
    | ⟨x, □A⟩ => if □A ∈ processed then none else some (x, A)
    | _ => none

end finders

section finders

variable {processed : Finset (Formula α)} {R : List (Label × Label)} {Γ Δ : List (LabelledFormula α)}
variable {w x : Label} {A : Formula α}

lemma loopTarget?_some (h : loopTarget? R Γ Δ = some (w, x, A)) :
  (w, x) ∈ R.toFinset ∧ (w ∶ □A) ∈ Γ.toFinset ∧ (x ∶ □A) ∈ Δ.toFinset := by
  obtain ⟨lf, hlf, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> try grind;
  case box B =>
    obtain ⟨p, hp, h2⟩ := List.exists_of_findSome?_eq_some h1;
    grind [List.mem_toFinset];

lemma lobTarget?_some (h : lobTarget? processed Δ = some (x, A)) :
  (x ∶ □A) ∈ Δ.toFinset ∧ □A ∉ processed := by
  obtain ⟨lf, hlf, h1⟩ := List.exists_of_findSome?_eq_some h;
  obtain ⟨x', F⟩ := lf;
  cases F <;> grind [List.mem_toFinset];

end finders


/-- Extends a family of values over the elements of a list by a value for a new head. -/
def consAllMem {β : Type v} [DecidableEq β] {f : β → Type w} {b : β} {l : List β}
  (p : f b) (ps : ∀ c ∈ l, f c) : ∀ c ∈ b :: l, f c :=
  fun c hc => if h : c = b then h ▸ p else ps c ((List.mem_cons.mp hc).resolve_left h)

mutual

/-- Proof search for `G3KGL`, following the termination argument of `[Neg14]`, Theorem 5.5:
saturate, then solve every stuck leaf (`searchLeaves`).  The parameter `processed` records
the boxed formulas already treated by `R□^Löb` on the current branch; since all formulas
occurring during the search are subformulas of the root sequent (`hsub`, preserved by
`saturate` and by the keep-principal `R□^Löb` step), the search terminates. -/
def search (processed : Finset (Formula α)) (R : List (Label × Label)) (Γ Δ : List (LabelledFormula α))
  (hsub : processed ⊆ (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).sf) :
  Option (⊢ˡ! (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset)) :=
  match saturate R Γ Δ with
  | .closed π => some π
  | .stuck leaves _ _ hsf k =>
    match searchLeaves processed ((R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset)).sf hsub leaves hsf with
    | some ps => some (k ps)
    | none => none
termination_by ((R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset).sf.card - processed.card, 1, 0)
decreasing_by
  apply Prod.Lex.right;
  exact Prod.Lex.left _ _ Nat.zero_lt_one;

/-- Solves every stuck leaf produced by `saturate`: a leaf is closed either by a looping
sequent (`[Neg14]` Lemma 5.2, via `ProofLabelledGentzen.loop`), or by applying `R□^Löb`
(keeping the principal formula) to a boxed succedent formula not yet in `processed` and
recursing with `search`. -/
def searchLeaves (processed : Finset (Formula α)) (X : FormulaFinset α) (hsub : processed ⊆ X)
  (leaves : List (List (Label × Label) × List (LabelledFormula α) × List (LabelledFormula α)))
  (hsf : ∀ L ∈ leaves, (LabelledSequent.ofLists L).sf = X) :
  Option (∀ L ∈ leaves, ⊢ˡ! (LabelledSequent.ofLists L)) :=
  match leaves, hsf with
  | [], _ => some (fun _ hL => nomatch hL)
  | ⟨Rl, Γl, Δl⟩ :: rest, hsf =>
    match h₁ : loopTarget? Rl Γl Δl with
    | some (w, x, A) =>
      match searchLeaves processed X hsub rest (fun L hL => hsf L (List.mem_cons_of_mem _ hL)) with
      | some ps =>
        some (consAllMem
          (ProofLabelledGentzen.loop w x (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).freshLabel A
            LabelledSequent.freshLabel_notMem
            (loopTarget?_some h₁).1 (loopTarget?_some h₁).2.1 (loopTarget?_some h₁).2.2)
          ps)
      | none => none
    | none =>
    match h₂ : lobTarget? processed Δl with
    | some (x, A) =>
      have hΔ : (x ∶ □A) ∈ Δl.toFinset := (lobTarget?_some h₂).1;
      have hnew : (□A) ∉ processed := (lobTarget?_some h₂).2;
      have hbox : (□A) ∈ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).sf :=
        LabelledSequent.mem_sf_of_mem_suc (lf := x ∶ □A) hΔ;
      have hsf₀ : (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).sf = X := hsf (Rl, Γl, Δl) (by simp);
      let y : Label := (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).freshLabel;
      have hA1 : (□A) ∈ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ insert (y ∶ A) Δl.toFinset).sf :=
        LabelledSequent.mem_sf_of_mem_suc (lf := x ∶ □A) (Finset.mem_insert_of_mem hΔ);
      have hA2 : A ∈ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).sf :=
        LabelledSequent.mem_sf_of_box hbox;
      have hprem :
        (((x, y) :: Rl).toFinset ⸴ ((y ∶ □A) :: Γl).toFinset ⟹ˡ ((y ∶ A) :: Δl).toFinset).sf = X := by
        simp only [List.toFinset_cons];
        rw [LabelledSequent.sf_insert_rel,
          LabelledSequent.sf_insert_ant_of_mem (lf := y ∶ □A) hA1,
          LabelledSequent.sf_insert_suc_of_mem (lf := y ∶ A) hA2];
        exact hsf₀;
      have hsub' : insert (□A) processed ⊆
        (((x, y) :: Rl).toFinset ⸴ ((y ∶ □A) :: Γl).toFinset ⟹ˡ ((y ∶ A) :: Δl).toFinset).sf := by
        rw [hprem];
        exact Finset.insert_subset_iff.mpr ⟨hsf₀ ▸ hbox, hsub⟩;
      have hlt :
        (((x, y) :: Rl).toFinset ⸴ ((y ∶ □A) :: Γl).toFinset ⟹ˡ ((y ∶ A) :: Δl).toFinset).sf.card
          - (insert (□A) processed).card < X.card - processed.card := by
        have h1 := Finset.card_insert_of_notMem hnew;
        have h2 := Finset.card_le_card (hprem ▸ hsub');
        rw [hprem];
        omega;
      match search (insert (□A) processed) ((x, y) :: Rl) ((y ∶ □A) :: Γl) ((y ∶ A) :: Δl) hsub' with
      | some π =>
        match searchLeaves processed X hsub rest (fun L hL => hsf L (List.mem_cons_of_mem _ hL)) with
        | some ps =>
          have hlab0 : x ∈ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset).labels :=
            LabelledSequent.mem_labels_of_mem_suc (lf := x ∶ □A) hΔ;
          have hfresh : y ∉ (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ insert (x ∶ □A) Δl.toFinset).labels := by
            rw [LabelledSequent.labels_insert_suc_of_mem (lf := x ∶ □A) hlab0];
            exact LabelledSequent.freshLabel_notMem;
          some (consAllMem
            (by
              show ⊢ˡ! (Rl.toFinset ⸴ Γl.toFinset ⟹ˡ Δl.toFinset);
              rw [show Δl.toFinset = insert (x ∶ □A) Δl.toFinset from (Finset.insert_eq_self.mpr hΔ).symm];
              exact ProofLabelledGentzen.boxRLob x y A hfresh (by simpa only [List.toFinset_cons] using π))
            ps)
        | none => none
      | none => none
    | none => none
termination_by (X.card - processed.card, 0, leaves.length)
decreasing_by
  · apply Prod.Lex.right;
    apply Prod.Lex.right;
    simp;
  · exact Prod.Lex.left _ _ hlt;
  · apply Prod.Lex.right;
    apply Prod.Lex.right;
    simp;

end

/-- Entry point of the proof search: no boxed formula has been processed yet. -/
def search0 (R : List (Label × Label)) (Γ Δ : List (LabelledFormula α)) :
  Option (⊢ˡ! (R.toFinset ⸴ Γ.toFinset ⟹ˡ Δ.toFinset)) :=
  search ∅ R Γ Δ (Finset.empty_subset _)

/-! Sanity checks: the Löb axiom `□(□a 🡒 a) 🡒 □a` and the `K` axiom are found
automatically; the `T` axiom `□a 🡒 a` and `□a` itself, which are not theorems of
`GL`, are rejected. -/

#guard (search0 (α := ℕ) [] [] [0 ∶ (□(□#0 🡒 #0) 🡒 □#0)]).isSome
#guard (search0 (α := ℕ) [] [] [0 ∶ (□(#0 🡒 #1) 🡒 □#0 🡒 □#1)]).isSome
#guard (search0 (α := ℕ) [] [] [0 ∶ (□#0 🡒 □□#0)]).isSome
#guard (search0 (α := ℕ) [] [] [0 ∶ (□#0 🡒 #0)]).isNone
#guard (search0 (α := ℕ) [] [] [0 ∶ (□#0)]).isNone

#eval match search0 (α := ℕ) [] [] [0 ∶ (□(□#0 🡒 #0) 🡒 □#0)] with
  | some p => ProofLabelledGentzen.toString p
  | none => "no proof found"

end
