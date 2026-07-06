module

public import SeqPL.Gentzen.Basic
public import SeqPL.LabelledGentzen.Basic
public import SeqPL.Kripke.Gentzen
public import SeqPL.Kripke.LabelledGentzen

@[expose]
public section

/-!
Syntactic embedding of the label-free Gentzen calculus (`ProofGentzen`/`⊢ᵍ`) into
Negri's labelled sequent calculus (`ProofLabelledGentzen`/`⊢ˡ`).

The embedding is by structural recursion on `ProofGentzen`, via the
generalized statement `ProofGentzen.toLabelledGentzenAux`: each antecedent
formula `B` of the label-free sequent is represented in the labelled
antecedent either directly as `z ∶ B`, or (for `B = □C`) as `x ∶ □C` at some
`R`-predecessor `x` of `z`.  The latter representation is what makes the
`boxGL` case go through: after `R□^Löb` introduces a fresh label `y`, the
boxed context `Γ.box` stays at `z`, and is transferred to `y` on demand by
`Trans` (`transMany`) and `L□` (`boxLMany`), while a boxed formula meeting
its succedent copy across a relational atom is closed by `loop`.
-/

open LabelledGentzen

variable {α : Type u} [DecidableEq α]

/-- Translation of a label-free sequent into a labelled sequent: every formula
is labelled with `z`, and the relational context is empty. -/
def Sequent.toLabelled (z : Label) (S : Sequent α) : LabelledSequent α :=
  ∅ ⸴ S.ant.image (z ∶ ·) ⟹ˡ S.suc.image (z ∶ ·)


namespace LabelledGentzen

variable {R : Finset (Label × Label)} {Γ Δ Θ : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

namespace ProofLabelledGentzen

/-- Iterated `Trans` (`List` version): relational atoms `(x, y)` for all `x ∈ l`
may be assumed, provided `(z, y) ∈ R` and `(x, z) ∈ R` for each `x ∈ l`. -/
def transManyList (l : List Label) (hzy : (z, y) ∈ R) (hl : ∀ x ∈ l, (x, z) ∈ R)
  (π : ⊢ˡ! ((R ∪ (l.map (·, y)).toFinset) ⸴ Γ ⟹ˡ Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  induction l generalizing R with
  | nil => simpa using π;
  | cons x l ih =>
    apply trans x z y (hl x (by simp)) hzy;
    apply ih (by grind) (by grind);
    exact wkRel π (by intro p hp; simp at hp ⊢; grind);

/-- Iterated `Trans`: relational atoms `(x, y)` for all `x ∈ T` may be assumed,
provided `(z, y) ∈ R` and `(x, z) ∈ R` for each `x ∈ T`. -/
noncomputable def transMany (T : Finset Label) (hzy : (z, y) ∈ R) (hT : ∀ x ∈ T, (x, z) ∈ R)
  (π : ⊢ˡ! ((R ∪ T.image (·, y)) ⸴ Γ ⟹ˡ Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  apply transManyList T.toList hzy (by simpa using hT);
  rw [(show (T.toList.map (·, y)).toFinset = T.image (·, y) by ext p; simp)];
  exact π;

/-- Iterated `L□` (`List` version): labelled formulas `y ∶ B` for all `(x, B) ∈ l`
may be assumed, provided `(x, y) ∈ R` and `x ∶ □B ∈ Γ` for each `(x, B) ∈ l`. -/
def boxLManyList (l : List (Label × Formula α)) (hl : ∀ p ∈ l, (p.1, y) ∈ R ∧ (p.1 ∶ □p.2) ∈ Γ)
  (π : ⊢ˡ! (R ⸴ (Γ ∪ (l.map (fun p => y ∶ p.2)).toFinset) ⟹ˡ Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  induction l generalizing Γ with
  | nil => simpa using π;
  | cons p l ih =>
    apply boxL p.1 y p.2 (hl p (by simp)).1 (hl p (by simp)).2;
    apply ih (by grind);
    exact wkAnt π (by intro f hf; simp at hf ⊢; grind);

/-- Iterated `L□`: labelled formulas `y ∶ B` for all `(x, B) ∈ T` may be assumed,
provided `(x, y) ∈ R` and `x ∶ □B ∈ Γ` for each `(x, B) ∈ T`. -/
noncomputable def boxLMany (T : Finset (Label × Formula α)) (hT : ∀ p ∈ T, (p.1, y) ∈ R ∧ (p.1 ∶ □p.2) ∈ Γ)
  (π : ⊢ˡ! (R ⸴ (Γ ∪ T.image (fun p => y ∶ p.2)) ⟹ˡ Δ)) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  apply boxLManyList (y := y) T.toList (by simpa using hT);
  rw [(show (T.toList.map (fun p => y ∶ p.2)).toFinset = T.image (fun p => y ∶ p.2) by
    ext f; simp)];
  exact π;

end ProofLabelledGentzen

/-- The boxed formula of `f` that can be unfolded at `y`: `some (x, B)` when
`f = x ∶ □B` with `(x, y) ∈ R`, and `none` otherwise. -/
def LabelledFormula.boxTarget (y : Label) (R : Finset (Label × Label)) :
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

/-- All pairs `(x, B)` with `x ∶ □B ∈ Θ` and `(x, y) ∈ R`: the boxed formulas of `Θ`
that can be unfolded at `y` by `L□`. -/
def boxTargets (y : Label) (R : Finset (Label × Label)) (Θ : Finset (LabelledFormula α)) :
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

end LabelledGentzen


namespace ProofGentzen

-- Proved by structural recursion on the proof.
set_option maxHeartbeats 1000000 in
/--
  Generalized embedding statement: if `S` has a `ProofGentzen` and every antecedent
  formula `B` of `S` is represented in `Θ` either as `z ∶ B`, or (for `B = □C`)
  as `x ∶ □C` at some `R`-predecessor `x` of `z`, then the labelled sequent
  `R ⸴ Θ ⟹ˡ S.suc.image (z ∶ ·)` has a `ProofLabelledGentzen`.
-/
noncomputable def toLabelledGentzenAux {S : Sequent α} :
  ⊢ᵍ! S → (z : Label) → (R : Finset (Label × Label)) → (Θ : Finset (LabelledFormula α)) →
  (∀ B ∈ S.ant, (z ∶ B) ∈ Θ ∨ ∃ x C, B = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ) →
  ⊢ˡ! (R ⸴ Θ ⟹ˡ S.suc.image (z ∶ ·))
  | .axm A, z, R, Θ, H => by
    simp only [Finset.image_singleton];
    if hzA : (z ∶ A) ∈ Θ then
      exact ProofLabelledGentzen.union z A hzA (by simp);
    else
      have hA : ∃ x C, A = □C ∧ (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ := (H A (by simp)).resolve_left hzA;
      clear hzA H;
      cases A with
      | box C =>
        have hex : ∃ x : Label, (x, z) ∈ R ∧ (x ∶ □C) ∈ Θ := by grind;
        exact ProofLabelledGentzen.loop (Nat.find hex) z ((R ⸴ Θ ⟹ˡ {z ∶ □C}).freshLabel) C
          LabelledSequent.freshLabel_notMem (Nat.find_spec hex).1 (Nat.find_spec hex).2 (by simp);
      | atom a => simp at hA;
      | bot => simp at hA;
      | imp B C => simp at hA;
  | .botL, z, R, Θ, H => by
    have hz : (z ∶ (⊥ : Formula α)) ∈ Θ := by have := H ⊥ (by simp); grind;
    exact ProofLabelledGentzen.botL_mem z hz;
  | .wkL π h, z, R, Θ, H => toLabelledGentzenAux π z R Θ (fun B hB => H B (h hB))
  | .wkR π h, z, R, Θ, H =>
    ProofLabelledGentzen.wkSuc (toLabelledGentzenAux π z R Θ H) (Finset.image_subset_image h)
  | .impL (A := A) (B := B) π₁ π₂, z, R, Θ, H => by
    have hAB : (z ∶ A 🡒 B) ∈ Θ := by have := H (A 🡒 B) (by simp); grind;
    have h₁ := toLabelledGentzenAux π₁ z R Θ (fun C hC => H C (Finset.mem_insert_of_mem hC));
    have h₂ := toLabelledGentzenAux π₂ z R (insert (z ∶ B) Θ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C (Finset.mem_insert_of_mem hC); grind;
    );
    rw [(show Θ = insert (z ∶ A 🡒 B) Θ by grind)];
    simp only [Finset.image_insert] at h₁;
    exact ProofLabelledGentzen.impL h₁ h₂;
  | .impR (A := A) (B := B) π, z, R, Θ, H => by
    have h := toLabelledGentzenAux π z R (insert (z ∶ A) Θ) (fun C hC => by
      rcases Finset.mem_insert.mp hC with rfl | hC;
      . exact Or.inl (by simp);
      . have := H C hC; grind;
    );
    simp only [Finset.image_insert] at h ⊢;
    exact ProofLabelledGentzen.impR h;
  | .boxGL (Γ := Γ) (A := A) π, z, R, Θ, H => by
    simp only [Finset.image_singleton];
    rw [← insert_empty_eq];
    apply ProofLabelledGentzen.boxRLob z ((R ⸴ Θ ⟹ˡ insert (z ∶ □A) ∅).freshLabel) A
      LabelledSequent.freshLabel_notMem;
    generalize (R ⸴ Θ ⟹ˡ insert (z ∶ □A) ∅).freshLabel = y;
    -- transfer the relational atoms `(x, z) ∈ R` to `(x, y)` by `Trans`
    apply ProofLabelledGentzen.transMany (z := z) (y := y)
      (T := (R.filter (fun p => p.2 = z)).image Prod.fst)
      (by grind) (by intro x hx; simp at hx; grind);
    set R' := insert (z, y) R ∪ ((R.filter (fun p => p.2 = z)).image Prod.fst).image (·, y)
      with hR';
    -- unfold every available boxed formula at `y` by `L□`
    apply ProofLabelledGentzen.boxLMany (y := y) (T := boxTargets y R' (insert (y ∶ □A) Θ))
      (by rintro ⟨x, B⟩ hp; exact mem_boxTargets.mp hp);
    have hzy : (z, y) ∈ R' := by grind;
    have hsat : ∀ x, (x, z) ∈ R → (x, y) ∈ R' := by
      intro x hxz;
      apply Finset.mem_union_right;
      have h₁ : (x, z) ∈ R.filter (fun p => p.2 = z) := Finset.mem_filter.mpr ⟨hxz, rfl⟩;
      have h₂ : x ∈ (R.filter (fun p => p.2 = z)).image Prod.fst := Finset.mem_image_of_mem _ h₁;
      exact Finset.mem_image_of_mem _ h₂;
    have h := toLabelledGentzenAux π y R'
      (insert (y ∶ □A) Θ ∪ (boxTargets y R' (insert (y ∶ □A) Θ)).image (fun p => y ∶ p.2))
      (fun E hE => by
        rcases Finset.mem_insert.mp hE with rfl | hE;
        . exact Or.inl (by grind);
        . rcases Finset.mem_union.mp hE with hEΓ | hEbox;
          . -- `E ∈ Γ` is unfolded at `y` by `boxLMany`
            left;
            apply Finset.mem_union_right;
            rcases H (□E) (Finset.mem_image_of_mem _ hEΓ) with hzE | ⟨x, C, hEC, hxz, hxC⟩;
            . exact Finset.mem_image_of_mem _ (mem_boxTargets.mpr ⟨hzy, by grind⟩);
            . obtain rfl : E = C := by grind;
              exact Finset.mem_image_of_mem _ (mem_boxTargets.mpr ⟨hsat x hxz, by grind⟩);
          . -- `□B ∈ Γ.box` stays represented at its old label
            obtain ⟨B, hBΓ, rfl⟩ := Finset.mem_image.mp hEbox;
            right;
            rcases H (□B) hEbox with hzB | ⟨x, C, hBC, hxz, hxC⟩;
            . exact ⟨z, B, rfl, hzy, by grind⟩;
            . obtain rfl : B = C := by grind;
              exact ⟨x, B, rfl, hsat x hxz, by grind⟩;
      );
    simp only [Finset.image_singleton] at h;
    rw [insert_empty_eq];
    exact h;

/-- Embedding of `ProofGentzen` into `ProofLabelledGentzen`: a proof of `S` yields a proof of
`S.toLabelled z` for any label `z`. -/
noncomputable def toLabelledGentzen (z : Label) {S : Sequent α} (π : ⊢ᵍ! S) : ⊢ˡ! (S.toLabelled z) :=
  toLabelledGentzenAux π z ∅ (S.ant.image (z ∶ ·)) (fun _ hB => Or.inl (Finset.mem_image_of_mem _ hB))

end ProofGentzen


/-- Embedding of `ProvableGentzen` into `ProvableLabelledGentzen`. -/
theorem ProvableGentzen.toLabelled (z : Label) {S : Sequent α} (h : ⊢ᵍ S) : ⊢ˡ (S.toLabelled z) :=
  ⟨h.some.toLabelledGentzen z⟩


/-- Converse embedding, via Kripke semantics: soundness of `ProvableLabelledGentzen`
on `GL` models (`LabelledGentzen.ProvableLabelledGentzen.Kripke.soundness_formula`)
specialized to finite `GL` models, composed with completeness of `ProvableGentzen`
for finite `GL` models (`ProvableGentzen.Kripke.completeness`). -/
theorem ProvableLabelledGentzen.toGentzen {x : Label} {A : Formula α}
  (h : ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {x ∶ A})) : ⊢ᵍ (∅ ⟹ {A}) := by
  apply ProvableGentzen.Kripke.completeness;
  intro κ _ M _ w;
  exact Model.World.forces_singleton_sequent.mpr
    (LabelledGentzen.ProvableLabelledGentzen.Kripke.soundness_formula h M w);

/-- `ProvableGentzen` and `ProvableLabelledGentzen` agree, for a formula `A` at any label `x`. -/
theorem iff_provableGentzen_provableLabelledGentzen {x : Label} {A : Formula α} :
  ⊢ᵍ (∅ ⟹ {A}) ↔ ⊢ˡ (∅ ⸴ ∅ ⟹ˡ {x ∶ A}) := by
  constructor;
  . intro h;
    simpa [Sequent.toLabelled] using ProvableGentzen.toLabelled x h;
  . exact ProvableLabelledGentzen.toGentzen;

end
