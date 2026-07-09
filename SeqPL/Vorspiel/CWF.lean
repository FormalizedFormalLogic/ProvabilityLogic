/-
  Original proof by: @iehality
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Rel
public import Mathlib.Data.Fintype.Card

@[expose]
public section


section

abbrev ConverseWellFounded {α} (r : Rel α α) := WellFounded $ flip r

class IsConverseWellFounded (α) (r : Rel α α) : Prop where cwf : ConverseWellFounded r

end



section

variable {α} {r : Rel α α} {a b : α} {n : ℕ}

instance [Std.Irrefl (flip r)] : Std.Irrefl r := by
  constructor;
  have := Std.Irrefl.irrefl (r := flip r);
  simpa;

lemma ConverseWellFounded.irrefl [IsConverseWellFounded α r] : Std.Irrefl r := by
  have := WellFounded.irrefl (r := flip r) IsConverseWellFounded.cwf;
  infer_instance;

lemma ConverseWellFounded.iff_has_max : ConverseWellFounded r ↔ (∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x)) := by
  simp [ConverseWellFounded, WellFounded.wellFounded_iff_has_min, flip]

lemma ConverseWellFounded.has_max (h : ConverseWellFounded r) : ∀ (s : Set α), Set.Nonempty s → ∃ m ∈ s, ∀ x ∈ s, ¬(r m x) := by
  apply ConverseWellFounded.iff_has_max.mp h;



theorem Finite.converseWellFounded_of_trans_of_irrefl [Finite α] [IsTrans α r] [Std.Irrefl r] : ConverseWellFounded r := by
  apply @Finite.wellFounded_of_trans_of_irrefl α _ (flip r)
    ⟨by intro a b c rba rcb; exact IsTrans.trans c b a rcb rba⟩
    ⟨by simp [flip, Std.Irrefl.irrefl]⟩


section cwfHeight

open Classical

noncomputable def cwfHeight (r) [IsConverseWellFounded α r] [Fintype α] : α → ℕ :=
  WellFounded.fix (r := flip r) (C := fun _ ↦ ℕ) IsConverseWellFounded.cwf fun x ih ↦
    Finset.univ.sup fun y : {y : α // r x y} ↦ ih y y.prop + 1

variable {r : Rel α α}

variable [Fintype α] [IsConverseWellFounded α r]

lemma cwfHeight_eq (a : α) :
  cwfHeight r a = Finset.sup {x : α | r a x} (fun b ↦ cwfHeight r b + 1) := by
  have h : cwfHeight r a = Finset.univ.sup fun b : {y : α // r a y} ↦ cwfHeight r b + 1 :=
    WellFounded.fix_eq _ _ a
  suffices
    Finset.univ.sup (fun b : {y : α // r a y} ↦ cwfHeight r b + 1) =
    Finset.sup {y : α | r a y} fun b ↦ cwfHeight r b + 1 from h.trans this
  apply eq_of_le_of_ge
  · apply Finset.sup_le
    intro b _
    exact Finset.le_sup (f := fun b ↦ cwfHeight r b + 1) (by simp [b.prop])
  · apply Finset.sup_le
    intro b hb
    simpa using Finset.le_sup (f := fun b : {y : α // r a y} ↦ cwfHeight r b + 1)
      (b := ⟨b, by simpa using hb⟩) (s := Finset.univ) (by simp)

lemma cwfHeight_gt_of : r a b → cwfHeight r a > cwfHeight r b := fun h ↦ calc
  cwfHeight r a = Finset.sup {x : α | r a x} fun b ↦ cwfHeight r b + 1 := cwfHeight_eq a
  _               ≥ cwfHeight r b + 1 := Finset.le_sup (f := fun b ↦ cwfHeight r b + 1) (by simp [h])

lemma cwfHeight_eq_zero_iff : cwfHeight r a = 0 ↔ ∀ b, ¬r a b := by
  constructor
  · intro h b hb
    have : cwfHeight r a > cwfHeight r b := cwfHeight_gt_of hb
    exact Nat.not_succ_le_zero (cwfHeight r b) (h ▸ this)
  · intro ha
    apply Nat.eq_zero_of_le_zero
    calc
      cwfHeight r a = Finset.sup {x : α | r a x} fun b ↦ cwfHeight r b + 1 := cwfHeight_eq a
      _               ≤ 0 := Finset.sup_le fun b hb ↦ False.elim <| ha b (by simpa using hb)

lemma cwfHeight_le (h : ∀ b, r a b → cwfHeight r b < n) : cwfHeight r a ≤ n := by
  rw [cwfHeight_eq]
  apply Finset.sup_le
  intro b hab
  exact h b (by simpa using hab)

lemma lt_cwfHeight (hb : r a b) (h : n ≤ cwfHeight r b) : n < cwfHeight r a := by
  have : cwfHeight r b < cwfHeight r a := by
    apply Nat.lt_of_succ_le
    rw [cwfHeight_eq a]
    exact Finset.le_sup (s := {x : α | r a x})
      (f := fun b ↦ cwfHeight r b + 1) (b := b) (by simp [hb])
  exact lt_of_le_of_lt h this

lemma cwfHeight_eq_of_lt_of_le
  (hr : ∀ b, r a b → cwfHeight r b < n) (h : ∃ b, r a b ∧ n ≤ cwfHeight r b + 1)
  : cwfHeight r a = n := by
  suffices cwfHeight r a ≤ n ∧ cwfHeight r a ≥ n from Nat.eq_iff_le_and_ge.mpr this
  constructor
  · exact cwfHeight_le hr
  · rcases h with ⟨b, hb, hn⟩
    suffices n - 1 < cwfHeight r a from Nat.le_of_pred_lt this
    apply lt_cwfHeight hb
    exact Nat.sub_le_of_le_add hn

lemma cwfHeight_eq_succ (h : cwfHeight r a ≠ 0)
  : ∃ b, r a b ∧ cwfHeight r a = cwfHeight r b + 1 := by
  have : ∃ b, r a b := by
    by_contra A
    have : cwfHeight r a = 0 := cwfHeight_eq_zero_iff.mpr <| by simpa using A
    simp_all
  have : ({x : α | r a x} : Finset α).Nonempty := by simpa [Finset.filter_nonempty_iff] using this
  simpa [cwfHeight_eq (r := r) a] using Finset.exists_mem_eq_sup _ this (fun b ↦ cwfHeight r b + 1)

lemma cwfHeight_eq_succ_cwfHeight (h : r a b) (hb : ∀ c, r a c → r b c ∨ b = c)
  : cwfHeight r a = cwfHeight r b + 1 := by
  apply cwfHeight_eq_of_lt_of_le
  · intro c Rac
    rcases hb c Rac with (Rbc | rfl)
    · suffices cwfHeight r c < cwfHeight r b from Nat.lt_add_right 1 this
      exact cwfHeight_gt_of Rbc
    · simp
  · use b

lemma cwfHeight_lt [IsTrans α r] : ∀ {n}, n < cwfHeight r a → ∃ b, r a b ∧ cwfHeight r b = n := by
  apply WellFounded.induction (r := flip r) IsConverseWellFounded.cwf a
  intro a ih
  rcases ha : cwfHeight r a with (_ | n)
  · simp
  · intro k hk
    have : ∃ b, r a b ∧ cwfHeight r b = n := by
      rcases cwfHeight_eq_succ (r := r) (a := a) (by simp [ha]) with ⟨b, hb, e⟩
      exact ⟨b, hb, by grind⟩
    rcases this with ⟨b, hb, rfl⟩
    have : k = cwfHeight r b ∨ k < cwfHeight r b := Nat.eq_or_lt_of_le <| Nat.le_of_lt_succ hk
    rcases this with (rfl | hk)
    · exact ⟨b, hb, rfl⟩
    · have : ∃ c, r b c ∧ cwfHeight r c = k := ih b hb hk
      rcases this with ⟨c, hc, rfl⟩
      exact ⟨c, IsTrans.trans _ _ _ hb hc, rfl⟩

/-- `cwfHeight` is invariant under an equivalence of relations: if `f : α ≃ β` carries `r`
to `r'`, then the heights of corresponding points agree. -/
lemma cwfHeight_congr {β} [Fintype β] {r' : Rel β β} [IsConverseWellFounded β r']
  (f : α ≃ β) (hf : ∀ a b, r a b ↔ r' (f a) (f b)) (a : α) :
  cwfHeight r a = cwfHeight r' (f a) := by
  apply WellFounded.induction (r := flip r) IsConverseWellFounded.cwf a;
  intro a ih;
  apply le_antisymm;
  · apply cwfHeight_le;
    intro b hab;
    rw [ih b hab];
    exact cwfHeight_gt_of ((hf a b).mp hab);
  · apply cwfHeight_le;
    intro b' hab';
    obtain ⟨b, rfl⟩ := f.surjective b';
    have hab : r a b := (hf a b).mpr hab';
    rw [← ih b hab];
    exact cwfHeight_gt_of hab;

end cwfHeight

end

end
