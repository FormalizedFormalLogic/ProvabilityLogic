module

public import ProvabilityLogic.Kripke.RootedModel
public import ProvabilityLogic.Kripke.RootExtension
public import ProvabilityLogic.Kripke.Preservation

@[expose]
public section

open Classical

variable [Nonempty κ]


@[grind] def TBB (n : ℕ) : Formula α := (□^[(n + 1)]⊥) 🡒 (□^[n]⊥)


namespace Model

variable {M : Model κ α} [Fintype M.World] [M.IsGL] {x y : M.World} {n : ℕ}

noncomputable def World.rank {M : Model κ α} [Fintype M.World] [M.IsGL] (x : M.World) : ℕ := cwfHeight (· ≺ ·) x

@[grind ->]
lemma rank_lt_of_rel (hij : x ≺ y) : y.rank < x.rank:= cwfHeight_gt_of hij

@[grind =]
lemma iff_rank_lt {n : ℕ} {x : M.World} : x.rank < n ↔ ∀ y, ¬x ≺^[n] y := by
  match n with
  |     0 => simp_all
  | n + 1 =>
    suffices x.rank ≤ n ↔ ∀ y : M.World, x ≺ y → y.rank < n by
      calc
        _ ↔ x.rank ≤ n                   := Nat.lt_add_one_iff
        _ ↔ ∀ y, x ≺ y → y.rank < n      := this
        _ ↔ ∀ y, x ≺ y → ∀ k, ¬y ≺^[n] k := by grind [iff_rank_lt (n := n)];
        _ ↔ ∀ k j, x ≺ j → ¬j ≺^[n] k    := by grind;
        _ ↔ ∀ j, ¬x ≺^[n + 1] j          := by simp;
    constructor
    · intro h y Rxy;
      exact lt_of_lt_of_le (cwfHeight_gt_of Rxy) h;
    · exact cwfHeight_le;

lemma iff_le_rank : n ≤ x.rank ↔ ∃ y, x ≺^[n] y := calc
  _ ↔ ¬x.rank < n    := Iff.symm Nat.not_lt
  _ ↔ ∃ y, x ≺^[n] y := by simp [iff_rank_lt]

lemma iff_rank_eq : x.rank = n ↔ (∃ y, x ≺^[n] y) ∧ (∀ y, x ≺^[n] y → ∀ z, ¬y ≺ z) := calc
  _ ↔ x.rank < n + 1 ∧ n ≤ x.rank                       := by simpa [Nat.lt_succ_iff] using Nat.eq_iff_le_and_ge;
  _ ↔ (∀ y, ¬x ≺^[n + 1] y) ∧ (∃ y, x ≺^[n] y)          := by rw [iff_rank_lt, iff_le_rank];
  _ ↔ (∀ l y, x ≺^[n] y → ¬y ≺ l) ∧ (∃ y, x ≺^[n] y)    := by simp only [Model.relItr_succ']; grind;
  _ ↔ (∃ y, x ≺^[n] y) ∧ (∀ y, x ≺^[n] y → ∀ z, ¬y ≺ z) := by grind;

lemma iff_rank_eq_zero : x.rank = 0 ↔ ∀ y, ¬x ≺ y := by
  apply Iff.trans $ iff_rank_eq;
  constructor;
  . grind;
  . rintro h;
    constructor;
    . use x;
      grind;
    . grind;



lemma of_lt_rank (hn : n < x.rank) : ∃ y : M.World, x ≺ y ∧ y.rank = n := cwfHeight_lt hn

lemma exists_rank_terminal (x : M.World) : ∃ y, x ≺^[x.rank] y := iff_le_rank.mp (by simp)

lemma terminal_rel_terminal (h : x ≺^[x.rank] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices x.rank + 1 ≤ x.rank by omega;
  apply iff_le_rank.mpr;
  exact ⟨z, Model.relItr_succ'.mpr ⟨y, h, Ryz⟩⟩;

lemma not_rel_over_rank (h : x.rank < n) : ¬x ≺^[n] y := by
  by_contra Rxy;
  rw [show n = x.rank + (n - x.rank) by omega] at Rxy;
  obtain ⟨z, Rxz, Rzy⟩ : ∃ z, x ≺^[x.rank] z ∧ z ≺^[n - x.rank] y := Model.relItr_decomp Rxy;
  exact terminal_rel_terminal Rxz y $ Model.relItr_unwrap_trans_pos (by omega) Rzy;

@[grind =]
lemma iff_rank_lt_forces_boxItr_bot : x.rank < n ↔ x ⊩ (□^[n]⊥) := by grind;

omit [Fintype M.World] [M.IsGL] in
/-- Forcing of `□^[n]⊥` is monotone in `n`: a world with no outgoing chain of length
`n` has none of length `m ≥ n` either. -/
lemma World.forces_boxItr_bot_mono {n m : ℕ} (hnm : n ≤ m) (h : x ⊩ (□^[n]⊥)) :
  x ⊩ (□^[m]⊥) := by
  apply forces_boxItr.mpr;
  intro y hy;
  rw [show m = n + (m - n) by omega] at hy;
  obtain ⟨z, hz, -⟩ := Model.relItr_decomp hy;
  exact forces_boxItr.mp h z hz;

@[grind =>]
lemma pos_rank_of_forces_dia (h : x ⊩ ◇A) : 0 < x.rank := by grind;

lemma iff_forces_dia_top_pos_rank : (x ⊩ ◇⊤) ↔ 0 < x.rank := by
  constructor;
  . exact pos_rank_of_forces_dia;
  . intro h;
    apply Model.World.forces_dia.mpr;
    obtain ⟨y, Rxy⟩ := exists_rank_terminal x;
    use y;
    grind;

@[grind =>]
lemma lt_rank_of_forces_diaItr (h : x ⊩ ◇^[n + 1]A) : n < x.rank := by
  induction n generalizing A x with
  | zero => grind;
  | succ n ih =>
    replace h : x ⊩ ◇◇^[n + 1]A := by grind [Formula.diaItr_comp];
    obtain ⟨y, Rxy, hy⟩ := Model.World.forces_dia.mp h;
    have : n < y.rank := ih hy;
    have : y.rank < x.rank := rank_lt_of_rel Rxy;
    omega;

lemma iff_forces_diaItr_top_lt_rank : (x ⊩ ◇^[n + 1]⊤) ↔ n < x.rank := by
  constructor;
  . exact lt_rank_of_forces_diaItr;
  . intro h;
    apply Model.World.forces_diaItr.mpr;
    obtain ⟨y, Rxy⟩ := exists_rank_terminal x;
    use y;
    constructor;
    . exact Model.relItr_reduce_trans_pos (by omega) (by omega) (by omega) Rxy;
    . grind;

lemma iff_not_forces_diaItr_top_le_rank : (x ⊮ ◇^[n + 1]⊤) ↔ x.rank ≤ n := by
  grind [iff_forces_diaItr_top_lt_rank]

omit [Fintype M.World] [M.IsGL] in @[grind =] lemma World.forces_TBB : x ⊩ (TBB n) ↔ x ⊩ (◇^[n + 1]⊤) ∨ x ⊮ (◇^[n]⊤) := by grind
omit [Fintype M.World] [M.IsGL] in @[grind =] lemma World.not_forces_TBB : x ⊮ (TBB n) ↔ x ⊮ (◇^[n + 1]⊤) ∧ x ⊩ (◇^[n]⊤) := by grind

lemma iff_forces_TBB_zero_neq_rank : x ⊩ (TBB 0) ↔ x.rank ≠ 0 := by grind [iff_forces_diaItr_top_lt_rank];

lemma iff_not_forces_TBB_zero_eq_rank_zero : x ⊮ (TBB 0) ↔ x.rank = 0 := by grind [iff_forces_TBB_zero_neq_rank];

lemma iff_forces_TBB_pos_neq_rank : x ⊩ (TBB (n + 1)) ↔ x.rank ≠ (n + 1) := by
  apply Iff.trans World.forces_TBB;
  rw [iff_forces_diaItr_top_lt_rank, iff_not_forces_diaItr_top_le_rank];
  omega;

lemma iff_not_forces_TBB_pos_eq_rank : x ⊮ (TBB (n + 1)) ↔ x.rank = (n + 1) := by
  grind [iff_forces_TBB_pos_neq_rank];

@[grind =]
lemma iff_forces_TBB_neq_rank : x ⊩ (TBB n) ↔ x.rank ≠ n := by
  match n with
  | 0     => exact iff_forces_TBB_zero_neq_rank;
  | n + 1 => exact iff_forces_TBB_pos_neq_rank;

@[grind =]
lemma iff_not_forces_TBB_eq_rank : x ⊮ (TBB n) ↔ x.rank = n := by grind;

section FrameBisimulation

variable {κ₁ κ₂ : Type*} [Nonempty κ₁] [Nonempty κ₂] {α₁ α₂ : Type*}
  {M₁ : Model κ₁ α₁} {M₂ : Model κ₂ α₂} [Fintype M₁.World] [Fintype M₂.World] [M₁.IsGL] [M₂.IsGL]
  {x₁ : M₁.World} {x₂ : M₂.World}

lemma rank_le_of_frameBisimilar (Bi : M₁ ⇄ᶠ M₂) (bisx : Bi x₁ x₂) : x₁.rank ≤ x₂.rank := by
  obtain ⟨y₁, Rx₁y₁⟩ := exists_rank_terminal x₁;
  obtain ⟨y₂, -, Rx₂y₂⟩ := Bi.forth_iterate bisx Rx₁y₁;
  exact iff_le_rank.mpr ⟨y₂, Rx₂y₂⟩;

lemma rank_eq_of_frameBisimilar (Bi : M₁ ⇄ᶠ M₂) (bisx : Bi x₁ x₂) : x₁.rank = x₂.rank :=
  le_antisymm (rank_le_of_frameBisimilar Bi bisx) (rank_le_of_frameBisimilar Bi.symm bisx)

end FrameBisimulation


section FramePseudoEpimorphism

variable {κ₁ κ₂ : Type*} [Nonempty κ₁] [Nonempty κ₂] {α₁ α₂ : Type*}
  {M₁ : Model κ₁ α₁} {M₂ : Model κ₂ α₂} [Fintype M₁.World] [Fintype M₂.World] [M₁.IsGL] [M₂.IsGL]

lemma FramePseudoEpimorphism.rank_eq (f : M₁ →ᶠ M₂) (w : M₁.World) : (f w).rank = w.rank :=
  (rank_eq_of_frameBisimilar f.bisimulation rfl).symm

end FramePseudoEpimorphism

end Model


namespace RootedModel

open Model

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL] {x y : M.World} {k : ℕ}

noncomputable def height (M : RootedModel κ α) [Fintype M.World] [M.IsGL] : ℕ := M.root.1.rank

@[grind <=]
lemma rank_lt_height (Rrx : M.root.1 ≺ x) : x.rank < M.height := cwfHeight_gt_of Rrx

@[grind .]
lemma rank_le_height : x.rank ≤ M.height := by
  by_cases exi : x = M.root.1
  · subst exi; rfl;
  · apply le_of_lt;
    apply rank_lt_height;
    grind;

@[grind =]
lemma iff_eq_rank_height_is_root : x.rank = M.height ↔ x = M.root.1 := by
  constructor;
  . contrapose!;
    intro h;
    apply Nat.ne_of_lt;
    apply rank_lt_height;
    grind;
  . tauto;

lemma root_not_forces_TBB_height : M.root.1 ⊮ (TBB M.height) := by grind;

@[grind =]
lemma iff_height_lt_root_forces_boxItr_bot : M.height < n ↔ M.root.1 ⊩ (□^[n]⊥) := iff_rank_lt_forces_boxItr_bot

namespace extendRoot

open RootedModel.extendRoot (embed)

variable {n : ℕ+}

@[simp, grind .]
lemma eq_extendRoot_height_extendRoot_root_rank : (M.extendRoot n).height = (M.extendRoot n).root.1.rank := by
  dsimp [height]

@[simp, grind .]
lemma height_pos : 0 < (M.extendRoot n).height := lt_cwfHeight (b := embed M.root.1) (by grind [embed]) (by omega)

namespace Ext1

@[simp, grind .]
lemma eq_height_original_height_succ : (M.extendRoot 1).height = M.height + 1 := by
  let h := (M.extendRoot 1).height;
  let r := (M.extendRoot 1).root;

  suffices h ≤ M.height + 1 ∧ M.height < h by omega;
  constructor
  · suffices h - 1 ≤ M.height from Nat.le_add_of_sub_le this;
    apply iff_le_rank.mpr;
    wlog lpos : 0 < h - 1;
    . use M.root.1;
      grind;

    obtain ⟨x, Rrx⟩ : ∃ y, r.1 ≺^[h] y := exists_rank_terminal r.1;
    obtain ⟨x₀, rfl⟩ : ∃ x₀, x = embed x₀ := Ext1.eq_original_of_rel_extendRoot_root $ Model.relItr_unwrap_trans_pos height_pos Rrx;
    obtain ⟨y, Rry, Ryx₀⟩ := (show h = (h - 1) + 1 by omega) ▸ Rrx;

    use x₀;
    by_cases y = embed M.root.1;
    . grind;
    . obtain ⟨y₀, rfl⟩ := Ext1.eq_original_of_rel_extendRoot_root Rry;
      replace Ryx₀ := relItr_embed_embed_iff_relItr.mp Ryx₀;
      have Rr₀y₀ : M.root.1 ≺^[1] y₀ := Model.relItr_one.mpr (by grind);
      have Ry₀x₀ : y₀ ≺^[h - 1] x₀ := by grind;
      have Rr₀x₀ := Model.relItr_comp Rr₀y₀ Ry₀x₀;
      exact Model.relItr_reduce_trans_pos (by grind) (by grind) (by omega) Rr₀x₀;

  · suffices M.height + 1 ≤ r.1.rank from this;
    apply iff_le_rank.mpr;
    rcases exists_rank_terminal M.root.1 with ⟨y, hy⟩;
    use ↑y, ↑M.root.1;
    constructor;
    . grind [embed];
    . grind;

@[simp, grind .]
lemma eq_embed_original_rank_original_rank {x₀ : M.World} : (embed (n := 1) x₀).rank = x₀.rank := by
  apply iff_rank_eq.mpr;
  constructor;
  . obtain ⟨y₀, Rxy⟩ := exists_rank_terminal x₀;
    use y₀;
    apply relItr_embed_embed_iff_relItr.mpr;
    exact Rxy;
  . rintro (y₀ | _) Rx₀y₀ (z₀ | _);
    . by_contra Ry₀z₀;
      have Rx₀z₀ := relItr_embed_embed_iff_relItr.mp $ Model.relItr_comp Rx₀y₀ $ Model.relItr_one.mpr Ry₀z₀;
      exact not_rel_over_rank (by grind) Rx₀z₀;
    . simp_all [Model.Rel];
    . exfalso;
      exact not_relItr_original_tail Rx₀y₀;
    . simp_all [Model.Rel];

@[simp, grind .]
lemma eq_original_root_rank_original_height : Model.World.rank (M := M.extendRoot 1 |>.toModel) (x := M.root) = M.height := eq_embed_original_rank_original_rank

end Ext1

end extendRoot

end RootedModel

end
