module

public import SeqPL.Kripke.Basic
public import SeqPL.Kripke.RootExtension

@[expose]
public section

open Classical

variable [Nonempty κ]


namespace Model

variable {M : Model κ α} [Fintype M.World] [M.IsGL] {i j : M.World}

noncomputable def World.rank {M : Model κ α} [Fintype M.World] [M.IsGL] (x : M.World) : ℕ := cwfHeight (· ≺ ·) x

@[grind ->]
lemma rank_lt_of_rel (hij : i ≺ j) : i.rank > j.rank := cwfHeight_gt_of hij

end Model


namespace RootedModel

variable {M : RootedModel κ α} [Fintype M.World] [M.IsGL] {x y : M.World} {k : ℕ}

noncomputable def height (M : RootedModel κ α) [Fintype M.World] [M.IsGL] : ℕ := M.root.1.rank

lemma exists_of_lt_height (hn : k < x.rank) : ∃ y : M.World, x ≺ y ∧ y.rank = k := cwfHeight_lt hn

lemma height_lt_iff_relItr {n : ℕ} {x : M.World} : x.rank < n ↔ ∀ y, ¬x ≺^[n] y := by
  match n with
  |     0 => simp_all
  | n + 1 =>
    suffices x.rank ≤ n ↔ ∀ y : M.World, x ≺ y → y.rank < n by
      calc
        _ ↔ x.rank ≤ n                   := Nat.lt_add_one_iff
        _ ↔ ∀ y, x ≺ y → y.rank < n      := this
        _ ↔ ∀ y, x ≺ y → ∀ k, ¬y ≺^[n] k := by grind [height_lt_iff_relItr (n := n)];
        _ ↔ ∀ k j, x ≺ j → ¬j ≺^[n] k    := by grind;
        _ ↔ ∀ j, ¬x ≺^[n + 1] j          := by simp;
    constructor
    · intro h y Rxy;
      exact lt_of_lt_of_le (cwfHeight_gt_of Rxy) h;
    · exact cwfHeight_le;

lemma le_height_iff_relItr : k ≤ x.rank ↔ ∃ y, x ≺^[k] y := calc
  _ ↔ ¬x.rank < k    := Iff.symm Nat.not_lt
  _ ↔ ∃ y, x ≺^[k] y := by simp [height_lt_iff_relItr]

lemma height_eq_iff_relItr : x.rank = k ↔ (∃ y, x ≺^[k] y) ∧ (∀ y, x ≺^[k] y → ∀ z, ¬y ≺ z) := calc
  _ ↔ x.rank < k + 1 ∧ k ≤ x.rank                       := by simpa [Nat.lt_succ_iff] using Nat.eq_iff_le_and_ge;
  _ ↔ (∀ y, ¬x ≺^[k + 1] y) ∧ (∃ y, x ≺^[k] y)          := by rw [height_lt_iff_relItr, le_height_iff_relItr];
  _ ↔ (∀ l y, x ≺^[k] y → ¬y ≺ l) ∧ (∃ y, x ≺^[k] y)    := by simp only [Model.relItr_succ']; grind;
  _ ↔ (∃ y, x ≺^[k] y) ∧ (∀ y, x ≺^[k] y → ∀ z, ¬y ≺ z) := by grind;

lemma exists_rank_terminal (x : M.World) : ∃ y, x ≺^[x.rank] y := le_height_iff_relItr.mp (by simp)

lemma terminal_rel_height (h : x ≺^[x.rank] y) : ∀ z, ¬y ≺ z := by
  intro z Ryz;
  suffices x.rank + 1 ≤ x.rank by omega;
  apply le_height_iff_relItr.mpr;
  exact ⟨z, Model.relItr_succ'.mpr ⟨y, h, Ryz⟩⟩;

lemma not_rel_over_rank (h : x.rank < k) : ¬x ≺^[k] y := by
  by_contra Rxy;
  rw [show k = x.rank + (k - x.rank) by omega] at Rxy;
  obtain ⟨z, Rxz, Rzy⟩ := Model.relItr_decomp Rxy;
  exact terminal_rel_height Rxz y $ Model.relItr_unwrap_trans_pos (by omega) Rzy;

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


namespace extendRoot

variable {n : ℕ+}

@[simp, grind .]
lemma eq_extendRoot_height_extendRoot_root_rank : (M.extendRoot n).height = (M.extendRoot n).root.1.rank := by
  dsimp [height]

@[simp, grind .]
lemma height_pos : 0 < (M.extendRoot n).height := lt_cwfHeight (b := Sum.inl M.root.1) (by grind) (by omega)

namespace Ext1

@[simp, grind .]
lemma eq_height_original_height_succ : (M.extendRoot 1).height = M.height + 1 := by
  let h := (M.extendRoot 1).height;
  let r := (M.extendRoot 1).root;

  suffices h ≤ M.height + 1 ∧ M.height < h by omega;
  constructor
  · suffices h - 1 ≤ M.height from Nat.le_add_of_sub_le this;
    apply le_height_iff_relItr.mpr;
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
    apply le_height_iff_relItr.mpr;
    rcases exists_rank_terminal M.root.1 with ⟨y, hy⟩;
    use ↑y, ↑M.root.1;
    constructor;
    . grind [embed];
    . grind;

@[simp, grind .]
lemma eq_embed_original_rank_original_rank {x₀ : M.World} : (embed (n := 1) x₀).rank = x₀.rank := by
  apply height_eq_iff_relItr.mpr;
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
      omega;

@[simp, grind .]
lemma eq_original_root_rank_original_height : Model.World.rank (M := M.extendRoot 1 |>.toModel) (x := M.root) = M.height := eq_embed_original_rank_original_rank

end Ext1

end extendRoot

end RootedModel

end
