module

public import ProvabilityLogic.Kripke.Rank

@[expose]
public section

/-- The chain `0 ≺ 1 ≺ ⋯ ≺ n` on `Fin (n + 1)`, with every propositional variable false. -/
abbrev finiteLineModel (n : ℕ) {α : Type*} : RootedModel (Fin (n + 1)) α where
  Rel' := (· < ·)
  Val' _ _ := False
  root := ⟨0, by
    intro x hx;
    exact Fin.pos_of_ne_zero hx;
  ⟩

namespace finiteLineModel

variable {n : ℕ} {α : Type*}

instance : Fintype (finiteLineModel n (α := α)).World := inferInstance
instance : (finiteLineModel n (α := α)).IsFiniteGL where
  finite := by infer_instance
instance : (finiteLineModel n (α := α)).IsGL := Model.instIsGLOfIsFiniteGL

protected abbrev of (i : Fin (n + 1)) : (finiteLineModel n (α := α)).World := i
instance : Coe (Fin (n + 1)) (finiteLineModel n (α := α)).World := ⟨finiteLineModel.of⟩

lemma _root_.PNat.exists_eq_succ (n : ℕ+) : ∃ m : ℕ, n = m + 1 := by
  if n = 1 then
    use 0;
    simp_all;
  else
    obtain ⟨m, hm⟩ := PNat.exists_eq_succ_of_ne_one ‹_›;
    use m;
    simp_all;

lemma rank_eq (i : (finiteLineModel n (α := α)).World) : i.rank = (n - i) := by
  induction i using Fin.reverseInduction with
  | last =>
    rw [show (n - (Fin.last n : ℕ)) = 0 by simp];
    apply Model.iff_rank_eq_zero.mpr;
    intro y;
    exact not_lt.mpr (Fin.le_last y);
  | cast i ih =>
    suffices
      (finiteLineModel.of (α := α) i.castSucc).rank = (finiteLineModel.of (α := α) i.succ).rank + 1
      by grind;
    haveI :
      IsConverseWellFounded (finiteLineModel n (α := α)).World (finiteLineModel n (α := α)).Rel :=
      ⟨(inferInstance : (finiteLineModel n (α := α)).IsGL).cwf⟩;
    apply cwfHeight_eq_succ_cwfHeight (R := (finiteLineModel n (α := α)).Rel);
    . exact Fin.castSucc_lt_succ;
    . intro c hc;
      simp only [Model.Rel, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hc ⊢;
      omega;

lemma height_eq : (finiteLineModel n (α := α)).height = n := by apply rank_eq;

end finiteLineModel
