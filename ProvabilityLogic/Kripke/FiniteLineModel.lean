module

public import ProvabilityLogic.Kripke.Rank

@[expose]
public section

abbrev finiteLineModel (n : ℕ) : RootedModel (Fin (n + 1)) Empty where
  Rel' := (· < ·)
  Val' _ _ := False
  root := ⟨0, by
    intro x hx;
    exact Fin.pos_of_ne_zero hx;
  ⟩

namespace finiteLineModel

variable {n : ℕ}

instance : Fintype (finiteLineModel n).World := inferInstance
instance : (finiteLineModel n).IsFiniteGL where
  finite := by infer_instance
instance : (finiteLineModel n).IsGL := Model.instIsGLOfIsFiniteGL

protected abbrev of (i : Fin (n + 1)) : (finiteLineModel n).World := i
instance : Coe (Fin (n + 1)) (finiteLineModel n).World := ⟨finiteLineModel.of⟩

lemma _root_.PNat.exists_eq_succ (n : ℕ+) : ∃ m : ℕ, n = m + 1 := by
  if n = 1 then
    use 0;
    simp_all;
  else
    obtain ⟨m, hm⟩ := PNat.exists_eq_succ_of_ne_one ‹_›;
    use m;
    simp_all;

lemma rank_eq (i : (finiteLineModel n).World) : i.rank = (n - i) := by
  induction i using Fin.reverseInduction with
  | last =>
    rw [show (n - (Fin.last n : ℕ)) = 0 by simp];
    apply Model.iff_rank_eq_zero.mpr;
    intro y;
    exact not_lt.mpr (Fin.le_last y);
  | cast i ih =>
    suffices (finiteLineModel.of i.castSucc).rank = (finiteLineModel.of i.succ).rank + 1 by grind;
    haveI : IsConverseWellFounded (finiteLineModel n).World (finiteLineModel n).Rel :=
      ⟨(inferInstance : (finiteLineModel n).IsGL).cwf⟩;
    apply cwfHeight_eq_succ_cwfHeight (R := (finiteLineModel n).Rel);
    . exact Fin.castSucc_lt_succ;
    . intro c hc;
      simp only [Model.Rel, Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hc ⊢;
      omega;

lemma height_eq : (finiteLineModel n).height = n := by apply rank_eq;

end finiteLineModel

universe u

/-- The `finiteLineModel n` lifted to an arbitrary universe `u` and to an arbitrary
letterless-formula alphabet `α`, via `ULift`. -/
abbrev uLiftFiniteLineModel (n : ℕ) {α : Type*} : RootedModel (ULift.{u} (Fin (n + 1))) α where
  Rel' x y := x.down < y.down
  Val' _ _ := False
  root := ⟨ULift.up 0, by
    rintro ⟨x⟩ hx;
    apply Fin.pos_of_ne_zero;
    intro h;
    subst h;
    exact hx rfl;
  ⟩

namespace uLiftFiniteLineModel

variable {n : ℕ} {α : Type*}

instance : Fintype (uLiftFiniteLineModel n (α := α)).World := inferInstance
instance : (uLiftFiniteLineModel n (α := α)).IsFiniteGL where
  finite := by infer_instance
instance : (uLiftFiniteLineModel n (α := α)).IsGL := Model.instIsGLOfIsFiniteGL

/-- The universe-lifting equivalence between the worlds of `finiteLineModel n` and
`uLiftFiniteLineModel n`, carrying the frame relation `<` to `≺`. -/
def worldEquiv : (finiteLineModel n).World ≃ (uLiftFiniteLineModel n (α := α)).World := Equiv.ulift.symm

lemma worldEquiv_rel_iff {i j : (finiteLineModel n).World} :
  i < j ↔ (worldEquiv (α := α) i : (uLiftFiniteLineModel n (α := α)).World) ≺ worldEquiv j := Iff.rfl

lemma rank_eq (x : (uLiftFiniteLineModel n (α := α)).World) : x.rank = (n - x.down) := by
  haveI : IsConverseWellFounded (finiteLineModel n).World (finiteLineModel n).Rel :=
    ⟨(inferInstance : (finiteLineModel n).IsGL).cwf⟩;
  haveI : IsConverseWellFounded (uLiftFiniteLineModel n (α := α)).World (uLiftFiniteLineModel n (α := α)).Rel :=
    ⟨(inferInstance : (uLiftFiniteLineModel n (α := α)).IsGL).cwf⟩;
  obtain ⟨i, rfl⟩ := worldEquiv.surjective x;
  show cwfHeight (uLiftFiniteLineModel n (α := α)).Rel (worldEquiv i) = (n - i);
  rw [← cwfHeight_congr (R := (finiteLineModel n).Rel) worldEquiv (fun a b => worldEquiv_rel_iff) i];
  exact finiteLineModel.rank_eq i;

lemma height_eq : (uLiftFiniteLineModel n (α := α)).height = n := by apply rank_eq;

end uLiftFiniteLineModel
