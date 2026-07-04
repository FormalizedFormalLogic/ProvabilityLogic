module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Fintype.List
public import Mathlib.Data.Fintype.EquivFin

@[expose]
public section

namespace List.IsChain

variable {α : Type*} {R : α → α → Prop} {l : List α} {x y : α}

/-- 推移的関係の chain 上の相異なる 2 元はいずれかの向きに関係する． -/
lemma connected_of_trans [IsTrans α R] (h : List.IsChain R l)
    (hx : x ∈ l) (hy : y ∈ l) (nexy : x ≠ y) : R x y ∨ R y x := by
  have hp : l.Pairwise (fun a b => R a b ∨ R b a) :=
    (List.isChain_iff_pairwise.mp h).imp (fun h => Or.inl h);
  haveI : Std.Symm (fun a b => R a b ∨ R b a) := ⟨fun _ _ h => h.symm⟩;
  exact hp.forall hx hy nexy;

/-- 非反射的・推移的関係の chain は重複を持たない． -/
lemma nodup_of_irrefl_trans [IsTrans α R] [Std.Irrefl R] (h : List.IsChain R l) : l.Nodup := by
  apply (List.isChain_iff_pairwise.mp h).imp;
  intro a b hab e;
  subst e;
  exact Std.Irrefl.irrefl a hab;

end List.IsChain


namespace List

variable {α : Type*} {R : α → α → Prop} {l : List α} {a : α}

private lemma isChain_concat :
    (l.concat a).IsChain R ↔ l.IsChain R ∧ ∀ x ∈ l.getLast?, R x a := by
  rw [List.concat_eq_append];
  constructor;
  . intro h;
    simpa using List.isChain_append.mp h;
  . rintro ⟨h₁, h₂⟩;
    apply List.isChain_append.mpr;
    refine ⟨h₁, by simp, ?_⟩;
    intro x hx;
    simpa using h₂ x hx;

/-- Appending one element to the end of a nonempty list keeps it a chain iff the
old last element relates to the new one. -/
lemma isChain_concat_of_not_nil (hl : l ≠ []) :
    (l.concat a).IsChain R ↔ l.IsChain R ∧ R (l.getLast hl) a := by
  apply Iff.trans isChain_concat;
  suffices (∀ x ∈ l.getLast?, R x a) ↔ R (l.getLast hl) a by tauto;
  constructor;
  . intro h;
    exact h (l.getLast hl) (List.getLast_mem_getLast? hl);
  . rintro h x hx;
    convert h;
    simp_all [List.getLast?_eq_some_getLast hl];

/-- In a chain under a transitive relation, every element other than the last
one relates to the last element. -/
lemma rel_getLast_of_isChain_trans [IsTrans α R] (h : l.IsChain R) (lh : l ≠ []) :
    ∀ x ∈ l, x ≠ l.getLast lh → R x (l.getLast lh) := by
  intro x hx₁ hx₂;
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx₁;
  rw [List.getLast_eq_getElem] at hx₂ ⊢;
  apply List.pairwise_iff_getElem.mp (List.isChain_iff_pairwise.mp h);
  rcases Nat.lt_or_ge i (l.length - 1) with hlt | hge;
  . exact hlt;
  . exact absurd (by congr 1; omega) hx₂;

/-- The chains under an irreflexive transitive relation over a finite type form a
finite set (they are exactly the strictly increasing sequences, so nodup). -/
lemma chains_finite [DecidableEq α] [Finite α] [IsTrans α R] [Std.Irrefl R] :
    Finite { l : List α // l.IsChain R } := by
  haveI := Fintype.ofFinite α;
  haveI : Finite { l : List α // l.Nodup } := Finite.of_fintype _;
  apply Finite.of_injective
    (fun l : { l : List α // l.IsChain R } =>
      (⟨l.1, l.2.nodup_of_irrefl_trans⟩ : { l : List α // l.Nodup }));
  rintro ⟨l, _⟩ ⟨m, _⟩ h;
  simpa using h;

end List

end
