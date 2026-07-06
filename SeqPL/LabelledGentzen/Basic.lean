module

public import SeqPL.Formula.Basic

@[expose]
public section

/-!
Labelled sequent calculus `G3KGL` for `GL`, following Negri's labelled
sequent calculus for provability logic as presented in `[MPB23]`
(Maggesi & Perini Brogi, *Mechanising Gödel–Löb Provability Logic in HOL
Light*, JAR 2023), §2.2 (calculus `G3K`) and §6 (Fig. 2/3, calculus
`G3KGL`). World-labels are drawn from `ℕ`.
-/

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

/-- World-labels of the labelled sequent calculus. A bare `abbrev` for `ℕ`, kept
distinct so that arithmetic on `Formula`/proof-search data is not confused with
label bookkeeping. -/
abbrev Label := ℕ

/-- A labelled formula `x : A`: the formula `A` tagged with the world-label `x`. -/
structure LabelledFormula (α : Type u) where
  label : Label
  formula : Formula α
deriving DecidableEq

infix:70 " ∶ " => LabelledFormula.mk

namespace LabelledFormula

/-- Typst math-mode source for a labelled formula `x : A`. -/
protected def toString [ToString α] (lf : LabelledFormula α) : String :=
  s!"{lf.label} : {Formula.toString lf.formula}"

instance [ToString α] : ToString (LabelledFormula α) := ⟨LabelledFormula.toString⟩

end LabelledFormula

/-- A labelled sequent `R ⸴ Γ ⟹ˡ Δ`: `R` is a finite set of relational atoms
`x R y`, and `Γ`/`Δ` are finite sets of labelled formulas. -/
structure LabelledSequent (α : Type u) where
  rel : Finset (Label × Label)
  ant : Finset (LabelledFormula α)
  suc : Finset (LabelledFormula α)

notation:50 R:51 " ⸴ " Γ:51 " ⟹ˡ " Δ:51 => LabelledSequent.mk R Γ Δ

namespace LabelledSequent

variable {S : LabelledSequent α}

/-- Every world-label occurring in `S`, either in a labelled formula or in a relational atom. -/
@[grind]
def labels (S : LabelledSequent α) : Finset Label :=
  S.ant.image LabelledFormula.label ∪ S.suc.image LabelledFormula.label ∪ S.rel.image Prod.fst ∪ S.rel.image Prod.snd

/-- A label not occurring in `S`, for the eigenvariable condition of `R□^Löb`. -/
def freshLabel (S : LabelledSequent α) : Label := S.labels.sup id + 1

omit [DecidableEq α] in
lemma freshLabel_notMem : S.freshLabel ∉ S.labels := by
  intro h;
  have := Finset.le_sup (f := id) h;
  simp only [id, freshLabel] at this;
  exact Nat.not_succ_le_self _ this;

end LabelledSequent


inductive ProofLabelledGentzen : LabelledSequent α → Type u
| axm (x A) : ProofLabelledGentzen (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A})
| botL (x) : ProofLabelledGentzen (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α)))
| wkRel {R R' Γ Δ} : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ) → (_ : R ⊆ R' := by grind) → ProofLabelledGentzen (R' ⸴ Γ ⟹ˡ Δ)
| wkAnt {R Γ Γ' Δ} : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofLabelledGentzen (R ⸴ Γ' ⟹ˡ Δ)
| wkSuc {R Γ Δ Δ'} : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ')
| impL {R Γ Δ x A B} :
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ (insert (x ∶ A) Δ)) →
    ProofLabelledGentzen (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (R ⸴ (insert (x ∶ A 🡒 B) Γ) ⟹ˡ Δ)
| impR {R Γ Δ x A B} :
    ProofLabelledGentzen (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ)) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ (insert (x ∶ A 🡒 B) Δ))
/-- `L□`: uses an already available successor `y` of `x` (`x R y ∈ R`) to unfold `x : □A`. -/
| boxL {R Γ Δ} (x y A) (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ Γ := by grind) :
    ProofLabelledGentzen (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
/-- `R□^Löb`: introduces a fresh successor `y` of `x`, additionally assuming `y : □A` (the Löb trick). -/
| boxRLob {R Γ Δ} (x y A) (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels := by grind) :
    ProofLabelledGentzen (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ)
/-- `Irref`: a reflexive relational atom `x R x` closes any sequent. -/
| irref {R Γ Δ} (x) (h : (x, x) ∈ R := by grind) : ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
/-- `Trans`: saturates `R` with the transitive consequence of `x R y` and `y R z`. -/
| trans {R Γ Δ} (x y z) (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) :
    ProofLabelledGentzen (insert (x, z) R ⸴ Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
prefix:120 "⊢ˡ! " => ProofLabelledGentzen


namespace ProofLabelledGentzen

variable {R : Finset (Label × Label)} {Γ Δ : Finset (LabelledFormula α)} {x y : Label} {A B : Formula α}

def union (x A) (hΓ : (x ∶ A) ∈ Γ := by grind) (hΔ : (x ∶ A) ∈ Δ := by grind) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) :=
  wkSuc $ wkAnt $ wkRel (axm x A)

def botL_mem (x) (h : (x ∶ (⊥ : Formula α)) ∈ Γ := by grind) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) :=
  wkSuc (Δ := ∅) $ wkAnt $ wkRel (botL x)

def mdpL_mem (x A B) (h₁ : (x ∶ A 🡒 B) ∈ Γ := by grind) (h₂ : (x ∶ A) ∈ Γ := by grind) (h₃ : (x ∶ B) ∈ Δ := by grind) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  rw [(show Γ = insert (x ∶ A 🡒 B) (insert (x ∶ A) (Γ \ {x ∶ A, x ∶ A 🡒 B})) by grind)];
  apply impL;
  . apply union x A;
  . apply union x B;

def negL : ⊢ˡ! (R ⸴ Γ ⟹ˡ (insert (x ∶ A) Δ)) → ⊢ˡ! (R ⸴ (insert (x ∶ ∼A) Γ) ⟹ˡ Δ) := λ p => impL p (wkSuc $ wkAnt $ wkRel (botL x))

def negR : ⊢ˡ! (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ Δ) → ⊢ˡ! (R ⸴ Γ ⟹ˡ (insert (x ∶ ∼A) Δ)) := λ p => impR $ wkSuc $ wkAnt p (by grind)

def andL : ⊢ˡ! (R ⸴ (insert (x ∶ A) $ insert (x ∶ B) $ Γ) ⟹ˡ Δ) → ⊢ˡ! (R ⸴ insert (x ∶ A ⋏ B) Γ ⟹ˡ Δ) := λ p => by
  apply impL;
  . apply impR;
    apply negR;
    simpa [(show (insert (x ∶ A) $ insert (x ∶ B) Γ) = (insert (x ∶ B) $ insert (x ∶ A) Γ) by grind)] using p;
  . exact botL_mem x;

def andR : ⊢ˡ! (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ) → ⊢ˡ! (R ⸴ Γ ⟹ˡ insert (x ∶ B) Δ) → ⊢ˡ! (R ⸴ Γ ⟹ˡ insert (x ∶ A ⋏ B) Δ) := λ p q => by
  apply impR;
  apply impL;
  . exact wkSuc p;
  . exact negL $ wkSuc q;

def orL : ⊢ˡ! (R ⸴ insert (x ∶ A) Γ ⟹ˡ Δ) → ⊢ˡ! (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ) → ⊢ˡ! (R ⸴ insert (x ∶ A ⋎ B) Γ ⟹ˡ Δ) := λ p q => by
  apply impL;
  . exact negR p;
  . exact q;

def orR : ⊢ˡ! (R ⸴ Γ ⟹ˡ (insert (x ∶ A) $ insert (x ∶ B) Δ)) → ⊢ˡ! (R ⸴ Γ ⟹ˡ insert (x ∶ A ⋎ B) Δ) := λ p => by
  apply impR;
  apply negL;
  simpa;

/-- `[Neg14]` Lemma 5.2: a *looping* sequent, where the same boxed formula `□A` is attached
to the antecedent side of `x` and the succedent side of `y` for an accessibility atom
`x R y`, is derivable outright (root-first: `R□^Löb` with a fresh label `z`, `Trans`, `L□`). -/
def loop (x y z : Label) (A : Formula α)
  (hz : z ∉ (R ⸴ Γ ⟹ˡ Δ).labels)
  (hR : (x, y) ∈ R := by grind)
  (hx : (x ∶ □A) ∈ Γ := by grind)
  (hy : (y ∶ □A) ∈ Δ := by grind) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  have h : Δ = insert (y ∶ □A) (Δ.erase (y ∶ □A)) := by grind;
  rw [h];
  apply boxRLob y z A (hfresh := by rw [← h]; exact hz);
  apply trans x y z (hxy := by grind) (hyz := by grind);
  apply boxL x z A (hxy := by grind) (hxA := by grind);
  exact union z A (by grind) (by grind);

end ProofLabelledGentzen


abbrev ProvableLabelledGentzen (S : LabelledSequent α) : Prop := Nonempty (ProofLabelledGentzen S)
prefix:120 "⊢ˡ " => ProvableLabelledGentzen

namespace ProvableLabelledGentzen

variable {R R' : Finset (Label × Label)} {Γ Γ' Δ Δ' : Finset (LabelledFormula α)} {x y z : Label} {A B : Formula α}

lemma axm (x : Label) (A : Formula α) : ⊢ˡ (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) := ⟨ProofLabelledGentzen.axm x A⟩
lemma union (x : Label) (A : Formula α) (hΓ : (x ∶ A) ∈ Γ := by grind) (hΔ : (x ∶ A) ∈ Δ := by grind) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.union x A hΓ hΔ⟩
lemma botL (x : Label) : ⊢ˡ (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) := ⟨ProofLabelledGentzen.botL x⟩
@[grind =>] lemma botL_mem (x : Label) (h : (x ∶ (⊥ : Formula α)) ∈ Γ := by grind) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.botL_mem x h⟩
lemma wkRel (π : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ)) (h : R ⊆ R') : ⊢ˡ (R' ⸴ Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.wkRel π.some h⟩
lemma wkAnt (π : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ)) (h : Γ ⊆ Γ') : ⊢ˡ (R ⸴ Γ' ⟹ˡ Δ) := ⟨ProofLabelledGentzen.wkAnt π.some h⟩
lemma wkSuc (π : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ)) (h : Δ ⊆ Δ') : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ') := ⟨ProofLabelledGentzen.wkSuc π.some h⟩
lemma impL (π₁ : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (π₂ : ⊢ˡ (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)) : ⊢ˡ (R ⸴ (insert (x ∶ A 🡒 B) Γ) ⟹ˡ Δ) := ⟨ProofLabelledGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ˡ (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ))) : ⊢ˡ (R ⸴ Γ ⟹ˡ (insert (x ∶ A 🡒 B) Δ)) := ⟨ProofLabelledGentzen.impR π.some⟩
lemma boxL (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ Γ := by grind) (π : ⊢ˡ (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ)) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) :=
  ⟨ProofLabelledGentzen.boxL x y A hxy hxA π.some⟩
lemma boxRLob (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels := by grind)
    (π : ⊢ˡ (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ)) : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) :=
  ⟨ProofLabelledGentzen.boxRLob x y A hfresh π.some⟩
lemma irref (h : (x, x) ∈ R := by grind) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.irref x h⟩
lemma trans (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) (π : ⊢ˡ (insert (x, z) R ⸴ Γ ⟹ˡ Δ)) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) :=
  ⟨ProofLabelledGentzen.trans x y z hxy hyz π.some⟩

lemma negL (h : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) : ⊢ˡ (R ⸴ insert (x ∶ ∼A) Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.negL h.some⟩
lemma negR (h : ⊢ˡ (R ⸴ insert (x ∶ A) Γ ⟹ˡ Δ)) : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ ∼A) Δ) := ⟨ProofLabelledGentzen.negR h.some⟩
lemma andL (h : ⊢ˡ (R ⸴ insert (x ∶ A) (insert (x ∶ B) Γ) ⟹ˡ Δ)) : ⊢ˡ (R ⸴ insert (x ∶ A ⋏ B) Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.andL h.some⟩
lemma andR (h₁ : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (h₂ : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ B) Δ)) : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ A ⋏ B) Δ) := ⟨ProofLabelledGentzen.andR h₁.some h₂.some⟩
lemma orL (h₁ : ⊢ˡ (R ⸴ insert (x ∶ A) Γ ⟹ˡ Δ)) (h₂ : ⊢ˡ (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)) : ⊢ˡ (R ⸴ insert (x ∶ A ⋎ B) Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.orL h₁.some h₂.some⟩
lemma orR (h : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ A) (insert (x ∶ B) Δ))) : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ A ⋎ B) Δ) := ⟨ProofLabelledGentzen.orR h.some⟩

lemma loop (x y : Label) (A : Formula α) (hR : (x, y) ∈ R := by grind)
  (hx : (x ∶ □A) ∈ Γ := by grind) (hy : (y ∶ □A) ∈ Δ := by grind) : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) :=
  ⟨ProofLabelledGentzen.loop x y (R ⸴ Γ ⟹ˡ Δ).freshLabel A LabelledSequent.freshLabel_notMem hR hx hy⟩

prefix:120 "⊬ˡ " => λ S => ¬⊢ˡ S

lemma iff_unprovableLabelledGentzen_isEmpty_ProofLabelledGentzen {S : LabelledSequent α} : (⊬ˡ S) ↔ (IsEmpty (⊢ˡ! S)) := by simp [ProvableLabelledGentzen];

end ProvableLabelledGentzen

end LabelledGentzen

end
