module

public import ProvabilityLogic.LabelledGentzen.Sequent
public import Mathlib.Combinatorics.Pigeonhole

/-!
Labelled sequent calculus `G3KGL` for `GL`, following Negri's labelled
sequent calculus for provability logic. World-labels are drawn from `ℕ`.

- [MPB23, §2.2, §6]
-/

/-!
Looping sequents are provable, and the pigeonhole argument underlying the
termination of proof search: along a chain of relational atoms longer than
the number of available boxed formulas, some boxed formula repeats at both
ends of a subchain, so the sequent is provable by looping.

- [Neg14, Lemma 5.2, Theorem 5.5]
-/

@[expose]
public section

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

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

variable {R : Finset LabelRel} {Γ Δ : Finset (LabelledFormula α)} {x y : Label} {A B : Formula α}

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

/--
A *looping* sequent, where the same boxed formula `□A` is attached
to the antecedent side of `x` and the succedent side of `y` for an accessibility atom
`x R y`, is derivable outright.

- [Neg14, Lemma 5.2]
-/
def loop (x y z : Label) (A : Formula α)
  (hz : z ∉ (R ⸴ Γ ⟹ˡ Δ).labels)
  (hR : (x, y) ∈ R := by grind)
  (hx : (x ∶ □A) ∈ Γ := by grind)
  (hy : (y ∶ □A) ∈ Δ := by grind) : ⊢ˡ! (R ⸴ Γ ⟹ˡ Δ) := by
  -- Root-first: `R□^Löb` introduces a fresh successor `z` of `y` (assuming `z : □A`),
  -- `Trans` derives `x R z` from `x R y` and `y R z`, then `L□` unfolds `x : □A` via `z`,
  -- closing with an axiom on `z : A`.
  rw [(show Δ = insert (y ∶ □A) (Δ.erase (y ∶ □A)) by grind)];
  apply boxRLob y z A;
  apply trans x y z;
  apply boxL x z A;
  exact union z A;

end ProofLabelledGentzen


abbrev ProvableLabelledGentzen (S : LabelledSequent α) : Prop := Nonempty (ProofLabelledGentzen S)
prefix:120 "⊢ˡ " => ProvableLabelledGentzen

namespace ProvableLabelledGentzen

variable {R R' : Finset LabelRel} {Γ Γ' Δ Δ' : Finset (LabelledFormula α)} {x y z : Label} {A B : Formula α}

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

@[induction_eliminator]
lemma rec
  {motive : (S : LabelledSequent α) → ⊢ˡ S → Prop}
  (axm : ∀ x A, motive (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) (ProvableLabelledGentzen.axm x A))
  (botL : ∀ x, motive (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) (ProvableLabelledGentzen.botL x))
  (wkRel : ∀ {R R' Γ Δ} (h : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ)) (h' : R ⊆ R'),
    motive (R ⸴ Γ ⟹ˡ Δ) h → motive (R' ⸴ Γ ⟹ˡ Δ) (wkRel h h')
  )
  (wkAnt : ∀ {R Γ Γ' Δ} (h : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ)) (h' : Γ ⊆ Γ'),
    motive (R ⸴ Γ ⟹ˡ Δ) h → motive (R ⸴ Γ' ⟹ˡ Δ) (wkAnt h h')
  )
  (wkSuc : ∀ {R Γ Δ Δ'} (h : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ)) (h' : Δ ⊆ Δ'),
    motive (R ⸴ Γ ⟹ˡ Δ) h → motive (R ⸴ Γ ⟹ˡ Δ') (wkSuc h h')
  )
  (impL : ∀ {R Γ Δ x A B} (h₁ : ⊢ˡ (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (h₂ : ⊢ˡ (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)),
    motive (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ) h₁ → motive (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ) h₂ →
    motive (R ⸴ (insert (x ∶ A 🡒 B) Γ) ⟹ˡ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {R Γ Δ x A B} (h : ⊢ˡ (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ))),
    motive (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ)) h → motive (R ⸴ Γ ⟹ˡ (insert (x ∶ A 🡒 B) Δ)) (impR h)
  )
  (boxL : ∀ {R Γ Δ x y A} (hxy : (x, y) ∈ R) (hxA : (x ∶ □A) ∈ Γ) (h : ⊢ˡ (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ)),
    motive (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ) h → motive (R ⸴ Γ ⟹ˡ Δ) (boxL hxy hxA h)
  )
  (boxRLob : ∀ {R Γ Δ x y A} (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels)
      (h : ⊢ˡ (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ)),
    motive (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ) h →
    motive (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) (boxRLob hfresh h)
  )
  (irref : ∀ {R Γ Δ x} (h : (x, x) ∈ R), motive (R ⸴ Γ ⟹ˡ Δ) (irref h))
  (trans : ∀ {R Γ Δ x y z} (hxy : (x, y) ∈ R) (hyz : (y, z) ∈ R) (h : ⊢ˡ (insert (x, z) R ⸴ Γ ⟹ˡ Δ)),
    motive (insert (x, z) R ⸴ Γ ⟹ˡ Δ) h → motive (R ⸴ Γ ⟹ˡ Δ) (trans hxy hyz h)
  )
  : ∀ {S : LabelledSequent α} (h : ⊢ˡ S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

prefix:120 "⊬ˡ " => λ S => ¬⊢ˡ S

lemma iff_unprovableLabelledGentzen_isEmpty_ProofLabelledGentzen {S : LabelledSequent α} : (⊬ˡ S) ↔ (IsEmpty (⊢ˡ! S)) := by simp [ProvableLabelledGentzen];

end ProvableLabelledGentzen


namespace ProvableLabelledGentzen

variable {R : Finset LabelRel} {Γ Δ : Finset (LabelledFormula α)}
         {x y z : Label} {A B : Formula α}

/-- If `y` is reachable from `x` through a nonempty chain of relational atoms in `R`,
then the relational atom `(x, y)` can be discharged by `Trans`. -/
lemma of_transGen_insert (h : Relation.TransGen (λ a b => (a, b) ∈ R) x y)
  : ⊢ˡ (insert (x, y) R ⸴ Γ ⟹ˡ Δ) → ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := by
  induction h with
  | single hxy =>
    simp [Finset.insert_eq_self.mpr hxy];
  | @tail b c _ hbc ih =>
    intro π;
    apply ih;
    apply trans (x := x) (y := b) (z := c);
    apply wkRel π;
    grind;

/--
Chain form of the looping lemma: a looping sequent is provable. If there is a nonempty
chain of relational atoms from `x` to `y`, and the same boxed formula `□A`
occurs at `x` in the antecedent and at `y` in the succedent, the sequent is provable.
The single-edge case is `ProvableLabelledGentzen.loop`.

- [Neg14, Lemma 5.2]
-/
lemma loopChain (h : Relation.TransGen (λ a b => (a, b) ∈ R) x y)
  (hx : (x ∶ □A) ∈ Γ := by grind) (hy : (y ∶ □A) ∈ Δ := by grind)
  : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := by
  apply of_transGen_insert h;
  exact loop x y A;

/-- `ReflTransGen` variant of `loopChain`, additionally covering the degenerate case `x = y`. -/
lemma loopChain' (h : Relation.ReflTransGen (λ a b => (a, b) ∈ R) x y)
  (hx : (x ∶ □A) ∈ Γ := by grind) (hy : (y ∶ □A) ∈ Δ := by grind)
  : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := by
  -- split on whether `x = y` (closed directly by `union`) or a genuine chain (delegate to `loopChain`)
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with rfl | h;
  . exact union y (□A);
  . exact loopChain h hx hy;

omit [DecidableEq α] in
/-- A nonempty chain of relational atoms in `R` yields a `TransGen` step. -/
lemma transGen_of_isChain {l : List Label} (hl : l ≠ [])
  (hchain : (x :: l).IsChain (λ a b => (a, b) ∈ R))
  : Relation.TransGen (λ a b => (a, b) ∈ R) x (l.getLast hl) := by
  induction l generalizing x with
  | nil => grind
  | cons b l ih =>
    rcases List.isChain_cons_cons.mp hchain with ⟨hxb, hchain⟩;
    match l with
    | [] => exact Relation.TransGen.single hxb;
    | c :: l =>
      rw [List.getLast_cons (by grind)];
      exact Relation.TransGen.head hxb (ih (by grind) hchain);

/--
`List`-chain form of the looping lemma: `x R y₁, …, yₙ₋₁ R yₙ` with
`x ∶ □A` in the antecedent and `yₙ ∶ □A` in the succedent.

- [Neg14, Lemma 5.2]
-/
lemma loopChain_of_isChain {l : List Label} (hl : l ≠ [])
  (hchain : (x :: l).IsChain (λ a b => (a, b) ∈ R))
  (hx : (x ∶ □A) ∈ Γ := by grind) (hy : ((l.getLast hl) ∶ □A) ∈ Δ := by grind)
  : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) :=
  loopChain (transGen_of_isChain hl hchain) hx hy


section Pigeonhole

variable {n : ℕ} {xs : Fin (n + 1) → Label}

omit [DecidableEq α] in
/-- Any segment of a chain `xs 0 R xs 1 R … R xs n` yields a `ReflTransGen` step. -/
lemma reflTransGen_of_chain (hchain : ∀ i : Fin n, (xs i.castSucc, xs i.succ) ∈ R) (hab : a ≤ b)
  : Relation.ReflTransGen (λ u w => (u, w) ∈ R) (xs a) (xs b) := by
  induction b using Fin.induction with
  | zero =>
    grind;
  | succ i ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt;
    . exact Relation.ReflTransGen.refl;
    . exact Relation.ReflTransGen.tail (ih (by grind)) (hchain i);

/--
Pigeonhole core of the termination argument: suppose that along a chain
`xs 0 R xs 1 R … R xs n` each edge `i` is generated by a boxed formula `□(f i)`,
occurring in the succedent at its source `xs i` and in the antecedent at its
target `xs (i + 1)`, with all `f i` drawn from a finite stock `X`.
If the chain has more edges than `X` has elements, then some boxed formula
repeats along the chain and the sequent is provable.

- [Neg14, Theorem 5.5]
-/
theorem provable_of_long_chain {X : Finset (Formula α)} (hX : X.card < n)
  (hchain : ∀ i : Fin n, (xs i.castSucc, xs i.succ) ∈ R)
  {f : Fin n → Formula α} (hf : ∀ i, f i ∈ X)
  (hant : ∀ i : Fin n, ((xs i.succ) ∶ □(f i)) ∈ Γ)
  (hsuc : ∀ i : Fin n, ((xs i.castSucc) ∶ □(f i)) ∈ Δ)
  : ⊢ˡ (R ⸴ Γ ⟹ˡ Δ) := by
  -- pigeonhole: more edges than elements of `X` forces two edges `i ≠ j` with `f i = f j`;
  -- whichever of `i.succ`, `j.succ` comes first, `loopChain'` closes the sequent via the repeat
  obtain ⟨i, -, j, -, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin n))) (t := X) (by simpa using hX) (λ i _ => hf i);
  wlog hij : i < j;
  . exact this (i := j) (j := i) ‹_› ‹_› ‹_› ‹_› ‹_› (by grind) (by grind) (by omega);
  apply loopChain' (A := f i) (reflTransGen_of_chain hchain ?_) (hant i) (by rw [heq]; exact hsuc j);
  grind;

end Pigeonhole

end ProvableLabelledGentzen

end LabelledGentzen

end
