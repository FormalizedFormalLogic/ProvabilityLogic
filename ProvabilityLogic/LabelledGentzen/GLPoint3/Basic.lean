module

public import ProvabilityLogic.LabelledGentzen.Basic

/-!
Labelled sequent calculus for `LogicGLPoint3` (`GL.3`), obtained from the labelled
calculus `G3KGL` for `GL` (`ProvabilityLogic.LabelledGentzen.Basic`) by adding a structural
rule `Lin` for linearity (weak connectedness) of the accessibility relation:
given `x R y` and `x R z`, the successors `y` and `z` of a common world are
compared by branching into `y R z`, `y = z` (realised as a relabelling of `y`
to `z`), or `z R y`.
-/

@[expose]
public section

namespace LabelledGentzen

variable {α : Type u} [DecidableEq α]

namespace LabelledFormula

/-- Renaming a labelled formula: replace the label `y` by `z` wherever it occurs. -/
def relabel (y z : Label) (lf : LabelledFormula α) : LabelledFormula α := ⟨if lf.label = y then z else lf.label, lf.formula⟩

omit [DecidableEq α] in
@[simp] lemma relabel_label (y z : Label) (lf : LabelledFormula α) : (lf.relabel y z).label = if lf.label = y then z else lf.label := rfl

omit [DecidableEq α] in
@[simp] lemma relabel_formula (y z : Label) (lf : LabelledFormula α) : (lf.relabel y z).formula = lf.formula := rfl

end LabelledFormula

namespace LabelledSequent

/-- Renaming a labelled sequent: replace the label `y` by `z` wherever it occurs, in the
relational atoms as well as in the antecedent and succedent formulas. -/
def relabel (y z : Label) (S : LabelledSequent α) : LabelledSequent α where
  rel := S.rel.image (fun p => (if p.1 = y then z else p.1, if p.2 = y then z else p.2))
  ant := S.ant.image (LabelledFormula.relabel y z)
  suc := S.suc.image (LabelledFormula.relabel y z)

end LabelledSequent


namespace GLPoint3

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
/-- `Lin`: linearity (weak connectedness). Two successors `y`, `z` of a common world `x` are
compared by branching into `y R z`, `y = z` (realised by relabelling `y` to `z`), or `z R y`. -/
| lin {R Γ Δ} (x y z) (hxy : (x, y) ∈ R := by grind) (hxz : (x, z) ∈ R := by grind) :
    ProofLabelledGentzen (insert (y, z) R ⸴ Γ ⟹ˡ Δ) →
    ProofLabelledGentzen (insert (z, y) R ⸴ Γ ⟹ˡ Δ) →
    ProofLabelledGentzen ((R ⸴ Γ ⟹ˡ Δ).relabel y z) →
    ProofLabelledGentzen (R ⸴ Γ ⟹ˡ Δ)
prefix:120 "⊢ˡ³! " => ProofLabelledGentzen


abbrev ProvableLabelledGentzen (S : LabelledSequent α) : Prop := Nonempty (ProofLabelledGentzen S)
prefix:120 "⊢ˡ³ " => ProvableLabelledGentzen

namespace ProvableLabelledGentzen

variable {R R' : Finset LabelRel} {Γ Γ' Δ Δ' : Finset (LabelledFormula α)} {x y z : Label} {A B : Formula α}

lemma axm (x : Label) (A : Formula α) : ⊢ˡ³ (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) := ⟨ProofLabelledGentzen.axm x A⟩
lemma botL (x : Label) : ⊢ˡ³ (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) := ⟨ProofLabelledGentzen.botL x⟩
lemma wkRel (π : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ)) (h : R ⊆ R') : ⊢ˡ³ (R' ⸴ Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.wkRel π.some h⟩
lemma wkAnt (π : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ)) (h : Γ ⊆ Γ') : ⊢ˡ³ (R ⸴ Γ' ⟹ˡ Δ) := ⟨ProofLabelledGentzen.wkAnt π.some h⟩
lemma wkSuc (π : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ)) (h : Δ ⊆ Δ') : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ') := ⟨ProofLabelledGentzen.wkSuc π.some h⟩
lemma impL (π₁ : ⊢ˡ³ (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (π₂ : ⊢ˡ³ (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)) : ⊢ˡ³ (R ⸴ (insert (x ∶ A 🡒 B) Γ) ⟹ˡ Δ) := ⟨ProofLabelledGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ˡ³ (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ))) : ⊢ˡ³ (R ⸴ Γ ⟹ˡ (insert (x ∶ A 🡒 B) Δ)) := ⟨ProofLabelledGentzen.impR π.some⟩
lemma boxL (hxy : (x, y) ∈ R := by grind) (hxA : (x ∶ □A) ∈ Γ := by grind) (π : ⊢ˡ³ (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ)) : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ) :=
  ⟨ProofLabelledGentzen.boxL x y A hxy hxA π.some⟩
lemma boxRLob (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels := by grind)
  (π : ⊢ˡ³ (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ)) : ⊢ˡ³ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) :=
  ⟨ProofLabelledGentzen.boxRLob x y A hfresh π.some⟩
lemma irref (h : (x, x) ∈ R := by grind) : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ) := ⟨ProofLabelledGentzen.irref x h⟩
lemma trans (hxy : (x, y) ∈ R := by grind) (hyz : (y, z) ∈ R := by grind) (π : ⊢ˡ³ (insert (x, z) R ⸴ Γ ⟹ˡ Δ)) : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ) :=
  ⟨ProofLabelledGentzen.trans x y z hxy hyz π.some⟩
lemma lin (hxy : (x, y) ∈ R := by grind) (hxz : (x, z) ∈ R := by grind)
  (π₁ : ⊢ˡ³ (insert (y, z) R ⸴ Γ ⟹ˡ Δ)) (π₂ : ⊢ˡ³ (insert (z, y) R ⸴ Γ ⟹ˡ Δ))
  (π₃ : ⊢ˡ³ ((R ⸴ Γ ⟹ˡ Δ).relabel y z)) : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ) :=
  ⟨ProofLabelledGentzen.lin x y z hxy hxz π₁.some π₂.some π₃.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : LabelledSequent α) → ⊢ˡ³ S → Prop}
  (axm : ∀ x A, motive (∅ ⸴ {x ∶ A} ⟹ˡ {x ∶ A}) (ProvableLabelledGentzen.axm x A))
  (botL : ∀ x, motive (∅ ⸴ {x ∶ (⊥ : Formula α)} ⟹ˡ (∅ : Finset (LabelledFormula α))) (ProvableLabelledGentzen.botL x))
  (wkRel : ∀ {R R' Γ Δ} (h : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ)) (h' : R ⊆ R'),
    motive (R ⸴ Γ ⟹ˡ Δ) h → motive (R' ⸴ Γ ⟹ˡ Δ) (wkRel h h')
  )
  (wkAnt : ∀ {R Γ Γ' Δ} (h : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ)) (h' : Γ ⊆ Γ'),
    motive (R ⸴ Γ ⟹ˡ Δ) h → motive (R ⸴ Γ' ⟹ˡ Δ) (wkAnt h h')
  )
  (wkSuc : ∀ {R Γ Δ Δ'} (h : ⊢ˡ³ (R ⸴ Γ ⟹ˡ Δ)) (h' : Δ ⊆ Δ'),
    motive (R ⸴ Γ ⟹ˡ Δ) h → motive (R ⸴ Γ ⟹ˡ Δ') (wkSuc h h')
  )
  (impL : ∀ {R Γ Δ x A B} (h₁ : ⊢ˡ³ (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ)) (h₂ : ⊢ˡ³ (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ)),
    motive (R ⸴ Γ ⟹ˡ insert (x ∶ A) Δ) h₁ → motive (R ⸴ insert (x ∶ B) Γ ⟹ˡ Δ) h₂ →
    motive (R ⸴ (insert (x ∶ A 🡒 B) Γ) ⟹ˡ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {R Γ Δ x A B} (h : ⊢ˡ³ (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ))),
    motive (R ⸴ (insert (x ∶ A) Γ) ⟹ˡ (insert (x ∶ B) Δ)) h → motive (R ⸴ Γ ⟹ˡ (insert (x ∶ A 🡒 B) Δ)) (impR h)
  )
  (boxL : ∀ {R Γ Δ x y A} (hxy : (x, y) ∈ R) (hxA : (x ∶ □A) ∈ Γ) (h : ⊢ˡ³ (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ)),
    motive (R ⸴ insert (y ∶ A) Γ ⟹ˡ Δ) h → motive (R ⸴ Γ ⟹ˡ Δ) (boxL hxy hxA h)
  )
  (boxRLob : ∀ {R Γ Δ x y A} (hfresh : y ∉ (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ).labels)
      (h : ⊢ˡ³ (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ)),
    motive (insert (x, y) R ⸴ insert (y ∶ □A) Γ ⟹ˡ insert (y ∶ A) Δ) h →
    motive (R ⸴ Γ ⟹ˡ insert (x ∶ □A) Δ) (boxRLob hfresh h)
  )
  (irref : ∀ {R Γ Δ x} (h : (x, x) ∈ R), motive (R ⸴ Γ ⟹ˡ Δ) (irref h))
  (trans : ∀ {R Γ Δ x y z} (hxy : (x, y) ∈ R) (hyz : (y, z) ∈ R) (h : ⊢ˡ³ (insert (x, z) R ⸴ Γ ⟹ˡ Δ)),
    motive (insert (x, z) R ⸴ Γ ⟹ˡ Δ) h → motive (R ⸴ Γ ⟹ˡ Δ) (trans hxy hyz h)
  )
  (lin : ∀ {R Γ Δ x y z} (hxy : (x, y) ∈ R) (hxz : (x, z) ∈ R)
      (h₁ : ⊢ˡ³ (insert (y, z) R ⸴ Γ ⟹ˡ Δ)) (h₂ : ⊢ˡ³ (insert (z, y) R ⸴ Γ ⟹ˡ Δ))
      (h₃ : ⊢ˡ³ ((R ⸴ Γ ⟹ˡ Δ).relabel y z)),
    motive (insert (y, z) R ⸴ Γ ⟹ˡ Δ) h₁ → motive (insert (z, y) R ⸴ Γ ⟹ˡ Δ) h₂ →
    motive ((R ⸴ Γ ⟹ˡ Δ).relabel y z) h₃ → motive (R ⸴ Γ ⟹ˡ Δ) (lin hxy hxz h₁ h₂ h₃)
  )
  : ∀ {S : LabelledSequent α} (h : ⊢ˡ³ S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

end ProvableLabelledGentzen

end GLPoint3

end LabelledGentzen

end
