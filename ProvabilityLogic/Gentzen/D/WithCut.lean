module

public import ProvabilityLogic.Gentzen.D.Basic

/-!
`LogicD.GentzenWithCutProof`, the with-cut extension of the cut-free `D³_seq` calculus
(`ProvabilityLogic.Gentzen.D.Basic`) by a level-preserving cut rule.

Like `LogicD.ProofGentzen`, this is a single inductive on `ThreeLayeredSequent`, a `Sequent`
tagged with a level `l : Fin 3`: `l = 0` is the GL-sequent, `l = 1` is the S-sequent, and
`l = 2` is the D-sequent. The constructors encode the source's modal rules `(GL□)` (`boxGL`),
`(GLtoS)` (`liftUp`), `(S□left)` (`boxL`), and `(StoD)` (`liftUpBox`).
-/

@[expose]
public section

variable {α : Type u} [DecidableEq α]

/-- `LogicD.ProofGentzen` with a level-preserving cut rule.

  - [KKIM25, §3]
-/
inductive LogicD.GentzenWithCutProof : ThreeLayeredSequent α → Type u
| axm (l) (A)      : GentzenWithCutProof ({A} ⟹[l] {A})
| botL (l)         : GentzenWithCutProof ({⊥} ⟹[l] ∅)
| wkL  {l Γ Γ' Δ}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Γ ⊆ Γ' := by grind) → GentzenWithCutProof (Γ' ⟹[l] Δ)
| wkR  {l Γ Δ Δ'}  : GentzenWithCutProof (Γ ⟹[l] Δ) → (_ : Δ ⊆ Δ' := by grind) → GentzenWithCutProof (Γ ⟹[l] Δ')
| impL {l Γ Δ A B} : GentzenWithCutProof (Γ ⟹[l] (insert A Δ)) → GentzenWithCutProof (insert B Γ ⟹[l] Δ) → GentzenWithCutProof ((insert (A 🡒 B) Γ) ⟹[l] Δ)
| impR {l Γ Δ A B} : GentzenWithCutProof ((insert A Γ) ⟹[l] (insert B Δ)) → GentzenWithCutProof (Γ ⟹[l] (insert (A 🡒 B) Δ))
| boxGL {Γ A}      : GentzenWithCutProof ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) → GentzenWithCutProof (Γ.box ⟹[0] {□A})
| liftUp {Γ Δ}     : GentzenWithCutProof (Γ ⟹[0] Δ) → GentzenWithCutProof (Γ ⟹[1] Δ)
| boxL {Γ Δ A}     : GentzenWithCutProof (insert A Γ ⟹[1] Δ) → GentzenWithCutProof (insert (□A) Γ ⟹[1] Δ)
| liftUpBox {Γ Δ : FormulaFinset α} : GentzenWithCutProof (Γ.box ⟹[1] Δ.box) → GentzenWithCutProof (Γ.box ⟹[2] Δ.box)
| cut  {l Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹[l] insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹[l] Δ₂) → GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂)

namespace LogicD

scoped prefix:120 "⊢ᵍᶜ[D]! " => GentzenWithCutProof

abbrev GentzenWithCutProvable (S : ThreeLayeredSequent α) : Prop := Nonempty (⊢ᵍᶜ[D]! S)
scoped prefix:120 "⊢ᵍᶜ[D] " => GentzenWithCutProvable

def GentzenWithCutProof.ofProofGentzen {S : ThreeLayeredSequent α} : ⊢ᵍ[D]! S → ⊢ᵍᶜ[D]! S
| .axm l A    => .axm l A
| .botL l     => .botL l
| .wkL h h'   => .wkL (GentzenWithCutProof.ofProofGentzen h) h'
| .wkR h h'   => .wkR (GentzenWithCutProof.ofProofGentzen h) h'
| .impL h₁ h₂ => .impL (GentzenWithCutProof.ofProofGentzen h₁) (GentzenWithCutProof.ofProofGentzen h₂)
| .impR h     => .impR (GentzenWithCutProof.ofProofGentzen h)
| .boxGL h    => .boxGL (GentzenWithCutProof.ofProofGentzen h)
| .liftUp h   => .liftUp (GentzenWithCutProof.ofProofGentzen h)
| .boxL h     => .boxL (GentzenWithCutProof.ofProofGentzen h)
| .liftUpBox h => .liftUpBox (GentzenWithCutProof.ofProofGentzen h)

namespace GentzenWithCutProvable

variable {S : ThreeLayeredSequent α} {Γ Γ' Δ Δ' Γ₁ Γ₂ Δ₁ Δ₂ : FormulaFinset α} {A B : Formula α} {l : Fin 3}

/-- Cut-free `LogicD` provability implies `LogicD.GentzenWithCutProof` provability.

  - [KKIM25, §3]
-/
theorem of_without_cut : ⊢ᵍ[D] S → ⊢ᵍᶜ[D] S := λ ⟨h⟩ => ⟨GentzenWithCutProof.ofProofGentzen h⟩

lemma axm (l) (A : Formula α) : ⊢ᵍᶜ[D] ({A} ⟹[l] {A}) := ⟨GentzenWithCutProof.axm l A⟩
lemma botL (l) : ⊢ᵍᶜ[D] (({⊥} : FormulaFinset α) ⟹[l] ∅) := ⟨GentzenWithCutProof.botL l⟩
lemma wkL (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ') : ⊢ᵍᶜ[D] (Γ' ⟹[l] Δ) := ⟨GentzenWithCutProof.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ') : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ') := ⟨GentzenWithCutProof.wkR h.some h'⟩
lemma impL (h₁ : ⊢ᵍᶜ[D] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[D] (insert B Γ ⟹[l] Δ)) : ⊢ᵍᶜ[D] ((insert (A 🡒 B) Γ) ⟹[l] Δ) :=
  ⟨GentzenWithCutProof.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ[D] ((insert A Γ) ⟹[l] (insert B Δ))) : ⊢ᵍᶜ[D] (Γ ⟹[l] (insert (A 🡒 B) Δ)) := ⟨GentzenWithCutProof.impR h.some⟩
lemma liftUp (h : ⊢ᵍᶜ[D] (Γ ⟹[0] Δ)) : ⊢ᵍᶜ[D] (Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.liftUp h.some⟩
lemma boxGL (h : ⊢ᵍᶜ[D] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})) : ⊢ᵍᶜ[D] (Γ.box ⟹[0] {□A}) := ⟨GentzenWithCutProof.boxGL h.some⟩
lemma boxL (h : ⊢ᵍᶜ[D] (insert A Γ ⟹[1] Δ)) : ⊢ᵍᶜ[D] (insert (□A) Γ ⟹[1] Δ) := ⟨GentzenWithCutProof.boxL h.some⟩
lemma liftUpBox (h : ⊢ᵍᶜ[D] (Γ.box ⟹[1] Δ.box)) : ⊢ᵍᶜ[D] (Γ.box ⟹[2] Δ.box) := ⟨GentzenWithCutProof.liftUpBox h.some⟩
lemma cut (h₁ : ⊢ᵍᶜ[D] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[D] (insert A Γ₂ ⟹[l] Δ₂)) : ⊢ᵍᶜ[D] (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) :=
  ⟨GentzenWithCutProof.cut h₁.some h₂.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : ThreeLayeredSequent α) → ⊢ᵍᶜ[D] S → Prop}
  (axm : ∀ (l) (A : Formula α), motive ({A} ⟹[l] {A}) (GentzenWithCutProvable.axm l A))
  (botL : ∀ (l), motive (({⊥} : FormulaFinset α) ⟹[l] ∅) (GentzenWithCutProvable.botL l))
  (wkL : ∀ {l Γ Γ' Δ} (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹[l] Δ) h → motive (Γ' ⟹[l] Δ) (wkL h h'))
  (wkR : ∀ {l Γ Δ Δ'} (h : ⊢ᵍᶜ[D] (Γ ⟹[l] Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹[l] Δ) h → motive (Γ ⟹[l] Δ') (wkR h h'))
  (impL : ∀ {l Γ Δ A B} (h₁ : ⊢ᵍᶜ[D] (Γ ⟹[l] insert A Δ)) (h₂ : ⊢ᵍᶜ[D] (insert B Γ ⟹[l] Δ)),
    motive (Γ ⟹[l] insert A Δ) h₁ → motive (insert B Γ ⟹[l] Δ) h₂ →
    motive ((insert (A 🡒 B) Γ) ⟹[l] Δ) (impL h₁ h₂)
  )
  (impR : ∀ {l Γ Δ A B} (h : ⊢ᵍᶜ[D] ((insert A Γ) ⟹[l] (insert B Δ))),
    motive ((insert A Γ) ⟹[l] (insert B Δ)) h → motive (Γ ⟹[l] (insert (A 🡒 B) Δ)) (impR h)
  )
  (liftUp : ∀ {Γ Δ} (h : ⊢ᵍᶜ[D] (Γ ⟹[0] Δ)), motive (Γ ⟹[0] Δ) h → motive (Γ ⟹[1] Δ) (liftUp h))
  (boxGL : ∀ {Γ A} (h : ⊢ᵍᶜ[D] ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A})),
    motive ((insert (□A) (Γ ∪ Γ.box)) ⟹[0] {A}) h → motive (Γ.box ⟹[0] {□A}) (boxGL h)
  )
  (boxL : ∀ {Γ Δ A} (h : ⊢ᵍᶜ[D] (insert A Γ ⟹[1] Δ)),
    motive (insert A Γ ⟹[1] Δ) h → motive (insert (□A) Γ ⟹[1] Δ) (boxL h)
  )
  (liftUpBox : ∀ {Γ Δ : FormulaFinset α} (h : ⊢ᵍᶜ[D] (Γ.box ⟹[1] Δ.box)),
    motive (Γ.box ⟹[1] Δ.box) h → motive (Γ.box ⟹[2] Δ.box) (liftUpBox h)
  )
  (cut : ∀ {l Γ₁ Γ₂ Δ₁ Δ₂ A} (h₁ : ⊢ᵍᶜ[D] (Γ₁ ⟹[l] insert A Δ₁)) (h₂ : ⊢ᵍᶜ[D] (insert A Γ₂ ⟹[l] Δ₂)),
    motive (Γ₁ ⟹[l] insert A Δ₁) h₁ → motive (insert A Γ₂ ⟹[l] Δ₂) h₂ →
    motive (Γ₁ ∪ Γ₂ ⟹[l] Δ₁ ∪ Δ₂) (GentzenWithCutProvable.cut h₁ h₂)
  )
  : ∀ {S : ThreeLayeredSequent α} (h : ⊢ᵍᶜ[D] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

end GentzenWithCutProvable

end LogicD

end
