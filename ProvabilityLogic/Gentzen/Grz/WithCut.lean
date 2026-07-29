module

public import ProvabilityLogic.Gentzen.Grz.Basic

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace LogicGrz

open LogicGL
open scoped FormulaFinset

/--
The cut-full Gentzen sequent calculus for `Grz`: the cut-free rules of `LogicGrz.ProofGentzen`
together with the `cut` rule. Cut-elimination (`ProvableGentzen.of_with_cut` below) shows that
adding `cut` yields no new provable sequents.
-/
inductive GentzenWithCutProof : Sequent α → Type u
| axm (A) : GentzenWithCutProof ({A} ⟹ {A})
| botL : GentzenWithCutProof ({⊥} ⟹ ∅)
| wkL  {Γ Γ' Δ}  : GentzenWithCutProof (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → GentzenWithCutProof (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : GentzenWithCutProof (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → GentzenWithCutProof (Γ ⟹ Δ')
| impL {Γ Δ A B} : GentzenWithCutProof (Γ ⟹ (insert A Δ)) → GentzenWithCutProof (insert B Γ ⟹ Δ) → GentzenWithCutProof ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : GentzenWithCutProof ((insert A Γ) ⟹ (insert B Δ)) → GentzenWithCutProof (Γ ⟹ (insert (A 🡒 B) Δ))
| boxT   {Γ Δ : FormulaFinset α} {B} : GentzenWithCutProof (insert B Γ ⟹ Δ) → GentzenWithCutProof (insert (□B) Γ ⟹ Δ)
| boxGrz {Γ : FormulaFinset α} {A}   : GentzenWithCutProof (insert (□(A 🡒 □A)) (□Γ) ⟹ {A}) → GentzenWithCutProof (□Γ ⟹ {□A})
| cut {Γ₁ Γ₂ Δ₁ Δ₂ A} : GentzenWithCutProof (Γ₁ ⟹ insert A Δ₁) → GentzenWithCutProof (insert A Γ₂ ⟹ Δ₂) → GentzenWithCutProof (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂)
notation:120 "⊢ᵍᶜ[Grz]! " S:121 => GentzenWithCutProof S

abbrev GentzenWithCutProvable (S : Sequent α) : Prop := Nonempty (⊢ᵍᶜ[Grz]! S)
notation:120 "⊢ᵍᶜ[Grz] " S:121 => GentzenWithCutProvable S


def GentzenWithCutProof.ofGentzenProof {S : Sequent α} : ⊢ᵍ[Grz]! S → ⊢ᵍᶜ[Grz]! S
| .axm A => .axm A
| .botL => .botL
| .wkL h h' => .wkL (ofGentzenProof h) h'
| .wkR h h' => .wkR (ofGentzenProof h) h'
| .impL h₁ h₂ => .impL (ofGentzenProof h₁) (ofGentzenProof h₂)
| .impR h => .impR (ofGentzenProof h)
| .boxT h => .boxT (ofGentzenProof h)
| .boxGrz h => .boxGrz (ofGentzenProof h)

namespace GentzenWithCutProvable

variable {S : Sequent α} {A B : Formula α} {Γ Γ' Γ₁ Γ₂ Δ Δ' Δ₁ Δ₂ : FormulaFinset α}

theorem of_without_cut : ⊢ᵍ[Grz] S → ⊢ᵍᶜ[Grz] S := λ ⟨p⟩ => ⟨GentzenWithCutProof.ofGentzenProof p⟩

lemma axm (A : Formula α) : ⊢ᵍᶜ[Grz] ({A} ⟹ {A}) := ⟨GentzenWithCutProof.axm A⟩
lemma botL : ⊢ᵍᶜ[Grz] ({⊥} ⟹ ∅ : Sequent α) := ⟨GentzenWithCutProof.botL⟩
lemma wkL (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ') : ⊢ᵍᶜ[Grz] (Γ' ⟹ Δ) := ⟨GentzenWithCutProof.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Δ ⊆ Δ') : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ') := ⟨GentzenWithCutProof.wkR h.some h'⟩
lemma impL (h₁ : ⊢ᵍᶜ[Grz] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ[Grz] ((insert (A 🡒 B) Γ) ⟹ Δ) := ⟨GentzenWithCutProof.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ[Grz] ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍᶜ[Grz] (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨GentzenWithCutProof.impR h.some⟩
lemma boxT (h : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ[Grz] (insert (□B) Γ ⟹ Δ) := ⟨GentzenWithCutProof.boxT h.some⟩
lemma boxGrz (h : ⊢ᵍᶜ[Grz] (insert (□(A 🡒 □A)) (□Γ) ⟹ {A})) : ⊢ᵍᶜ[Grz] (□Γ ⟹ {□A}) := ⟨GentzenWithCutProof.boxGrz h.some⟩
lemma cut (h₁ : ⊢ᵍᶜ[Grz] (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᵍᶜ[Grz] (insert A Γ₂ ⟹ Δ₂)) : ⊢ᵍᶜ[Grz] (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := ⟨GentzenWithCutProof.cut h₁.some h₂.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent α) → ⊢ᵍᶜ[Grz] S → Prop}
  (axm : ∀ A : Formula α, motive ({A} ⟹ {A}) (GentzenWithCutProvable.axm A))
  (botL : motive ({⊥} ⟹ ∅ : Sequent α) GentzenWithCutProvable.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ Δ Δ'} (h : ⊢ᵍᶜ[Grz] (Γ ⟹ Δ)) (h' : Δ ⊆ Δ'), motive (Γ ⟹ Δ) h → motive (Γ ⟹ Δ') (wkR h h'))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍᶜ[Grz] (Γ ⟹ insert A Δ)) (h₂ : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ insert A Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive ((insert (A 🡒 B) Γ) ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ Δ A B} (h : ⊢ᵍᶜ[Grz] ((insert A Γ) ⟹ (insert B Δ))),
    motive ((insert A Γ) ⟹ (insert B Δ)) h → motive (Γ ⟹ (insert (A 🡒 B) Δ)) (impR h)
  )
  (boxT : ∀ {Γ : FormulaFinset α} {Δ B} (h : ⊢ᵍᶜ[Grz] (insert B Γ ⟹ Δ)),
    motive (insert B Γ ⟹ Δ) h → motive (insert (□B) Γ ⟹ Δ) (boxT h)
  )
  (boxGrz : ∀ {Γ : FormulaFinset α} {A} (h : ⊢ᵍᶜ[Grz] (insert (□(A 🡒 □A)) (□Γ) ⟹ {A})),
    motive (insert (□(A 🡒 □A)) (□Γ) ⟹ {A}) h → motive (□Γ ⟹ {□A}) (boxGrz h)
  )
  (cut : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A}
    (h₁ : ⊢ᵍᶜ[Grz] (Γ₁ ⟹ insert A Δ₁)) (h₂ : ⊢ᵍᶜ[Grz] (insert A Γ₂ ⟹ Δ₂)),
    (motive (Γ₁ ⟹ insert A Δ₁) h₁) → (motive (insert A Γ₂ ⟹ Δ₂) h₂) →
    motive (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) (GentzenWithCutProvable.cut h₁ h₂)
  )
  : ∀ {S : Sequent α} (h : ⊢ᵍᶜ[Grz] S), motive S h := by
    rintro S ⟨h⟩;
    induction h with
    | axm A => apply axm;
    | botL => apply botL;
    | wkL h h' ih => apply wkL ⟨h⟩ h' ih;
    | wkR h h' ih => apply wkR ⟨h⟩ h' ih;
    | cut h₁ h₂ ih₁ ih₂ => apply cut ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impL h₁ h₂ ih₁ ih₂ => apply impL ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impR h ih => apply impR ⟨h⟩ ih;
    | boxT h ih => apply boxT ⟨h⟩ ih;
    | boxGrz h ih => apply boxGrz ⟨h⟩ ih;

/-- One direction of the deduction theorem for the cut-full calculus. -/
theorem deductionTheorem (π : ⊢ᵍᶜ[Grz] (insert A Γ ⟹ {B})) : ⊢ᵍᶜ[Grz] (Γ ⟹ {A 🡒 B}) := by
  rw [(show ({A 🡒 B} : FormulaFinset α) = insert (A 🡒 B) ∅ by grind)];
  apply impR;
  rwa [(show insert B (∅ : FormulaFinset α) = {B} by grind)];

/-- The standard form of the Grz axiom, via a cut on `□A` between `seq_grz_box` and `seq_T`. -/
theorem grz_std {A : Formula α} : ⊢ᵍᶜ[Grz] (∅ ⟹ {□(□(A 🡒 □A) 🡒 A) 🡒 A}) := by
  have h₁ : ⊢ᵍᶜ[Grz] ({□(□(A 🡒 □A) 🡒 A)} ⟹ insert (□A) ∅) := by
    rw [(show insert (□A) (∅ : FormulaFinset α) = {□A} by grind)];
    exact of_without_cut ProvableGentzen.seq_grz_box;
  have h₂ : ⊢ᵍᶜ[Grz] (insert (□A) (∅ : FormulaFinset α) ⟹ {A}) := by
    rw [(show insert (□A) (∅ : FormulaFinset α) = {□A} by grind)];
    exact of_without_cut ProvableGentzen.seq_T;
  have h₃ := cut h₁ h₂;
  rw [(show ({□(□(A 🡒 □A) 🡒 A)} ∪ (∅ : FormulaFinset α)) = {□(□(A 🡒 □A) 🡒 A)} by grind),
      (show ((∅ : FormulaFinset α) ∪ {A}) = {A} by grind)] at h₃;
  exact deductionTheorem h₃;

end GentzenWithCutProvable


namespace ProvableGentzen

variable {S : Sequent α} {A B : Formula α}

/-- Cut-elimination for `Grz`. To be proved semantically via Kripke completeness, as in
    `LogicGL.ProvableGentzen.of_with_cut`.
    - [Avr84, §I] (semantic proof)
    - [BG86] (syntactic proof) -/
theorem of_with_cut {S : Sequent α} : ⊢ᵍᶜ[Grz] S → ⊢ᵍ[Grz] S := sorry
alias cut_elimination := of_with_cut

/-- Modus ponens for `Grz`, via the cut system. -/
theorem mdp : ⊢ᵍ[Grz] (∅ ⟹ {A 🡒 B}) → ⊢ᵍ[Grz] (∅ ⟹ {A}) → ⊢ᵍ[Grz] (∅ ⟹ {B}) := λ p q => by
  replace p : ⊢ᵍ[Grz] ((∅ : FormulaFinset α) ⟹ insert (A 🡒 B) ∅) := by
    rwa [(show insert (A 🡒 B) (∅ : FormulaFinset α) = {A 🡒 B} by grind)];
  replace q : ⊢ᵍ[Grz] ((∅ : FormulaFinset α) ⟹ insert A ∅) := by
    rwa [(show insert A (∅ : FormulaFinset α) = {A} by grind)];
  have himpL : ⊢ᵍ[Grz] (insert (A 🡒 B) (insert A ∅) ⟹ {B}) :=
    LogicGrz.ProvableGentzen.impL (LogicGrz.ProvableGentzen.union A) (LogicGrz.ProvableGentzen.union B);
  have r : ⊢ᵍᶜ[Grz] (insert A (∅ : FormulaFinset α) ⟹ {B}) := by
    have h := GentzenWithCutProvable.cut (GentzenWithCutProvable.of_without_cut p) (GentzenWithCutProvable.of_without_cut himpL);
    rwa [(show ((∅ : FormulaFinset α) ∪ insert A ∅) = insert A ∅ by grind),
         (show ((∅ : FormulaFinset α) ∪ {B}) = {B} by grind)] at h;
  have h := GentzenWithCutProvable.cut (GentzenWithCutProvable.of_without_cut q) r;
  rw [(show ((∅ : FormulaFinset α) ∪ (∅ : FormulaFinset α)) = ∅ by grind),
      (show ((∅ : FormulaFinset α) ∪ {B}) = {B} by grind)] at h;
  exact cut_elimination h;

end ProvableGentzen

end LogicGrz

end
