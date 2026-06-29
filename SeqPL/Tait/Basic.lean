module

public import SeqPL.DFormula.Basic

@[expose]
public section

variable {α : Type u} [DecidableEq α]

/-
inductive ProofTait : DFormulaFinset α → Type u
| axm {a : α} : ProofTait $ {(♯a), (♭a)}
| bot         : ProofTait $ {⊥}
| or  {Γ A B} : (ProofTait $ insert A $ insert B $ Γ) → (ProofTait $ insert (A ⋎ B) Γ)
| and {Γ A B} : (ProofTait $ insert A Γ) → (ProofTait $ insert B Γ) → (ProofTait $ insert (A ⋏ B) Γ)
-/

inductive ProofTait : DFormulaList α → Type u
| axm {a : α} : ProofTait $ [(♯a), (♭a)]
| bot         : ProofTait $ [⊥]
| or  {Γ A B} : (ProofTait $ insert A $ insert B $ Γ) → (ProofTait $ insert (A ⋎ B) Γ)
| and {Γ A B} : (ProofTait $ insert A Γ) → (ProofTait $ insert B Γ) → (ProofTait $ insert (A ⋏ B) Γ)


end
