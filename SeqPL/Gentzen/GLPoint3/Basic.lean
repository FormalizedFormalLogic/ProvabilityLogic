module

public import SeqPL.Gentzen.Basic

@[expose]
public section

variable {α : Type u} [DecidableEq α]

namespace GLPoint3

/-!
Sequent calculus for `LogicGLPoint3` (`GL.3`), obtained from the sequent calculus for `GL`
(`SeqPL.Gentzen.Basic`) by generalising `boxGL` to the rule `boxGLPoint3`: given a linear
frame, two successors of a common world are comparable, so a boxed succedent `□Δ` can be
established by exhausting every nonempty split `S ⊆ Δ`.
-/

inductive ProofGentzen : Sequent α → Type u
| axm (A) : ProofGentzen ({A} ⟹ {A})
| botL : ProofGentzen ({⊥} ⟹ (∅ : FormulaFinset α))
| wkL  {Γ Γ' Δ}  : ProofGentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹ Δ)
| wkR  {Γ Δ Δ'}  : ProofGentzen (Γ ⟹ Δ) → (_ : Δ ⊆ Δ' := by grind) → ProofGentzen (Γ ⟹ Δ')
| impL {Γ Δ A B} : ProofGentzen (Γ ⟹ (insert A Δ)) → ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen ((insert (A 🡒 B) Γ) ⟹ Δ)
| impR {Γ Δ A B} : ProofGentzen ((insert A Γ) ⟹ (insert B Δ)) → ProofGentzen (Γ ⟹ (insert (A 🡒 B) Δ))
/-- `□GL.3`: the linear-frame generalisation of `boxGL`. For every nonempty `S ⊆ Δ`, the
sequent `□Γ, Γ, □S ⟹ S, □(Δ \ S)` must hold; taking `Δ = {A}` recovers `boxGL`. -/
| boxGLPoint3 {Γ Δ} (hΔ : Δ.Nonempty) :
    (∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty →
      ProofGentzen ((Γ.box ∪ Γ ∪ S.box) ⟹ (S ∪ (Δ \ S).box))) →
    ProofGentzen (Γ.box ⟹ Δ.box)
prefix:120 "⊢ᵍ³! " => ProofGentzen


abbrev ProvableGentzen (S : Sequent α) : Prop := Nonempty (ProofGentzen S)
prefix:120 "⊢ᵍ³ " => ProvableGentzen

end GLPoint3

end
