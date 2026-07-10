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

/-- Negated form of `GLPoint3.ProvableGentzen`. Declared once here so that files depending on
`GLPoint3.Basic` (both `Completeness` and `Witness`) share a single notation instead of each
redeclaring their own copy, which would make `⊬ᵍ³` ambiguous whenever both are imported together. -/
prefix:120 "⊬ᵍ³ " => fun S => ¬⊢ᵍ³ S

namespace ProvableGentzen

variable {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α}

lemma axm (A : Formula α) : ⊢ᵍ³ ({A} ⟹ {A}) := ⟨ProofGentzen.axm A⟩

lemma union (A : Formula α) (hΓ : A ∈ Γ := by grind) (hΔ : A ∈ Δ := by grind) : ⊢ᵍ³ (Γ ⟹ Δ) :=
  ⟨ProofGentzen.wkR (ProofGentzen.wkL (ProofGentzen.axm A) (by grind)) (by grind)⟩

lemma union' (A : Formula α) {S : Sequent α} (hΓ : A ∈ S.ant := by grind) (hΔ : A ∈ S.suc := by grind) : ⊢ᵍ³ S := union A hΓ hΔ

lemma botL : ⊢ᵍ³ ({⊥} ⟹ (∅ : FormulaFinset α)) := ⟨ProofGentzen.botL⟩

@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ³ (Γ ⟹ Δ) :=
  ⟨ProofGentzen.wkR (Δ := ∅) (ProofGentzen.wkL ProofGentzen.botL (by grind)) (by grind)⟩

@[grind =>] lemma botL_mem' (S : Sequent α) (h : ⊥ ∈ S.ant := by grind) : ⊢ᵍ³ S := botL_mem h

lemma wkL (π : ⊢ᵍ³ (Γ ⟹ Δ)) (h : Γ ⊆ Γ') : ⊢ᵍ³ (Γ' ⟹ Δ) := ⟨ProofGentzen.wkL π.some h⟩

lemma wkR (π : ⊢ᵍ³ (Γ ⟹ Δ)) (h : Δ ⊆ Δ') : ⊢ᵍ³ (Γ ⟹ Δ') := ⟨ProofGentzen.wkR π.some h⟩

lemma wk (π : ⊢ᵍ³ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᵍ³ (Γ' ⟹ Δ') := wkR (wkL π hΓ) hΔ

lemma impL (π₁ : ⊢ᵍ³ (Γ ⟹ insert A Δ)) (π₂ : ⊢ᵍ³ (insert B Γ ⟹ Δ)) : ⊢ᵍ³ ((insert (A 🡒 B) Γ) ⟹ Δ) :=
  ⟨ProofGentzen.impL π₁.some π₂.some⟩

lemma impR (π : ⊢ᵍ³ ((insert A Γ) ⟹ (insert B Δ))) : ⊢ᵍ³ (Γ ⟹ (insert (A 🡒 B) Δ)) := ⟨ProofGentzen.impR π.some⟩

lemma boxGLPoint3 (hΔ : Δ.Nonempty)
    (h : ∀ S : FormulaFinset α, S ⊆ Δ → S.Nonempty →
      ⊢ᵍ³ ((Γ.box ∪ Γ ∪ S.box) ⟹ (S ∪ (Δ \ S).box))) :
    ⊢ᵍ³ (Γ.box ⟹ Δ.box) :=
  ⟨ProofGentzen.boxGLPoint3 hΔ (fun S hS hSne => (h S hS hSne).some)⟩

/-- Embedding of the `GL` sequent calculus into the `GL.3` sequent calculus: every `GL`-provable
sequent is `GL.3`-provable, since `boxGL` is the special case of `boxGLPoint3` with `Δ = {A}`. -/
lemma of_gentzenGL {S : Sequent α} (h : ⊢ᵍ S) : ⊢ᵍ³ S := by
  induction h with
  | axm A => exact axm A
  | botL => exact botL
  | wkL _ h' ih => exact wkL ih h'
  | wkR _ h' ih => exact wkR ih h'
  | impL _ _ ih₁ ih₂ => exact impL ih₁ ih₂
  | impR _ ih => exact impR ih
  | @boxGL Γ A _ ih =>
    have hbox : ({A} : FormulaFinset α).box = {□A} := by simp [FormulaFinset.box]
    rw [← hbox]
    apply boxGLPoint3 (Δ := {A}) (by simp)
    intro S hS hSne
    obtain rfl : S = {A} := by
      rcases Finset.subset_singleton_iff.mp hS with h' | h'
      · exact absurd h' hSne.ne_empty
      · exact h'
    have e1 : Γ.box ∪ Γ ∪ ({A} : FormulaFinset α).box = insert (□A) (Γ ∪ Γ.box) := by
      rw [hbox]; grind
    have e2 : ({A} : FormulaFinset α) ∪ (({A} : FormulaFinset α) \ {A}).box = {A} := by simp
    rw [e1, e2]
    exact ih

end ProvableGentzen

end GLPoint3

end
