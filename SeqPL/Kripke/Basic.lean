module

public import SeqPL.Gentzen.Basic

@[expose]
public section

structure Model (κ : Type*) [Nonempty κ] where
  Rel' : κ → κ → Prop
  Val : κ → ℕ → Prop

namespace Model

variable [Nonempty κ] {M : Model κ}

abbrev World (_ : Model κ) := κ
abbrev Rel {M : Model κ} : M.World → M.World → Prop := M.Rel'
infixl:60 " ≺ " => Rel


abbrev _root_.IsConverseWellFounded (α) (R : α → α → Prop) := IsWellFounded α (λ x y => R y x)

lemma has_terminal [IsConverseWellFounded _ M.Rel] : ∀ (X : Set M.World), Set.Nonempty X → ∃ t ∈ X, ∀ x ∈ X, ¬(t ≺ x) :=
  WellFounded.wellFounded_iff_has_min.mp (by apply IsWellFounded.wf)

class IsGL (M : Model κ) extends IsTrans _ M.Rel, IsConverseWellFounded _ M.Rel

class IsFiniteGL (M : Model κ) extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  finite : Finite M.World

instance [M.IsFiniteGL] : M.IsGL where
  wf := by apply @Finite.wellFounded_of_trans_of_irrefl M.World (IsFiniteGL.finite);

end Model




variable [Nonempty κ] {M : Model κ} {A B : Formula} {Γ Γ' Δ Δ' : FormulaFinset}

namespace Model.World

variable {M : Model κ} {x : M.World} {A B : Formula}

@[grind]
def Forces (x : M.World) : Formula → Prop
| #a    => M.Val x a
| ⊥     => False
| A 🡒 B => Forces x A → Forces x B
| □A    => ∀ y, x ≺ y → Forces y A
infix:55 " ⊩ " => Forces

abbrev NotForces (x : M.World) (A : Formula) : Prop := ¬x ⊩ A
infix:55 " ⊮ " => NotForces


@[grind =]
lemma iff_not_forced_box {A : Formula} : ¬x ⊩ □A ↔ ∃ y, x ≺ y ∧ ¬y ⊩ A := by grind;

@[simp, grind .]
lemma not_forces_bot : x ⊮ ⊥ := by grind;


@[grind]
def ForcesSet (x : M.World) (Γ : FormulaFinset) : Prop := ∀ A ∈ Γ, x ⊩ A
infix:55 " ⊩ " => ForcesSet

end Model.World



namespace Model

@[grind]
def Validate (M : Model κ) (A : Formula) : Prop := ∀ x : M.World, x ⊩ A
infix:50 " ⊧ " => Model.Validate

end Model


end
