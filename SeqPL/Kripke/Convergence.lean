module

public import SeqPL.Kripke.Basic

@[expose]
public section

variable [Nonempty κ]

namespace Model

/-- `LogicGLPoint2` frame class: transitive, converse well-founded, and piecewise
convergent (weakly confluent), i.e. any two distinct successors of a common world
have a common successor. -/
class IsGLPoint2 (M : Model κ α) extends Model.IsGL M where
  p_convergent : ∀ {x y z : M.World}, x ≺ y → x ≺ z → y ≠ z → ∃ u, y ≺ u ∧ z ≺ u

/-- Finite `LogicGLPoint2` frame class: finite, transitive, irreflexive, and piecewise
convergent (weakly confluent), i.e. any two distinct successors of a common world
have a common successor. -/
class IsFiniteGLPoint2 (M : Model κ α) extends Model.IsFiniteGL M where
  p_convergent : ∀ {x y z : M.World}, x ≺ y → x ≺ z → y ≠ z → ∃ u, y ≺ u ∧ z ≺ u

variable {M : Model κ α}

instance [M.IsFiniteGLPoint2] : M.IsGLPoint2 where
  p_convergent := IsFiniteGLPoint2.p_convergent

lemma p_convergent [M.IsGLPoint2] {x y z : M.World} :
    x ≺ y → x ≺ z → y ≠ z → ∃ u, y ≺ u ∧ z ≺ u :=
  IsGLPoint2.p_convergent

namespace World

variable {A B : Formula α}

/-- The weak convergence axiom `.2` (`WeakPoint2`) holds at every world of a
piecewise convergent model. -/
lemma forces_axiomWeakPoint2 [M.IsGLPoint2] {x : M.World} :
    x ⊩ (◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B) := by
  intro h;
  obtain ⟨y, Rxy, hy⟩ := forces_dia.mp h;
  obtain ⟨hyA, hyB⟩ := forces_and.mp hy;
  intro z Rxz;
  apply forces_or.mpr;
  by_cases hyz : y = z;
  . right; subst hyz; exact hyB;
  . obtain ⟨u, Ryu, Rzu⟩ := p_convergent Rxy Rxz hyz;
    left;
    exact forces_dia.mpr ⟨u, Rzu, hyA u Ryu⟩;

end World

/-- The weak convergence axiom `.2` (`WeakPoint2`) is valid on piecewise
convergent models. -/
lemma validate_axiomWeakPoint2 [M.IsGLPoint2] {A B : Formula α} :
    M ⊧ (◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B) :=
  fun _ => World.forces_axiomWeakPoint2

end Model

end
