module

public import SeqPL.Kripke.Basic
public import SeqPL.Kripke.Cone

@[expose]
public section

variable [Nonempty κ]

namespace Model

/-- `GLPoint3` frame class: transitive, converse well-founded, and linear (weakly
connected), i.e. any two successors of a common world are comparable or equal. -/
class IsGLPoint3 (M : Model κ α) extends Model.IsGL M where
  linear : ∀ {x y z : M.World}, x ≺ y → x ≺ z → y ≺ z ∨ y = z ∨ z ≺ y

/-- Finite `GLPoint3` frame class: finite, transitive, irreflexive, and linear (weakly
connected), i.e. any two successors of a common world are comparable or equal. -/
class IsFiniteGLPoint3 (M : Model κ α) extends Model.IsFiniteGL M where
  linear : ∀ {x y z : M.World}, x ≺ y → x ≺ z → y ≺ z ∨ y = z ∨ z ≺ y

variable {M : Model κ α}

instance [M.IsFiniteGLPoint3] : M.IsGLPoint3 where
  linear := IsFiniteGLPoint3.linear

lemma linear [M.IsGLPoint3] {x y z : M.World} :
    x ≺ y → x ≺ z → y ≺ z ∨ y = z ∨ z ≺ y :=
  IsGLPoint3.linear

instance [M.IsFiniteGLPoint3] {r : M.World} :
    (toRootedModel M r).toModel.IsFiniteGLPoint3 where
  linear := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ Rxy Rxz;
    simp_all only [Model.Rel, toRootedModel];
    rcases Model.linear Rxy Rxz with (Ryz | rfl | Rzy);
    . exact Or.inl Ryz;
    . exact Or.inr (Or.inl rfl);
    . exact Or.inr (Or.inr Rzy);

namespace World

variable {A B : Formula α}

/-- The weak linearity axiom `.3` (`WeakPoint3`) holds at every world of a linear
model. -/
lemma forces_axiomWeakPoint3 [M.IsGLPoint3] {x : M.World} :
    x ⊩ (□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A)) := by
  by_contra hC;
  obtain ⟨h₁, h₂⟩ := not_forces_or.mp hC;
  obtain ⟨y, Rxy, hy⟩ := not_forces_box.mp h₁;
  obtain ⟨z, Rxz, hz⟩ := not_forces_box.mp h₂;
  obtain ⟨hyA, hyB⟩ := not_forces_imp.mp hy;
  obtain ⟨hzB, hzA⟩ := not_forces_imp.mp hz;
  obtain ⟨hyA₁, hyA₂⟩ := forces_boxdot.mp hyA;
  obtain ⟨hzB₁, hzB₂⟩ := forces_boxdot.mp hzB;
  rcases linear Rxy Rxz with (Ryz | rfl | Rzy);
  . exact hzA (hyA₂ z Ryz);
  . exact hzA hyA₁;
  . exact hyB (hzB₂ y Rzy);

end World

/-- The weak linearity axiom `.3` (`WeakPoint3`) is valid on linear models. -/
lemma validate_axiomWeakPoint3 [M.IsGLPoint3] {A B : Formula α} :
    M ⊧ (□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A)) :=
  fun _ => World.forces_axiomWeakPoint3

end Model

end
