module

public import ProvabilityLogic.Logic.Grz.Basic
public import ProvabilityLogic.Logic.S.Boxdot

@[expose] public section

variable {F : Frame}


open Formula (boxdotTranslate)

namespace Model

variable [Nonempty κ]

abbrev irreflGen (M : Model κ α) : Model κ α := ⟨Rel.IrreflGen M.Rel, M.Val⟩

variable {M : Model κ α}

lemma World.irreflGen_forces_boxdot [M.IsGrz]
  : (x ⊩[M.irreflGen] (Aᵇ)) ↔ (x ⊩[M] A) := by
  induction A generalizing x with
  | box A ihA =>
    constructor;
    . intro h y Rxy;
      by_cases exy : x = y;
      . subst exy;
        exact ihA |>.mp $ Model.World.forces_boxdot.mp h |>.1;
      . exact ihA |>.mp $ Model.World.forces_boxdot.mp h |>.2 y ⟨Rxy, exy⟩;
    . intro h;
      apply Model.World.forces_boxdot.mpr;
      constructor;
      . apply ihA |>.mpr;
        apply h;
        apply Std.Refl.refl;
      . intro y Rxy;
        apply ihA |>.mpr;
        exact h _ Rxy.1;
  | _ => grind;

/-- Semantic core of the boxdot translation of the Grz axiom: `⊡(⊡(B 🡒 ⊡B) 🡒 B) 🡒 B` is
valid at every point of every `GL` model, for an arbitrary formula `B`. Proved by converse
well-founded induction on the accessibility relation; this is the folklore semantic argument
underlying the Hilbert-style derivation `boxdotGrz_of_L` in the modal-logic literature on
the Grzegorczyk axiom. -/
lemma World.forces_boxdotGrz [M.IsGL] {B : Formula α} {x : M.World} :
    x ⊩[_] (⊡(⊡(B 🡒 ⊡B) 🡒 B) 🡒 B) := by
  induction x using WellFounded.induction (IsConverseWellFounded.cwf (rel := M.Rel)) with
  | _ x ih =>
    intro hxD;
    obtain ⟨h1, h2⟩ := Model.World.forces_boxdot.mp hxD;
    have key : ∀ z, x ≺ z → z ⊩[_] B := by
      intro z hxz;
      apply ih z hxz;
      apply Model.World.forces_boxdot.mpr;
      exact ⟨h2 z hxz, fun w hzw => h2 w (IsTrans.trans x z w hxz hzw)⟩;
    apply h1;
    apply Model.World.forces_boxdot.mpr;
    constructor;
    . intro hxB;
      exact Model.World.forces_boxdot.mpr ⟨hxB, key⟩;
    . intro y hxy hyB;
      exact Model.World.forces_boxdot.mpr ⟨hyB, fun z hyz => key z (IsTrans.trans x y z hxy hyz)⟩;

end Model


variable [DecidableEq α] {A : Formula α}

lemma provable_boxdot_GL_of_provable_Grz : A ∈ LogicGrz → Aᵇ ∈ LogicGL := by
  intro h;
  replace h := LogicGrz.iff_provableHilbert.mp h;
  induction h with
  | modal4 =>
    apply LogicGL.iff_forces.mpr;
    intro _ _ _ _ x h;
    obtain ⟨h₁, h₂⟩ := Model.World.forces_and.mp h;
    apply Model.World.forces_and.mpr;
    constructor;
    . assumption;
    . intro y Rxy;
      apply Model.World.forces_and.mpr;
      constructor;
      . exact h₂ _ Rxy;
      . intro z Ryz;
        apply h₂;
        trans y <;> assumption;
  | @modalGrz A =>
    simp only [boxdotTranslate];
    apply LogicGL.iff_forces.mpr;
    intro κ _ M _ x;
    exact Model.World.forces_boxdotGrz;
  | modalK | modalT => apply LogicGL.iff_forces.mpr; grind;
  | _ => grind;

lemma provable_Grz_of_provable_boxdot_GL :  Aᵇ ∈ LogicGL → A ∈ LogicGrz := by
  intro h;
  apply LogicGrz.iff_forces.mpr;
  intro κ _ M hM x;
  replace h := @LogicGL.iff_forces.mp h κ _ M.irreflGen ?_ x;
  . exact Model.World.irreflGen_forces_boxdot |>.mp h;
  . exact {
      finite := hM.finite,
      trans := by
        rintro x y z ⟨Rxy, hxy⟩ ⟨Ryz, hyz⟩;
        constructor;
        . exact hM.trans _ _ _ Rxy Ryz;
        . by_contra!;
          subst this;
          have := hM.toAntisymm.antisymm _ _ Rxy Ryz;
          contradiction;
    }

theorem iff_provable_boxdot_GL_provable_Grz : Aᵇ ∈ LogicGL ↔ A ∈ LogicGrz := ⟨
  provable_Grz_of_provable_boxdot_GL,
  provable_boxdot_GL_of_provable_Grz
⟩

theorem iff_provable_boxdot_S_provable_Grz : Aᵇ ∈ LogicS ↔ A ∈ LogicGrz :=
  Iff.trans LogicS.iff_provable_boxdot_GL_provable_boxdot_S.symm
    iff_provable_boxdot_GL_provable_Grz

end
