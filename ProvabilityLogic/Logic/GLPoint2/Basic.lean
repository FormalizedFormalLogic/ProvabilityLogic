module

public import ProvabilityLogic.Logic.GLPoint3.Basic
public import ProvabilityLogic.Kripke.Convergence

@[expose]
public section

/-- `LogicGLPoint2`: the normal extension of `GL` by the weak convergence axiom `.2`,
i.e. `◇(□A ⋏ B) 🡒 □(◇A ⋎ B)`. -/
abbrev LogicGLPoint2 {α} : Logic α := LogicGL ⊕ᴸ { (◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B) | (A) (B) }

open LogicGL

namespace LogicGLPoint2

lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicGLPoint2 :=
  Logic.sumNormal.mem₁ h

lemma provable_axiomWeakPoint2 {A B : Formula α} :
  ((◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B)) ∈ LogicGLPoint2 :=
  Logic.sumNormal.mem₂ ⟨A, B, rfl⟩

section

/-- Intrinsic definition of `LogicGLPoint2` avoiding `subst`, for
`LogicGLPoint2.substlessInduction`. -/
protected inductive substless : Logic α
  | provable_GL {A} : A ∈ LogicGL → LogicGLPoint2.substless A
  | axiomWeakPoint2 (A B : Formula α) : LogicGLPoint2.substless ((◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B))
  | mdp {A B} : LogicGLPoint2.substless (A 🡒 B) → LogicGLPoint2.substless A → LogicGLPoint2.substless B
  | nec {A} : LogicGLPoint2.substless A → LogicGLPoint2.substless (□A)

private lemma substless.eq_LogicGLPoint2 : LogicGLPoint2.substless (α := α) = LogicGLPoint2 := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | provable_GL h => exact provable_of_provable_GL h;
    | axiomWeakPoint2 A B => exact provable_axiomWeakPoint2;
    | mdp _ _ ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA;
    | nec _ ih => exact Logic.sumNormal.nec ih;
  . intro h;
    induction h with
    | mem₁ h => exact LogicGLPoint2.substless.provable_GL h;
    | mem₂ h =>
      obtain ⟨B, C, rfl⟩ := h;
      exact LogicGLPoint2.substless.axiomWeakPoint2 B C;
    | mdp _ _ ihAB ihA => exact LogicGLPoint2.substless.mdp ihAB ihA;
    | nec _ ih => exact LogicGLPoint2.substless.nec ih;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | provable_GL h => exact LogicGLPoint2.substless.provable_GL (ProvableHilbert.subst h);
      | axiomWeakPoint2 B C => exact LogicGLPoint2.substless.axiomWeakPoint2 _ _;
      | mdp _ _ ihAB ihA => exact LogicGLPoint2.substless.mdp ihAB ihA;
      | nec _ ih => exact LogicGLPoint2.substless.nec ih;

private lemma substless.toLogicGLPoint2 {A : Formula α} (h : LogicGLPoint2.substless A) : A ∈ LogicGLPoint2 :=
  substless.eq_LogicGLPoint2 ▸ h

private lemma substless.ofLogicGLPoint2 {A : Formula α} (h : A ∈ LogicGLPoint2) : LogicGLPoint2.substless A :=
  substless.eq_LogicGLPoint2.symm ▸ h

/-- Induction principle for `LogicGLPoint2` avoiding `subst`: it suffices to cover the
GL part, the axiom `.2` instances, modus ponens, and necessitation. -/
protected lemma substlessInduction
  {motive : (A : Formula α) → A ∈ LogicGLPoint2 → Prop}
  (provable_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (axiomWeakPoint2 : ∀ {A B}, motive ((◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B)) provable_axiomWeakPoint2)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicGLPoint2} → {hA : A ∈ LogicGLPoint2} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumNormal.mdp hAB hA))
    (nec : ∀ {A}, {hA : A ∈ LogicGLPoint2} → motive A hA → motive (□A) (Logic.sumNormal.nec hA)) :
    ∀ {A}, (h : A ∈ LogicGLPoint2) → motive A h := by
  intro A h;
  induction substless.ofLogicGLPoint2 h with
  | provable_GL hg => exact provable_GL hg;
  | axiomWeakPoint2 A B => exact axiomWeakPoint2;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := substless.toLogicGLPoint2 hAB) (hA := substless.toLogicGLPoint2 hA) (ihAB _) (ihA _);
  | nec hA ihA =>
    exact nec (hA := substless.toLogicGLPoint2 hA) (ihA _);

end

universe u
variable {α : Type u}

open Model Model.World

lemma sound [DecidableEq α] {κ : Type u} [Nonempty κ] {M : Model κ α}
  [M.IsFiniteGLPoint2] {A : Formula α} (h : A ∈ LogicGLPoint2) : M ⊧ A := by
  induction h using LogicGLPoint2.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.finite_soundness h M;
  | axiomWeakPoint2 => exact validate_axiomWeakPoint2;
  | mdp ihAB ihA => exact fun x => (ihAB x) (ihA x);
  | nec ih => exact fun x y _ => ih y;

variable [DecidableEq α] {A B C : Formula α}

omit [DecidableEq α] in
lemma imp_trans (hAB : (A 🡒 B) ∈ @LogicGLPoint2 α) (hBC : (B 🡒 C) ∈ LogicGLPoint2) :
  (A 🡒 C) ∈ LogicGLPoint2 :=
  Logic.sumNormal.imp_trans LogicGL.imp_trans hAB hBC

lemma provable_boxboxbot : (□^[2]⊥) ∈ @LogicGLPoint2 α := by
  show (□□⊥) ∈ @LogicGLPoint2 α;
  -- `∼□⊥` is `□⊥ 🡒 ⊥` definitionally.
  have h₁ : (□(∼□⊥) 🡒 □□⊥) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL <|
      ProvableHilbert.impTrans (ProvableHilbert.modalL (A := ⊥)) ProvableHilbert.modal4;
  have s1 : (◇□⊥ 🡒 ◇(□(∼□⊥) ⋏ □⊥)) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    apply LogicGL.iff_forces.mpr;
    intro κ _ M _ x;
    apply forces_imp.mpr;
    by_cases h : x ⊩[_] ◇□⊥;
    . right;
      obtain ⟨y, hxy, hy⟩ := forces_dia.mp h;
      apply forces_dia.mpr;
      use y, hxy;
      apply forces_and.mpr;
      and_intros;
      . apply forces_box.mpr;
        intro z hyz;
        exact absurd (forces_box.mp hy z hyz) not_forces_bot;
      . exact hy;
    . left; exact h;
  have s2 : (◇(□(∼□⊥) ⋏ □⊥) 🡒 □(◇(∼□⊥) ⋎ □⊥)) ∈ @LogicGLPoint2 α :=
    provable_axiomWeakPoint2;
  have s3 : (□(◇(∼□⊥) ⋎ □⊥) 🡒 □(□□⊥ 🡒 □⊥)) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    apply LogicGL.iff_forces.mpr;
    grind;
  have s4 : (□(□□⊥ 🡒 □⊥) 🡒 □□⊥) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.modalL (A := □⊥));
  have h₂ : (◇□⊥ 🡒 □□⊥) ∈ @LogicGLPoint2 α :=
    imp_trans (imp_trans (imp_trans s1 s2) s3) s4;
  -- `◇□⊥` is `∼□(∼□⊥)` definitionally.
  have bridge : (∼◇□⊥ 🡒 □(∼□⊥)) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.dne (A := □(∼□⊥)));
  have T : ((□(∼□⊥) 🡒 □□⊥) 🡒 (◇□⊥ 🡒 □□⊥) 🡒 (∼◇□⊥ 🡒 □(∼□⊥)) 🡒 □□⊥) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    apply LogicGL.iff_forces.mpr;
    grind;
  exact Logic.sumNormal.mdp (Logic.sumNormal.mdp (Logic.sumNormal.mdp T h₁) h₂) bridge;

lemma core_diamond : (◇(C ⋏ □C) 🡒 □C) ∈ @LogicGLPoint2 α := by
  have hLöb : (□(□(∼(C ⋏ □C)) 🡒 ∼(C ⋏ □C)) 🡒 □(∼(C ⋏ □C))) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.modalL (A := ∼(C ⋏ □C)));
  have hFour : (□(□C 🡒 □□C)) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.nec ProvableHilbert.modal4);
  have hMeta : ((□(□(∼(C ⋏ □C)) 🡒 ∼(C ⋏ □C)) 🡒 □(∼(C ⋏ □C))) 🡒 □(□C 🡒 □□C) 🡒 ◇(C ⋏ □C) 🡒 ◇(□⊥ ⋏ C)) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    apply LogicGL.iff_forces.mpr;
    intro κ _ M _ x hL h4 hdia;
    obtain ⟨y, hxy, hyD⟩ := forces_dia.mp hdia;
    by_cases hbox : x ⊩[_] □(∼(C ⋏ □C));
    . grind;
    . have hx : x ⊮[_] □(□(∼(C ⋏ □C)) 🡒 ∼(C ⋏ □C)) := fun h => hbox (hL h);
      obtain ⟨w, hxw, hw⟩ := not_forces_box.mp hx;
      obtain ⟨hw₁, hw₂⟩ := not_forces_imp.mp hw;
      obtain ⟨hwC, hwBC⟩ := forces_and.mp (not_forces_neg.mp hw₂);
      have hwBBC : w ⊩[_] □□C := forces_box.mp h4 w hxw hwBC;
      apply forces_dia.mpr;
      use w, hxw;
      apply forces_and.mpr;
      and_intros;
      . apply forces_box.mpr;
        intro z hwz;
        have hzD : z ⊩[_] C ⋏ □C := forces_and.mpr
          ⟨forces_box.mp hwBC z hwz, forces_box.mp hwBBC z hwz⟩;
        exact absurd hzD (forces_neg.mp (forces_box.mp hw₁ z hwz));
      . exact hwC;
  have h₁ : (◇(C ⋏ □C) 🡒 ◇(□⊥ ⋏ C)) ∈ @LogicGLPoint2 α :=
    Logic.sumNormal.mdp (Logic.sumNormal.mdp hMeta hLöb) hFour;
  have h₂ : (◇(□⊥ ⋏ C) 🡒 □(◇⊥ ⋎ C)) ∈ @LogicGLPoint2 α := provable_axiomWeakPoint2;
  have h₃ : (□(◇⊥ ⋎ C) 🡒 □C) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    apply LogicGL.iff_forces.mpr;
    grind;
  exact imp_trans (imp_trans h₁ h₂) h₃;

lemma weakPoint3_bridge : (∼□(⊡A 🡒 B) 🡒 ◇(⊡B 🡒 A ⋏ □(⊡B 🡒 A))) ∈ @LogicGLPoint2 α := by
  apply provable_of_provable_GL;
  apply LogicGL.iff_forces.mpr;
  grind;

lemma provable_axiomWeakPoint3 : (□(⊡A 🡒 B) ⋎ □(⊡B 🡒 A)) ∈ LogicGLPoint2 := by
  have h : (∼□(⊡A 🡒 B) 🡒 □(⊡B 🡒 A)) ∈ LogicGLPoint2 :=
    imp_trans weakPoint3_bridge (core_diamond (C := ⊡B 🡒 A));
  have T : ((∼□(⊡A 🡒 B) 🡒 □(⊡B 🡒 A)) 🡒 (□(⊡A 🡒 B) ⋎ □(⊡B 🡒 A))) ∈ LogicGLPoint2 := by
    apply provable_of_provable_GL;
    apply LogicGL.iff_forces.mpr;
    grind;
  exact Logic.sumNormal.mdp T h;

end LogicGLPoint2

lemma LogicGLPoint3_subset_LogicGLPoint2 [DecidableEq α] :
  LogicGLPoint3 ⊆ (LogicGLPoint2 : Logic α) := by
  intro A h;
  induction h using LogicGLPoint3.substlessInduction with
  | provable_GL h => exact LogicGLPoint2.provable_of_provable_GL h;
  | axiomWeakPoint3 => exact LogicGLPoint2.provable_axiomWeakPoint3;
  | mdp ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA;
  | nec ih => exact Logic.sumNormal.nec ih;

end
