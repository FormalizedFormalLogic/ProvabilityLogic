module

public import SeqPL.Logic.SumNormal
public import SeqPL.Logic.GL.Basic
public import SeqPL.Kripke.Linearity

@[expose]
public section

/-- `GLPoint3` (also known as `GLLin` or `K4.3W` in Sambin & Valentini): the normal
extension of `GL` by the weak linearity axiom `.3`, i.e. `□(⊡A 🡒 B) ⋎ □(⊡B 🡒 A)`. -/
abbrev LogicGLPoint3 {α} : Logic α := LogicGL ⊕ᴸ { (□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A)) | (A) (B) }

namespace LogicGLPoint3

lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicGLPoint3 :=
  Logic.sumNormal.mem₁ h

lemma provable_axiomWeakPoint3 {A B : Formula α} :
    ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A))) ∈ LogicGLPoint3 :=
  Logic.sumNormal.mem₂ ⟨A, B, rfl⟩

section

/-- Intrinsic definition of `LogicGLPoint3` avoiding `subst` (for `LogicGLPoint3.substlessInduction`). -/
protected inductive substless : Logic α
  | provable_GL {A} : A ∈ LogicGL → LogicGLPoint3.substless A
  | axiomWeakPoint3 (A B : Formula α) : LogicGLPoint3.substless ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A)))
  | mdp {A B} : LogicGLPoint3.substless (A 🡒 B) → LogicGLPoint3.substless A → LogicGLPoint3.substless B
  | nec {A} : LogicGLPoint3.substless A → LogicGLPoint3.substless (□A)

private lemma substless.eq_LogicGLPoint3 : LogicGLPoint3.substless (α := α) = LogicGLPoint3 := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | provable_GL h => exact provable_of_provable_GL h;
    | axiomWeakPoint3 A B => exact provable_axiomWeakPoint3;
    | mdp _ _ ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA;
    | nec _ ih => exact Logic.sumNormal.nec ih;
  . intro h;
    induction h with
    | mem₁ h => exact LogicGLPoint3.substless.provable_GL h;
    | mem₂ h =>
      obtain ⟨B, C, rfl⟩ := h;
      exact LogicGLPoint3.substless.axiomWeakPoint3 B C;
    | mdp _ _ ihAB ihA => exact LogicGLPoint3.substless.mdp ihAB ihA;
    | nec _ ih => exact LogicGLPoint3.substless.nec ih;
    | subst hA ihA =>
      clear hA;
      induction ihA with
      | provable_GL h => exact LogicGLPoint3.substless.provable_GL (ProvableHilbert.subst h);
      | axiomWeakPoint3 B C => exact LogicGLPoint3.substless.axiomWeakPoint3 _ _;
      | mdp _ _ ihAB ihA => exact LogicGLPoint3.substless.mdp ihAB ihA;
      | nec _ ih => exact LogicGLPoint3.substless.nec ih;

private lemma substless.toLogicGLPoint3 {A : Formula α} (h : LogicGLPoint3.substless A) : A ∈ LogicGLPoint3 :=
  substless.eq_LogicGLPoint3 ▸ h

private lemma substless.ofLogicGLPoint3 {A : Formula α} (h : A ∈ LogicGLPoint3) : LogicGLPoint3.substless A :=
  substless.eq_LogicGLPoint3.symm ▸ h

/-- Induction principle for `LogicGLPoint3` avoiding `subst`: it suffices to cover the
GL part, the axiom `.3` instances, modus ponens, and necessitation. -/
protected lemma substlessInduction
  {motive : (A : Formula α) → A ∈ LogicGLPoint3 → Prop}
  (provable_GL : ∀ {A}, (h : A ∈ LogicGL) → motive A (provable_of_provable_GL h))
  (axiomWeakPoint3 : ∀ {A B}, motive ((□((⊡A) 🡒 B)) ⋎ (□((⊡B) 🡒 A))) provable_axiomWeakPoint3)
  (mdp : ∀ {A B}, {hAB : (A 🡒 B) ∈ LogicGLPoint3} → {hA : A ∈ LogicGLPoint3} →
    motive (A 🡒 B) hAB → motive A hA → motive B (Logic.sumNormal.mdp hAB hA))
    (nec : ∀ {A}, {hA : A ∈ LogicGLPoint3} → motive A hA → motive (□A) (Logic.sumNormal.nec hA)) :
    ∀ {A}, (h : A ∈ LogicGLPoint3) → motive A h := by
  intro A h;
  induction substless.ofLogicGLPoint3 h with
  | provable_GL hg => exact provable_GL hg;
  | axiomWeakPoint3 A B => exact axiomWeakPoint3;
  | mdp hAB hA ihAB ihA =>
    exact mdp (hAB := substless.toLogicGLPoint3 hAB) (hA := substless.toLogicGLPoint3 hA) (ihAB _) (ihA _);
  | nec hA ihA =>
    exact nec (hA := substless.toLogicGLPoint3 hA) (ihA _);

end


universe u
variable {α : Type u}

open Model Model.World

/-- Soundness of `GLPoint3` over finite linear GL models. -/
lemma sound [DecidableEq α] {κ : Type u} [Nonempty κ] {M : Model κ α}
    [M.IsFiniteGLPoint3] {A : Formula α} (h : A ∈ LogicGLPoint3) : M ⊧ A := by
  induction h using LogicGLPoint3.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.finite_soundness h M;
  | axiomWeakPoint3 => exact Model.validate_axiomWeakPoint3;
  | mdp ihAB ihA => exact fun x => (ihAB x) (ihA x);
  | nec ih => exact fun x y _ => ih y;

end LogicGLPoint3

end
