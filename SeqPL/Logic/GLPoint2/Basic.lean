module

public import SeqPL.Logic.SumNormal
public import SeqPL.Logic.GL.Basic
public import SeqPL.Logic.GL.Theorems
public import SeqPL.Logic.GLPoint3.Basic
public import SeqPL.Kripke.Convergence
meta import SeqPL.Logic.GL.Basic

@[expose]
public section

/-- `GLPoint2`: the normal extension of `GL` by the weak convergence axiom `.2`,
i.e. `◇(□A ⋏ B) 🡒 □(◇A ⋎ B)`. -/
abbrev LogicGLPoint2 {α} : Logic α := LogicGL ⊕ᴸ { (◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B) | (A) (B) }

namespace LogicGLPoint2

lemma provable_of_provable_GL {A : Formula α} (h : A ∈ LogicGL) : A ∈ LogicGLPoint2 :=
  Logic.sumNormal.mem₁ h

lemma provable_axiomWeakPoint2 {A B : Formula α} :
    ((◇((□A) ⋏ B)) 🡒 □((◇A) ⋎ B)) ∈ LogicGLPoint2 :=
  Logic.sumNormal.mem₂ ⟨A, B, rfl⟩

section

/-- Intrinsic definition of `LogicGLPoint2` avoiding `subst` (for `LogicGLPoint2.substlessInduction`). -/
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

/-- Soundness of `GLPoint2` over piecewise convergent GL models. -/
lemma sound [DecidableEq α] {κ : Type u} [Nonempty κ] {M : Model κ α}
    [M.IsFiniteGLPoint2] {A : Formula α} (h : A ∈ LogicGLPoint2) : M ⊧ A := by
  induction h using LogicGLPoint2.substlessInduction with
  | provable_GL h => exact ProvableHilbert.Kripke.finite_soundness h M;
  | axiomWeakPoint2 => exact Model.validate_axiomWeakPoint2;
  | mdp ihAB ihA => exact fun x => (ihAB x) (ihA x);
  | nec ih => exact fun x y _ => ih y;

variable [DecidableEq α] {A B C : Formula α}

omit [DecidableEq α] in
/-- Transitivity of implication inside `LogicGLPoint2`. -/
lemma imp_trans (hAB : (A 🡒 B) ∈ @LogicGLPoint2 α) (hBC : (B 🡒 C) ∈ LogicGLPoint2) :
    (A 🡒 C) ∈ LogicGLPoint2 :=
  Logic.sumNormal.imp_trans LogicGL.imp_trans hAB hBC

omit [DecidableEq α] in
/-- `□^[2]⊥` is provable in `GLPoint2`. -/
lemma provable_boxboxbot : (□^[2]⊥) ∈ @LogicGLPoint2 α := by
  show (□□⊥) ∈ @LogicGLPoint2 α;
  -- `∼□⊥ = □⊥ 🡒 ⊥` definitionally, so the Löb axiom gives `□(∼□⊥) 🡒 □⊥`.
  have h₁ : (□(∼□⊥) 🡒 □□⊥) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL <|
      ProvableHilbert.impTrans (ProvableHilbert.modalL (A := ⊥)) ProvableHilbert.modal4;
  have s1 : (◇□⊥ 🡒 ◇(□(∼□⊥) ⋏ □⊥)) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    suffices h : (◇□⊥ 🡒 ◇(□(∼□⊥) ⋏ □⊥)) ∈ @LogicGL ℕ by
      simpa using ProvableHilbert.subst (s := fun _ => (⊥ : Formula α)) h;
    native_decide;
  have s2 : (◇(□(∼□⊥) ⋏ □⊥) 🡒 □(◇(∼□⊥) ⋎ □⊥)) ∈ @LogicGLPoint2 α :=
    provable_axiomWeakPoint2;
  have s3 : (□(◇(∼□⊥) ⋎ □⊥) 🡒 □(□□⊥ 🡒 □⊥)) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    suffices h : (□(◇(∼□⊥) ⋎ □⊥) 🡒 □(□□⊥ 🡒 □⊥)) ∈ @LogicGL ℕ by
      simpa using ProvableHilbert.subst (s := fun _ => (⊥ : Formula α)) h;
    native_decide;
  have s4 : (□(□□⊥ 🡒 □⊥) 🡒 □□⊥) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.modalL (A := □⊥));
  have h₂ : (◇□⊥ 🡒 □□⊥) ∈ @LogicGLPoint2 α :=
    imp_trans (imp_trans (imp_trans s1 s2) s3) s4;
  -- `◇□⊥ = ∼□(∼□⊥)` definitionally, so the bridge is a double-negation elimination.
  have bridge : (∼◇□⊥ 🡒 □(∼□⊥)) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.dne (A := □(∼□⊥)));
  have T : ((□(∼□⊥) 🡒 □□⊥) 🡒 (◇□⊥ 🡒 □□⊥) 🡒 (∼◇□⊥ 🡒 □(∼□⊥)) 🡒 □□⊥) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    suffices h : ((□(∼□⊥) 🡒 □□⊥) 🡒 (◇□⊥ 🡒 □□⊥) 🡒 (∼◇□⊥ 🡒 □(∼□⊥)) 🡒 □□⊥) ∈ @LogicGL ℕ by
      simpa using ProvableHilbert.subst (s := fun _ => (⊥ : Formula α)) h;
    native_decide;
  exact Logic.sumNormal.mdp (Logic.sumNormal.mdp (Logic.sumNormal.mdp T h₁) h₂) bridge;

omit [DecidableEq α] in
/-- `◇(C ⋏ □C) 🡒 □C` is a `GLPoint2` theorem. -/
lemma core_diamond : (◇(C ⋏ □C) 🡒 □C) ∈ @LogicGLPoint2 α := by
  have hLöb : (□(□(∼(C ⋏ □C)) 🡒 ∼(C ⋏ □C)) 🡒 □(∼(C ⋏ □C))) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.modalL (A := ∼(C ⋏ □C)));
  have hFour : (□(□C 🡒 □□C)) ∈ @LogicGLPoint2 α :=
    provable_of_provable_GL (ProvableHilbert.nec ProvableHilbert.modal4);
  -- A K-valid meta-implication absorbing converse well-foundedness into its two GL premises.
  have hMeta : ((□(□(∼(C ⋏ □C)) 🡒 ∼(C ⋏ □C)) 🡒 □(∼(C ⋏ □C))) 🡒
      □(□C 🡒 □□C) 🡒 ◇(C ⋏ □C) 🡒 ◇(□⊥ ⋏ C)) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    suffices h : ((□(□(∼(#0 ⋏ □#0)) 🡒 ∼(#0 ⋏ □#0)) 🡒 □(∼(#0 ⋏ □#0))) 🡒
        □(□#0 🡒 □□#0) 🡒 ◇(#0 ⋏ □#0) 🡒 ◇(□⊥ ⋏ #0)) ∈ @LogicGL ℕ by
      simpa using ProvableHilbert.subst (s := fun _ => C) h;
    native_decide;
  have h₁ : (◇(C ⋏ □C) 🡒 ◇(□⊥ ⋏ C)) ∈ @LogicGLPoint2 α :=
    Logic.sumNormal.mdp (Logic.sumNormal.mdp hMeta hLöb) hFour;
  have h₂ : (◇(□⊥ ⋏ C) 🡒 □(◇⊥ ⋎ C)) ∈ @LogicGLPoint2 α :=
    provable_axiomWeakPoint2 (A := ⊥) (B := C);
  have h₃ : (□(◇⊥ ⋎ C) 🡒 □C) ∈ @LogicGLPoint2 α := by
    apply provable_of_provable_GL;
    suffices h : (□(◇⊥ ⋎ #0) 🡒 □#0) ∈ @LogicGL ℕ by
      simpa using ProvableHilbert.subst (s := fun _ => C) h;
    native_decide;
  exact imp_trans (imp_trans h₁ h₂) h₃;

omit [DecidableEq α] in
/-- `∼□(⊡A 🡒 B) 🡒 ◇((⊡B 🡒 A) ⋏ □(⊡B 🡒 A))` is valid on all GL models. -/
lemma weakPoint3_bridge : (∼□(⊡A 🡒 B) 🡒 ◇(⊡B 🡒 A ⋏ □(⊡B 🡒 A))) ∈ @LogicGLPoint2 α := by
  apply provable_of_provable_GL;
  suffices h : (∼□(⊡(#0) 🡒 #1) 🡒 ◇(⊡(#1) 🡒 #0 ⋏ □(⊡(#1) 🡒 #0))) ∈ @LogicGL ℕ by
    simpa using ProvableHilbert.subst (s := fun n =>
      match n with
      | 0 => A
      | _ => B
    ) h;
  native_decide;

omit [DecidableEq α] in
/-- The weak linearity axiom `.3` is provable in `GLPoint2`. -/
lemma provable_axiomWeakPoint3 : (□(⊡A 🡒 B) ⋎ □(⊡B 🡒 A)) ∈ LogicGLPoint2 := by
  have h : (∼□(⊡A 🡒 B) 🡒 □(⊡B 🡒 A)) ∈ LogicGLPoint2 :=
    imp_trans weakPoint3_bridge (core_diamond (C := ⊡B 🡒 A));
  have T : ((∼□(⊡A 🡒 B) 🡒 □(⊡B 🡒 A)) 🡒 (□(⊡A 🡒 B) ⋎ □(⊡B 🡒 A))) ∈ LogicGLPoint2 := by
    apply provable_of_provable_GL;
    suffices h : ((∼□(⊡(#0) 🡒 #1) 🡒 □(⊡(#1) 🡒 #0)) 🡒 (□(⊡(#0) 🡒 #1) ⋎ □(⊡(#1) 🡒 #0))) ∈ @LogicGL ℕ by
      exact ProvableHilbert.subst (s := fun n =>
        match n with
        | 0 => A
        | _ => B
      ) h;
    native_decide;
  exact Logic.sumNormal.mdp T h;

end LogicGLPoint2


/-- `GLPoint3 ⪯ GLPoint2`: every `GLPoint3` theorem is a `GLPoint2` theorem. -/
lemma LogicGLPoint3_subset_LogicGLPoint2 [DecidableEq α] :
    LogicGLPoint3 ⊆ (LogicGLPoint2 : Logic α) := by
  intro A h
  induction h using LogicGLPoint3.substlessInduction with
  | provable_GL h => exact LogicGLPoint2.provable_of_provable_GL h
  | axiomWeakPoint3 => exact LogicGLPoint2.provable_axiomWeakPoint3
  | mdp ihAB ihA => exact Logic.sumNormal.mdp ihAB ihA
  | nec ih => exact Logic.sumNormal.nec ih

end
