module

public import SeqPL.ProvabilityLogic.Classification.Letterless
public import SeqPL.Logic.S.Basic
public import SeqPL.Logic.D.Basic

@[expose]
public section

universe u
variable {α : Type u}


namespace Formula

end Formula

/-
def Model.uLift.{u₁, u₂, v} {κ : Type u₁} [Nonempty κ] {α : Type v} (M : Model κ α) : Model (ULift.{u₂, u₁} κ) α where
  Rel' x y := M.Rel x.down y.down
  Val' x a := M.Val x.down a

namespace Model.uLift

variable {κ₁ : Type u₁} [Nonempty κ₁] {M : Model κ₁ α}
variable {α : Type v} {A B : Formula α}


def embed : M.World → (M.uLift.{u₁, u₂}).World := fun x => ⟨x⟩
instance : Coe M.World (M.uLift.{u₁, u₂}).World := ⟨embed⟩

@[grind =]
lemma rel_iff {x y : M.World} : M.Rel x y ↔ (M.uLift.{u₁, u₂}).Rel x y := by simp [Model.uLift, Model.Rel, embed]

lemma same_forces {x : M.World} {A : Formula α} : Model.World.Forces (M := M.uLift.{u₁, u₂, v}) (embed x) A ↔ x ⊩ A := by
  induction A generalizing x with
  | atom a => simp [Model.uLift, Model.World.Forces, embed]
  | bot => simp [Model.uLift, Model.World.Forces, embed]
  | imp A B ihA ihB => grind;
  | box A ihA =>
    constructor;
    . intro h y Rxy;
      exact ihA |>.mp $ @h (embed y) (rel_iff.mpr Rxy);
    . rintro h ⟨y⟩ Rxy;
      exact ihA |>.mpr $ @h y (rel_iff.mp Rxy);

end Model.uLift
-/

namespace Formula

variable {n : ℕ} {A B : Formula α}

@[grind]
def trace (A : Formula α) : Set ℕ := { n |
  ∃ κ : Type u, ∃ _ : Nonempty κ, ∃ M : RootedModel κ α, ∃ _ : Fintype M.World, ∃ _ : M.IsGL,
  (M.height = n ∧ M.root.1 ⊮ A)
}

@[grind =]
lemma iff_mem_trace :
  n ∈ A.trace ↔
  ∃ κ : Type u, ∃ _ : Nonempty κ, ∃ M : RootedModel κ α, ∃ _ : Fintype M.World, ∃ _ : M.IsGL, M.height = n ∧ M.root.1 ⊮ A := by
  grind;

@[grind =]
lemma iff_mem_not_trace :
  n ∉ A.trace ↔
  ∀ κ : Type u, ∀ _ : Nonempty κ, ∀ M : RootedModel κ α, ∀ _ : Fintype M.World, ∀ _ : M.IsGL, M.height = n → M.root.1 ⊩ A := by
  grind;

variable {α : Type u} {A B : Formula α}

@[grind =]
lemma eq_trace_toLetterless_trace (hA : A.Letterless) : A.trace = LetterlessFormula.trace (A.toLetterless hA) := by classical
  ext n;
  apply Iff.trans ?_ $ spectrum_TFAE.out 1 0 |>.not;
  push Not;
  rw [iff_mem_trace];
  constructor;
  . sorry;
  . rintro ⟨κ, _, _, M, _, x, rfl, h⟩;
    use (ULift κ), inferInstance;
    sorry;

@[simp, grind =]
lemma trace_top : (⊤ : Formula α).trace = ∅ := by grind;

@[simp, grind =]
lemma trace_bot : (⊥ : Formula α).trace = Set.univ := by
  rw [eq_trace_toLetterless_trace (A := ⊥) (by simp [Letterless])];
  exact LetterlessFormula.trace_bot;

@[simp, grind =]
lemma trace_and : (A ⋏ B).trace = A.trace ∪ B.trace := by ext n; grind;

@[simp, grind =]
lemma trace_lconj {Γ : FormulaList α} : (⋀Γ).trace = ⋃ A ∈ Γ, A.trace := by
  match Γ with
  | [] => simp;
  | [A] => simp;
  | A :: B :: Γ => simp [FormulaList.conj, trace_and, trace_lconj];

@[simp, grind =]
lemma trace_fconj {Γ : FormulaFinset α} : (⋀Γ).trace = ⋃ A ∈ Γ, A.trace := by
  simp [FormulaFinset.conj, trace_lconj]


@[simp, grind! .]
lemma letterless_boxItr_bot {n} : (□^[n]⊥ : Formula α).Letterless := by
  match n with
  | 0 => simp [Formula.boxItr, Letterless];
  | n + 1 => apply letterless_boxItr_bot (n := n);

@[simp, grind! .]
lemma letterless_TBB : (@TBB α n).Letterless := by
  simp [Letterless, TBB]


@[grind =]
lemma toLetterless_boxItr_bot {n} : (□^[n]⊥ : Formula α).toLetterless (by grind) = (□^[n]⊥ : LetterlessFormula) := by
  match n with
  | 0 => simp [Formula.boxItr, Formula.toLetterless];
  | n + 1 => simp [Formula.boxItr, Formula.toLetterless, toLetterless_boxItr_bot (n := n)];

@[grind =]
lemma toLetterless_TBB : (@TBB α n).toLetterless (by grind) = (TBB n) := by
  simp [TBB, Formula.toLetterless]
  grind;


@[grind .] lemma trace_TBB : (@TBB α n).trace = {n} := by grind;


lemma subset_trace_of_provable_GL (h : A 🡒 B ∈ LogicGL) : B.trace ⊆ A.trace := by classical
  intro n;
  simp only [iff_mem_trace];
  rintro ⟨κ, _, M, _, _, rfl, hB⟩;
  use κ, ‹_›, M, ‹_›, ‹_›, rfl;
  have : Finite M.World := by infer_instance;
  have : M.IsFiniteGL := {}
  revert hB;
  contrapose!;
  show M.root.1 ⊩ A 🡒 B;
  have := (LogicGL_semantical_TFAE.out 0 2 |>.mp h);
  apply this;

end Formula



namespace FormulaSet

def trace (X : FormulaSet α) : Set ℕ := ⋃ A ∈ X, A.trace

@[grind =] lemma trace_empty : (∅ : FormulaSet α).trace = ∅ := by simp [trace];
@[grind =] lemma trace_singleton : trace {A} = A.trace := by simp [trace];

end FormulaSet


abbrev Logic.trace (L : Logic α) : Set ℕ := FormulaSet.trace L

namespace Model

variable [Nonempty κ] {M : Model κ α}

/-- 付値を置換 `s` で合成したモデル（フレームは不変）． -/
abbrev substModel (M : Model κ α) (s : Formula.Substitution α) : Model κ α where
  Rel' := M.Rel'
  Val' x a := Model.World.Forces (M := M) x (s a)

lemma forces_substModel {s : Formula.Substitution α} {A : Formula α} {x : M.World} :
    x ⊩ A⟦s⟧ ↔ Model.World.Forces (M := M.substModel s) x A := by
  induction A generalizing x with
  | atom a => rw [Formula.subst_atom]; rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [Formula.subst_imp, Model.World.Forces]; rw [ihA, ihB]
  | box A ih =>
    simp only [Formula.subst_box, Model.World.Forces];
    constructor;
    · intro h y hy; exact ih.mp (h y hy);
    · intro h y hy; exact ih.mpr (h y hy);

instance {s : Formula.Substitution α} [Fintype M.World] : Fintype (M.substModel s).World := ‹Fintype M.World›
instance {s : Formula.Substitution α} [h : M.IsGL] : (M.substModel s).IsGL where __ := h

end Model

namespace RootedModel

variable [Nonempty κ] {M : RootedModel κ α} {s : Formula.Substitution α}

/-- 付値を置換 `s` で合成した根付きモデル（フレーム・根は不変）． -/
abbrev substModel (M : RootedModel κ α) (s : Formula.Substitution α) : RootedModel κ α where
  toModel := M.toModel.substModel s
  root := M.root

end RootedModel

lemma trace_subst_subset {A : Formula α} {s : Formula.Substitution α} : (A⟦s⟧).trace ⊆ A.trace := by
  intro n hn;
  obtain ⟨κ, _, M, _, _, hh, hr⟩ := Formula.iff_mem_trace.mp hn;
  exact Formula.iff_mem_trace.mpr ⟨κ, inferInstance, M.substModel s, inferInstance, inferInstance, hh, fun h => hr (Model.forces_substModel.mpr h)⟩;

lemma eq_LogicGL_quasiExtension_trace {X : FormulaSet α} (X_subst : ∀ A ∈ X, ∀ s, A.subst s ∈ X) : (LogicGL +ᴸ X).trace = X.trace := by
  classical
  ext n;
  constructor;
  . simp only [Logic.trace, FormulaSet.trace, Set.mem_iUnion, exists_prop];
    suffices H : ∀ x, x ∈ ((@LogicGL α) +ᴸ X) → n ∈ x.trace → ∃ i ∈ X, n ∈ i.trace by
      rintro ⟨x, hx, hn⟩; exact H x hx hn;
    intro x hx;
    induction hx with
    | @mem₁ C hA =>
      intro hn;
      exfalso;
      obtain ⟨κ, _, M, _, _, rfl, hr⟩ := Formula.iff_mem_trace.mp hn;
      haveI : M.IsFiniteGL := ⟨⟩;
      have hval := (LogicGL_semantical_TFAE (A := C)).out 0 2 |>.mp hA;
      exact hr (hval M);
    | mem₂ hA => intro hn; exact ⟨_, hA, hn⟩
    | @mdp A B hAB hA ihAB ihA =>
      intro hn;
      by_cases hA' : n ∈ A.trace;
      · exact ihA hA';
      · by_cases hAB' : n ∈ (A 🡒 B).trace;
        · exact ihAB hAB';
        · exfalso;
          obtain ⟨κ, _, M, _, _, rfl, hr⟩ := Formula.iff_mem_trace.mp hn;
          have fA := Formula.iff_mem_not_trace.mp hA' κ inferInstance M inferInstance inferInstance rfl;
          have fAB := Formula.iff_mem_not_trace.mp hAB' κ inferInstance M inferInstance inferInstance rfl;
          exact hr (fAB fA);
    | @subst A s hA ihA => intro hn; exact ihA (trace_subst_subset hn)
  . simp [Logic.trace, FormulaSet.trace];
    intro A hA₁ hA₂;
    use A;
    constructor;
    . exact Logic.sumQuasiNormal.mem₂ hA₁;
    . assumption;


namespace Logic

class ModusPonens (L : Logic α) : Prop where
  mdp : ∀ {A B : Formula α}, A 🡒 B ∈ L → A ∈ L → B ∈ L
export ModusPonens (mdp)

class Substitution (L : Logic α) : Prop where
  subst : ∀ {A s}, A ∈ L → A⟦s⟧ ∈ L
export Substitution (subst)

class IsQuasiNormal (L : Logic α) extends ModusPonens L, Substitution L where

@[grind =]
lemma sumQuasiNormal.eq_sum_empty {L : Logic α} [L.IsQuasiNormal] : (L +ᴸ ∅) = L := by
  ext A;
  constructor;
  . intro h;
    induction h with
    | mem₁ hA => exact hA;
    | mem₂ hB => contradiction;
    | mdp _ _ ihAB ihA => exact L.mdp ihAB ihA;
    | subst _ ihA => exact L.subst ihA;
  . apply Logic.sumQuasiNormal.mem₁;

instance {L₁ L₂ : Logic α} : (L₁ +ᴸ L₂).IsQuasiNormal where
  mdp := Logic.sumQuasiNormal.mdp;
  subst := Logic.sumQuasiNormal.subst;

end Logic


instance : (@LogicGL α).IsQuasiNormal where
  mdp := ProvableHilbert.mdp;
  subst := fun h => ProvableHilbert.subst h;

@[simp, grind =]
lemma LogicGL.eq_trace : (@LogicGL α).trace = ∅ := by
  grind [eq_LogicGL_quasiExtension_trace (α := α) (X := ∅) (by simp)];

@[simp, grind =]
lemma LogicGLAlpha.eq_trace {Alpha : Set ℕ} : (@LogicGLAlpha α Alpha).trace = Alpha := by
  apply Eq.trans (eq_LogicGL_quasiExtension_trace (by grind));
  ext n;
  simp only [FormulaSet.trace, LetterlessFormulaSet.lift, Set.mem_iUnion,
    Set.mem_image, exists_prop];
  constructor;
  · rintro ⟨A, ⟨B, ⟨i, hi, rfl⟩, rfl⟩, hn⟩;
    rw [LetterlessFormula.eq_lift_TBB, Formula.trace_TBB] at hn;
    simpa using hn ▸ hi;
  · intro hn;
    exact ⟨TBB n, ⟨TBB n, ⟨n, hn, rfl⟩, LetterlessFormula.eq_lift_TBB⟩, by rw [Formula.trace_TBB]; simp⟩;

lemma subset_LogicGLAlpha_LogicS : LogicGLAlpha Alpha ⊆ @LogicS α := by
  intro φ hφ;
  induction hφ with
  | mem₁ hA => exact Logic.sumQuasiNormal.mem₁ hA;
  | mem₂ hA =>
    obtain ⟨A, ⟨i, _, rfl⟩, rfl⟩ := hA;
    -- TODO: extract for all TBB instances are theorem of LogicS
    apply Logic.sumQuasiNormal.mem₂;
    use □^[i]⊥
    grind;
  | mdp _ _ ihAB ihA => exact LogicS.mdp ihAB ihA;
  | subst _ ihA => exact LogicS.subst ihA;

lemma LogicS.eq_trace : (@LogicS α).trace = Set.univ := by
  suffices ∀ i : ℕ, ∃ A ∈ @LogicS α, i ∈ A.trace by
    simpa [Set.eq_univ_iff_forall, Logic.trace, FormulaSet.trace];
  intro i;
  use (TBB i);
  constructor;
  . -- TODO: extract for all TBB instances are theorem of LogicS
    apply Logic.sumQuasiNormal.mem₂;
    use □^[i]⊥
    grind;
  . grind;

end
