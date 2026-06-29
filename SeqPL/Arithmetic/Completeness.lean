module

public import SeqPL.Arithmetic.Soundness
public import SeqPL.Arithmetic.SolovaySentences

@[expose] public section

open Classical
open LO
open LO.FirstOrder.ProvabilityAbstraction

variable {T : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

variable {κ : Type*} [Nonempty κ]
         {α : Type*}
         {A B : _root_.Formula α}
         {M : RootedModel κ α}

@[grind]
def LO.FirstOrder.ArithmeticTheory.provabilityLogicRelativeTo (T U : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := {A | ∀ f : StandardRealization α T, U ⊢ f A}

abbrev LO.FirstOrder.ArithmeticTheory.provabilityLogic (T : FirstOrder.ArithmeticTheory) [T.Δ₁] : Logic α := T.provabilityLogicRelativeTo T

theorem unprovable_realization_exists
  (M : RootedModel κ α) [Fintype M.World] [M.IsGL]
  (hA : M.root.1 ⊮ A) (h : M.height < T.height)
  : ∃ f : StandardRealization α T, T ⊬ f A := by
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences (M := M.extendRoot 1) (T := T);
  use S.realization;
  contrapose! h;
  apply Order.le_of_lt_add_one;
  calc
    T.height < (M.extendRoot 1).height := S.theory_height (T.standardProvability.syntactical_sound ℕ) (A := A) ?_ h
    _        = _                       := by
      have := RootedModel.extendRoot.Ext1.eq_height_original_height_succ (M := M);
      simp_all only [ne_eq, PNat.val_ofNat, Nat.cast_add, Nat.cast_one];
  . apply Model.World.forces_dia.mpr;
    use M.root;
    constructor;
    . tauto;
    . exact RootedModel.extendRoot.same_forces_embed.not.mpr hA;

namespace LogicGL

theorem arithmetical_completeness_of_infinity_height (height : T.height = (⊤ : ℕ∞)) :
  (∀ f : StandardRealization α T, T ⊢ f A) → A ∈ LogicGL _ := by
  contrapose!;
  intro hA;
  replace h := LogicGL_semantical_TFAE.out 0 2 |>.not.mp hA;
  push Not at h;
  obtain ⟨κ, _, M, _, hA⟩ := h;
  have : Fintype M.World := Fintype.ofFinite _;
  exact unprovable_realization_exists M hA (by simp_all);

theorem arithmetical_completeness_of_finite_le {n : ℕ} (height : n ≤ T.height)
  : (∀ f : StandardRealization α T, T ⊢ f A) →  □^[n] ⊥ 🡒 A ∈ LogicGL _ := by
  contrapose!;
  intro hA;
  replace h := LogicGL_semantical_TFAE.out 0 2 |>.not.mp hA;
  push Not at h;
  obtain ⟨κ, _, M, _, hA⟩ := h;
  replace hA := Model.World.not_forces_imp.mp hA;
  have : Fintype M.World := Fintype.ofFinite _;
  apply unprovable_realization_exists M hA.2;
  apply lt_of_lt_of_le;
  . apply Nat.cast_lt.mpr $ RootedModel.iff_height_lt_root_forces_boxItr_bot |>.mpr hA.1;
  . exact height;

lemma arithmetical_completeness_iff_of_infinity_height (height : T.height = (⊤ : ℕ∞))
  : A ∈ LogicGL _ ↔ (∀ f : StandardRealization α T, T ⊢ f A) := by
  constructor;
  . intro h f;
    exact arithmetical_soundness (f := f) h;
  . exact arithmetical_completeness_of_infinity_height height;

lemma arithmetical_completeness_iff_of_sigma1_sound [T.SoundOnHierarchy 𝚺 1]
  : A ∈ LogicGL _ ↔ (∀ f : StandardRealization α T, T ⊢ f A) :=
  arithmetical_completeness_iff_of_infinity_height (FirstOrder.Arithmetic.height_eq_top_of_sigma1_sound T)

theorem eq_provabilityLogic_sigma1_sound [T.SoundOnHierarchy 𝚺 1] : LogicGL α = T.provabilityLogic := by
  ext A;
  exact LogicGL.arithmetical_completeness_iff_of_sigma1_sound;

theorem eq_provabilityLogic_peano_arithmetic : LogicGL α = (𝗣𝗔.provabilityLogic) := LogicGL.eq_provabilityLogic_sigma1_sound

end LogicGL


namespace LogicGLPlusBoxBot

theorem arithmetical_completeness {n : ℕ∞} (hn : n ≤ T.height)
  (h : ∀ f : StandardRealization α T, T ⊢ f A) : A ∈ LogicGLPlusBoxBot n := by
  match n with
  | .none =>
    apply LogicGL.arithmetical_completeness_of_infinity_height (T := T) ?_ h;
    exact eq_top_iff.mpr hn;
  | .some n =>
    apply LogicGLPlusBoxBot.iff_provable_provable_GL.mpr;
    apply LogicGL.arithmetical_completeness_of_finite_le (T := T) ?_ h;
    exact hn;

theorem arithmetical_completeness_iff
  : A ∈ LogicGLPlusBoxBot T.height ↔ (∀ f : StandardRealization α T, T ⊢ f A) := by
  constructor;
  . intro h f; exact arithmetical_soundness h;
  . exact arithmetical_completeness (by simp);

lemma eq_provabilityLogic : LogicGLPlusBoxBot (α := α) T.height = T.provabilityLogic := by
  ext A;
  exact arithmetical_completeness_iff;

end LogicGLPlusBoxBot


end
