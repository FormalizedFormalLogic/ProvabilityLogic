module

public import SeqPL.ProvabilityLogic.Classification.Letterless
public import SeqPL.Logic.S.Basic
public import SeqPL.Logic.S.GL
public import SeqPL.Logic.D.Basic
public import SeqPL.Kripke.GraftChain

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


section

variable [Nonempty κ] {M : Model κ α} [Fintype M.World] [M.IsGL]

/--
  In a finite GL model, every world whose rank exceeds `Γ.card` has a strict successor
  forcing all axiom T instances `□B 🡒 B` for `B ∈ Γ` (the semantic core of Lemma 26
  in [AB05]). Induction on `Γ.card`: take a successor `z` of rank exactly `Γ.card`;
  if some `□B₀ 🡒 B₀` fails at `z` then `z ⊩ □B₀`, hence `□B₀ 🡒 B₀` holds automatically
  at every successor of `z`, and the induction hypothesis applies to `Γ.erase B₀`.
-/
lemma Model.exists_forces_axiomT_of_card_lt_rank [DecidableEq α] :
    ∀ {n : ℕ} {Γ : FormulaFinset α}, Γ.card = n → ∀ {x : M.World}, n < x.rank →
    ∃ z, x ≺ z ∧ ∀ B ∈ Γ, z ⊩ ((□B) 🡒 B) := by
  intro n;
  induction n with
  | zero =>
    intro Γ hΓ x hx;
    obtain ⟨z, Rxz, _⟩ := Model.of_lt_rank hx;
    exact ⟨z, Rxz, by simp [Finset.card_eq_zero.mp hΓ]⟩;
  | succ n ih =>
    intro Γ hΓ x hx;
    obtain ⟨z, Rxz, hz⟩ := Model.of_lt_rank hx;
    by_cases hall : ∀ B ∈ Γ, z ⊩ ((□B) 🡒 B);
    . exact ⟨z, Rxz, hall⟩;
    . push Not at hall;
      obtain ⟨B₀, hB₀, hfail⟩ := hall;
      obtain ⟨hbox, hnB⟩ := Model.World.not_forces_imp.mp hfail;
      obtain ⟨z', Rzz', hz'⟩ := ih
        (Γ := Γ.erase B₀) (by rw [Finset.card_erase_of_mem hB₀, hΓ]; rfl)
        (x := z) (by omega);
      refine ⟨z', IsTrans.trans _ _ _ Rxz Rzz', ?_⟩;
      intro B hB;
      by_cases hBB₀ : B = B₀;
      . subst hBB₀;
        intro _;
        exact hbox z' Rzz';
      . exact hz' B (Finset.mem_erase.mpr ⟨hBB₀, hB⟩);

/--
  **Chain lemma** (corresponding to Lemma 26 in [AB05], instantiated to the boxed
  subformulas of `A`): `GL ⊢ ∼□^[m+1]⊥ 🡒 ◇⋀{□B 🡒 B | □B ∈ Sub(A)}` where `m` is the
  number of boxed subformulas. An actual proof of what Foundation assumes as the axiom
  `GL.formalized_validates_axiomT_set_in_irrefl_trans_chain`.
-/
lemma LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS [DecidableEq α] {A : Formula α} :
    ((∼(□^[A.subfmls.prebox.card + 1]⊥)) 🡒 ◇(⋀A.subfmlsS)) ∈ LogicGL := by
  apply LogicGL_semantical_TFAE.out 2 0 |>.mp;
  intro κ _ M _ hne;
  haveI : Fintype M.World := Fintype.ofFinite _;
  replace hne : ¬(Model.World.rank M.root.1 < A.subfmls.prebox.card + 1) :=
    fun h => (Model.World.forces_neg.mp hne) (Model.iff_rank_lt_forces_boxItr_bot.mp h);
  obtain ⟨z, Rrz, hz⟩ := Model.exists_forces_axiomT_of_card_lt_rank
    (Γ := A.subfmls.prebox) rfl (x := M.root.1) (by omega);
  apply Model.World.forces_dia.mpr;
  refine ⟨z, Rrz, Model.World.forces_fconj.mpr ?_⟩;
  intro C hC;
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC;
  exact hz B hB;

end

/--
  **Finiteness or cofiniteness of traces** (Lemma 12 in [AB05]): the trace of any formula
  is either finite or cofinite. If the trace is infinite, take a countermodel whose height
  exceeds the number of boxed subformulas; the chain lemma yields a world `a` forcing all
  axiom T instances, and `graftChain` then produces countermodels of every height `≥ M.height`.
-/
lemma Formula.trace_finite_or_cofinite [DecidableEq α] {A : Formula α} :
    A.trace.Finite ∨ A.traceᶜ.Finite := by
  rw [or_iff_not_imp_left];
  intro h_inf;
  replace h_inf : A.trace.Infinite := h_inf;
  obtain ⟨m, hm₁, hm₂⟩ := h_inf.exists_gt (A.subfmls.prebox.card);
  obtain ⟨κ, _, M, _, _, hh, hr⟩ := Formula.iff_mem_trace.mp hm₁;
  have : Finite M.World := by infer_instance;
  haveI : M.IsFiniteGL := {};
  have hroot : M.height = Model.World.rank M.root.1 := rfl;
  have H₁ : M.root.1 ⊩ (∼(□^[A.subfmls.prebox.card + 1]⊥)) := by
    apply Model.World.forces_neg.mpr;
    intro hc;
    have := Model.iff_rank_lt_forces_boxItr_bot.mpr hc;
    omega;
  have H₂ : M.root.1 ⊩ ((∼(□^[A.subfmls.prebox.card + 1]⊥)) 🡒 ◇(⋀A.subfmlsS)) := by
    have := LogicGL_semantical_TFAE.out 0 2 |>.mp
      (LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS (A := A));
    apply this;
  obtain ⟨a, Rra, hA⟩ := Model.World.forces_dia.mp (H₂ H₁);
  have ha : ∀ B, (□B) ∈ A.subfmls → a ⊩ ((□B) 🡒 B) := by
    intro B hB;
    exact Model.World.forces_fconj.mp hA _
      (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hB));
  apply Set.Finite.subset (Set.finite_Iio M.height);
  intro n hn;
  simp only [Set.mem_compl_iff] at hn;
  by_contra hge;
  apply hn;
  replace hge : M.height ≤ n := by simpa using hge;
  have hra : Model.World.rank a < M.height := RootedModel.rank_lt_height Rra;
  haveI := RootedModel.graftChain.isFiniteGL (M := M) (a := a) (k := n - Model.World.rank a - 1) Rra;
  apply Formula.iff_mem_trace.mpr;
  refine ⟨κ ⊕ Fin (n - Model.World.rank a - 1), inferInstance,
    M.graftChain a (n - Model.World.rank a - 1), inferInstance, inferInstance, ?_, ?_⟩;
  . rw [RootedModel.graftChain.height_eq Rra];
    omega;
  . intro hc;
    apply hr;
    exact RootedModel.graftChain.mainlemma Rra ha (Formula.mem_subfmls_self) |>.2 M.root.1 |>.mp hc;


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


section

lemma Logic.trace_subset_of_mem {L : Logic α} {A : Formula α} (h : A ∈ L) : A.trace ⊆ L.trace := by
  intro n hn;
  simp only [Logic.trace, FormulaSet.trace, Set.mem_iUnion, exists_prop];
  exact ⟨A, h, hn⟩;

/--
  Forcing of a lifted letterless formula is determined by the rank
  (generalization of `Model.iff_forces_rank_mem_spectrum` to models over arbitrary `α`).
-/
lemma Model.iff_forces_lift_rank_mem_spectrum
    {κ : Type*} [Nonempty κ] {M : Model κ α} [Fintype M.World] [M.IsGL]
    {x : M.World} {B : LetterlessFormula} :
    x ⊩ (LetterlessFormula.lift B : Formula α) ↔ x.rank ∈ LetterlessFormula.spectrum B := by
  induction B generalizing x with
  | atom a => exact a.elim;
  | bot => simp [LetterlessFormula.lift];
  | imp B C ihB ihC =>
    show ((x ⊩ (LetterlessFormula.lift B : Formula α)) → (x ⊩ (LetterlessFormula.lift C : Formula α))) ↔ _;
    rw [ihB, ihC, LetterlessFormula.spectrum_imp];
    grind;
  | box B ihB =>
    calc
      _ ↔ ∀ y, x ≺ y → y ⊩ (LetterlessFormula.lift B : Formula α) := by
        exact Model.World.forces_box (A := (LetterlessFormula.lift B : Formula α));
      _ ↔ ∀ y, x ≺ y → Model.World.rank y ∈ LetterlessFormula.spectrum B := by simp [ihB];
      _ ↔ ∀ i < x.rank, i ∈ LetterlessFormula.spectrum B := by
        constructor;
        . intro h i hi;
          grind [Model.of_lt_rank hi];
        . grind [Model.rank_lt_of_rel];
      _ ↔ _ := by grind [LetterlessFormula.spectrum_box];

variable [DecidableEq α] {L : Logic α} {A : Formula α}

/--
  If `L.trace` is coinfinite then `L ⊆ GLα (L.trace)`.
  First half of Lemma 45 in [AB05].
-/
lemma subset_LogicGLAlpha_of_trace_coinfinite (hL : L.traceᶜ.Infinite) :
    L ⊆ LogicGLAlpha L.trace := by
  intro A hA;
  have hsub : A.trace ⊆ L.trace := Logic.trace_subset_of_mem hA;
  have hfin : A.trace.Finite := by
    rcases Formula.trace_finite_or_cofinite (A := A) with h | h;
    . exact h;
    . exact absurd (h.subset (Set.compl_subset_compl.mpr hsub)) hL;
  have hGL : ((⋀(hfin.toFinset.image (TBB (α := α)))) 🡒 A) ∈ LogicGL := by
    apply LogicGL_semantical_TFAE.out 2 0 |>.mp;
    intro κ _ M _ hTBB;
    haveI : Fintype M.World := Fintype.ofFinite _;
    have hnot : M.height ∉ A.trace := by
      intro hmem;
      exact Model.iff_forces_TBB_neq_rank.mp
        (Model.World.forces_fconj.mp hTBB (TBB M.height)
          (Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hmem))) rfl;
    exact Formula.iff_mem_not_trace.mp hnot κ inferInstance M inferInstance inferInstance rfl;
  apply Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ hGL);
  apply fconj_mem_sumQuasiNormal;
  intro B hB;
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hB;
  apply Logic.sumQuasiNormal.mem₂;
  exact ⟨TBB n, ⟨n, hsub (hfin.mem_toFinset.mp hn), rfl⟩, LetterlessFormula.eq_lift_TBB⟩;

/--
  If `L.trace` is cofinite then `L ⊆ GLβ⁻ (L.trace)`.
  Second half of Lemma 45 in [AB05].
-/
lemma subset_LogicGLBetaMinus_of_trace_cofinite (hL : L.traceᶜ.Finite) :
    L ⊆ LogicGLBetaMinus L.trace hL := by
  intro A hA;
  have hsub : A.trace ⊆ L.trace := Logic.trace_subset_of_mem hA;
  have hGL : ((LetterlessFormula.lift (TBBMinus _ hL) : Formula α) 🡒 A) ∈ LogicGL := by
    apply LogicGL_semantical_TFAE.out 2 0 |>.mp;
    intro κ _ M _ hTM;
    haveI : Fintype M.World := Fintype.ofFinite _;
    have hnot : M.height ∉ A.trace := by
      intro hmem;
      have hrank : M.height ∈ LetterlessFormula.spectrum (TBBMinus _ hL) :=
        Model.iff_forces_lift_rank_mem_spectrum.mp hTM;
      have : LetterlessFormula.spectrum (TBBMinus _ hL) = L.traceᶜ := by
        have := LetterlessFormula.trace_TBBMinus (s := L.traceᶜ) hL;
        simpa [LetterlessFormula.trace, compl_compl] using congrArg compl this;
      rw [this] at hrank;
      exact hrank (hsub hmem);
    exact Formula.iff_mem_not_trace.mp hnot κ inferInstance M inferInstance inferInstance rfl;
  apply Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ hGL);
  exact Logic.sumQuasiNormal.mem₂ ⟨TBBMinus _ hL, rfl, rfl⟩;

end

end
