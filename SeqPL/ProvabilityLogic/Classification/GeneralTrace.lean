module

public import SeqPL.ProvabilityLogic.Classification.LetterlessTrace
public import SeqPL.Logic.S.Basic
public import SeqPL.Logic.D.Basic
public import SeqPL.Kripke.RootedModel
public import SeqPL.Kripke.Graft
public import SeqPL.Formula.Substitution
public import SeqPL.ProvabilityLogic.SolovaySentences

@[expose]
public section

universe u
variable {α : Type u}

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
lemma eq_trace_toLetterless_trace (hA : A.Letterless) : A.trace = LetterlessFormula.trace (A.toLetterless hA) := by
  ext n;
  rw [iff_mem_trace, LetterlessFormula.iff_mem_trace_rootedModel, lift_toLetterless hA];

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
lemma letterless_TBB : (@TBB α n).Letterless := by
  simp [Letterless, TBB]


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
  apply LogicGL.iff_forces_root.mp h;

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
      use z', IsTrans.trans _ _ _ Rxz Rzz';
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
  apply LogicGL.iff_forces_root.mpr;
  intro κ _ M _ hne;
  haveI : Fintype M.World := Fintype.ofFinite _;
  replace hne : ¬(Model.World.rank M.root.1 < A.subfmls.prebox.card + 1) :=
    fun h => (Model.World.forces_neg.mp hne) (Model.iff_rank_lt_forces_boxItr_bot.mp h);
  obtain ⟨z, Rrz, hz⟩ := Model.exists_forces_axiomT_of_card_lt_rank
    (Γ := A.subfmls.prebox) rfl (x := M.root.1) (by omega);
  apply Model.World.forces_dia.mpr;
  use z, Rrz;
  apply Model.World.forces_fconj.mpr;
  intro C hC;
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hC;
  exact hz B hB;

end

/--
  **Finiteness or cofiniteness of traces** (Lemma 12 in [AB05]): the trace of any formula
  is either finite or cofinite. If the trace is infinite, take a countermodel whose height
  exceeds the number of boxed subformulas; the chain lemma yields a world `a` forcing all
  axiom T instances, and `graft` then produces countermodels of every height `≥ M.height`.
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
    apply LogicGL.iff_forces_root.mp
      (LogicGL.provable_neg_boxItr_bot_imp_dia_subfmlsS (A := A));
  obtain ⟨a, Rra, hA⟩ := Model.World.forces_dia.mp (H₂ H₁);
  have ha : ∀ B, (□B) ∈ A.subfmls → a ⊩ ((□B) 🡒 B) := by
    intro B hB;
    exact Model.World.forces_fconj.mp hA _
      (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hB));
  let a' : M.ReflexiveWorldOf A.subfmls := ⟨a, fun {B} hB => ha B hB⟩;
  apply Set.Finite.subset (Set.finite_Iio M.height);
  intro n hn;
  simp only [Set.mem_compl_iff] at hn;
  by_contra hge;
  apply hn;
  replace hge : M.height ≤ n := by simpa using hge;
  have hra : Model.World.rank a < M.height := RootedModel.rank_lt_height Rra;
  haveI := RootedModel.graft.isFiniteGL (M := M) (a := a) (k := n - Model.World.rank a - 1) Rra;
  apply Formula.iff_mem_trace.mpr;
  refine ⟨κ ⊕ Fin (n - Model.World.rank a - 1), inferInstance,
    M.graft a (n - Model.World.rank a - 1), inferInstance, inferInstance, ?_, ?_⟩;
  . rw [RootedModel.graft.height_eq Rra];
    omega;
  . intro hc;
    apply hr;
    exact RootedModel.graft.mainlemma a' Rra (Formula.mem_subfmls_self) |>.2 M.root.1 |>.mp hc;


namespace FormulaSet

def trace (X : FormulaSet α) : Set ℕ := ⋃ A ∈ X, A.trace

@[grind =] lemma trace_empty : (∅ : FormulaSet α).trace = ∅ := by simp [trace];
@[grind =] lemma trace_singleton : trace {A} = A.trace := by simp [trace];

end FormulaSet


abbrev Logic.trace (L : Logic α) : Set ℕ := FormulaSet.trace L

lemma trace_subst_subset {A : Formula α} {s : Formula.Substitution α α} : (A⟦s⟧).trace ⊆ A.trace := by
  intro n hn;
  obtain ⟨κ, _, M, _, _, hh, hr⟩ := Formula.iff_mem_trace.mp hn;
  exact Formula.iff_mem_trace.mpr ⟨κ, inferInstance, M.substModel s, inferInstance, inferInstance, hh, fun h => hr (Model.forces_substModel.mpr h)⟩;

lemma eq_LogicGL_quasiExtension_trace {X : FormulaSet α} (_ : ∀ A ∈ X, ∀ s, A.subst s ∈ X) : (LogicGL +ᴸ X).trace = X.trace := by
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
      exact hr (LogicGL.iff_forces_root.mp hA M);
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

/-- The trace of a lifted letterless formula equals the trace of that letterless
formula, computed directly from the `RootedModel`-existential descriptions of both traces. -/
lemma Formula.trace_lift {B : LetterlessFormula} :
    (LetterlessFormula.lift B : Formula α).trace = LetterlessFormula.trace B := by
  ext n;
  rw [Formula.iff_mem_trace, LetterlessFormula.iff_mem_trace_rootedModel];

@[simp, grind =]
lemma LogicGLBetaMinus.eq_trace [DecidableEq α] {Beta : Set ℕ} (hCf : Betaᶜ.Finite) :
    (LogicGLBetaMinus Beta hCf : Logic α).trace = Beta := by
  have hclosure : ∀ A ∈ (LetterlessFormulaSet.lift {TBBMinus _ hCf} : FormulaSet α), ∀ s,
      A⟦s⟧ ∈ (LetterlessFormulaSet.lift {TBBMinus _ hCf} : FormulaSet α) := by
    rintro A hA s;
    simp only [LetterlessFormulaSet.lift, Set.image_singleton, Set.mem_singleton_iff] at hA ⊢;
    simp [hA];
  apply Eq.trans (eq_LogicGL_quasiExtension_trace hclosure);
  simp only [LetterlessFormulaSet.lift, Set.image_singleton, FormulaSet.trace_singleton,
    Formula.trace_lift, LetterlessFormula.trace_TBBMinus hCf, compl_compl];

/-- `LogicGLBetaMinus` only depends on `Beta` (the finiteness proof of `Betaᶜ` is
irrelevant, by proof irrelevance). -/
lemma LogicGLBetaMinus.congr [DecidableEq α] {Beta₁ Beta₂ : Set ℕ} (h : Beta₁ = Beta₂)
    (hCf₁ : Beta₁ᶜ.Finite) (hCf₂ : Beta₂ᶜ.Finite) :
    (LogicGLBetaMinus Beta₁ hCf₁ : Logic α) = LogicGLBetaMinus Beta₂ hCf₂ := by
  subst h;
  rfl;

lemma subset_LogicGLAlpha_LogicS : LogicGLAlpha Alpha ⊆ @LogicS α := by
  intro C hC;
  induction hC with
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
    apply LogicGL.iff_forces_root.mpr;
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
    apply LogicGL.iff_forces_root.mpr;
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

/--
  If `Beta` is the universal set, `LogicGLBetaMinus Beta hCf` proves `⊥`: once `Beta⁻`'s
  cofiniteness assumption is instantiated at `Beta = Set.univ`, the `TBBMinus` axiom
  ranges over the empty set and hence has empty spectrum, so it entails everything.
  Extracted from the proof of `subset_LogicS_addTBB_compl_trace_of_subset_LogicS` in
  Lemma 49 of [AB05].
-/
lemma LogicGLBetaMinus.bot_mem_of_eq_univ {hCf : (Set.univ : Set ℕ)ᶜ.Finite} :
    (⊥ : Formula α) ∈ LogicGLBetaMinus Set.univ hCf := by
  apply Logic.sumQuasiNormal.mdp (Logic.sumQuasiNormal.mem₁ ?_)
    (Logic.sumQuasiNormal.mem₂ ⟨TBBMinus _ hCf, rfl, rfl⟩);
  have hD : (((TBBMinus _ hCf : LetterlessFormula)) 🡒 ⊥) ∈ LogicGL := by
    apply iff_GL_proves_imp_GL_subset_spectrum.mpr;
    have hsp : LetterlessFormula.spectrum (TBBMinus _ hCf) = ∅ := by
      have h := LetterlessFormula.trace_TBBMinus (s := (Set.univ : Set ℕ)ᶜ) hCf;
      rw [LetterlessFormula.trace, compl_inj_iff] at h;
      rw [h];
      simp;
    rw [hsp];
    exact Set.empty_subset _;
  exact ProvableHilbert.lift (α := α) hD;

end

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

variable {T U : FirstOrder.ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/--
  If `n` is in the trace of the provability logic of `T` relative to `U`, then `TBB n`
  is a theorem of it. Lemma 46 and Corollary 47 in [AB05], stated directly for
  `provabilityLogicRelativeTo` via the Solovay construction.
-/
theorem provable_TBB_of_mem_trace {n : ℕ}
    (h : n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace) :
    (TBB n : Formula α) ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  obtain ⟨A, hA_L, hA_tr⟩ : ∃ A ∈ (T.provabilityLogicRelativeTo U : Logic α), n ∈ A.trace := by
    simpa [Logic.trace, FormulaSet.trace] using h;
  obtain ⟨κ, _, M, _, _, rfl, hr⟩ := Formula.iff_mem_trace.mp hA_tr;
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences T (M.extendRoot 1);
  -- Each Solovay sentence implies the interpretation of `A 🡒 TBB M.height`.
  have key : ∀ i : (M.extendRoot 1).World,
      𝗜𝚺₁ ⊢ S.σ i 🡒 ((A 🡒 TBB M.height).interpret S.realization) := by
    rintro (x | i);
    . -- original world: use the main lemma with the semantic claim
      apply S.mainlemma (i := Sum.inl x) (by simp [RootedModel.extendRoot, Fin.posLast]);
      intro hAx;
      by_cases hx : x = M.root.1;
      . subst hx;
        exact absurd (RootedModel.extendRoot.same_forces_embed.mp hAx) hr;
      . apply Model.iff_forces_TBB_neq_rank.mpr;
        rw [show Sum.inl x = RootedModel.extendRoot.embed (M := M) (n := 1) x from rfl,
          RootedModel.extendRoot.Ext1.eq_embed_original_rank_original_rank];
        exact fun hcon => hx (RootedModel.iff_eq_rank_height_is_root.mp hcon);
    . -- the new root: chain through `SC2` and the negative main lemma
      have b₁ : 𝗜𝚺₁ ⊢ S.σ (Sum.inr i) 🡒 T.standardProvability.dia (S.σ (Sum.inl M.root.1)) :=
        S.SC2 _ _ (by simp [Model.Rel]);
      have b₂ : 𝗜𝚺₁ ⊢ S.σ (Sum.inl M.root.1) 🡒
          ∼((□^[M.height]⊥ : Formula α).interpret S.realization) := by
        apply S.mainlemma_neg (by simp [RootedModel.extendRoot, Fin.posLast]);
        apply Model.iff_rank_lt_forces_boxItr_bot.not.mp;
        rw [show (Sum.inl M.root.1 : (M.extendRoot 1).World)
          = RootedModel.extendRoot.embed (M := M) (n := 1) M.root.1 from rfl,
          RootedModel.extendRoot.Ext1.eq_embed_original_rank_original_rank];
        exact lt_irrefl _;
      have b₃ : 𝗜𝚺₁ ⊢ T.standardProvability.dia (S.σ (Sum.inl M.root.1)) 🡒
          ∼(T.standardProvability ((□^[M.height]⊥ : Formula α).interpret S.realization)) :=
        contra! $ T.standardProvability.mono' $ CN!_of_CN!_right b₂;
      have b₄ : (□^[M.height + 1]⊥ : Formula α).interpret S.realization
          = T.standardProvability ((□^[M.height]⊥ : Formula α).interpret S.realization) := by
        simp only [Formula.interpret_boxItr, Function.iterate_succ_apply'];
      simp only [Formula.interpret, TBB, b₄];
      cl_prover [b₁, b₃];
  have main : 𝗜𝚺₁ ⊢ ((A 🡒 TBB M.height).interpret S.realization) := by
    have := left_Udisj!_intro _ key;
    cl_prover [this, S.SC4];
  intro f;
  have h₃ : U ⊢ ((TBB M.height : Formula α).interpret S.realization) := by
    have h₁ : U ⊢ (A.interpret S.realization) 🡒 ((TBB M.height : Formula α).interpret S.realization) :=
      WeakerThan.pbl main;
    exact h₁ ⨀ (hA_L S.realization);
  have e : ∀ g : StandardRealization α T,
      (TBB M.height : Formula α).interpret g
      = LetterlessFormula.interpret T.standardProvability (TBB M.height) := by
    intro g;
    rw [← LetterlessFormula.eq_lift_TBB (α := α), LetterlessFormula.interpret_lift];
  show U ⊢ (TBB M.height : Formula α).interpret f;
  rw [e f];
  rw [e S.realization] at h₃;
  exact h₃;

/--
  If the trace of the provability logic of `T` relative to `U` is coinfinite, then it
  equals `GLα` of its trace. Corollary 48 in [AB05].
-/
theorem eq_provabilityLogic_LogicGLAlpha_of_coinfinite_trace [DecidableEq α]
    (hCi : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Infinite) :
    (T.provabilityLogicRelativeTo U : Logic α)
      = LogicGLAlpha (T.provabilityLogicRelativeTo U : Logic α).trace := by
  apply Set.Subset.antisymm;
  . exact subset_LogicGLAlpha_of_trace_coinfinite hCi;
  . intro A hA;
    induction hA with
    | mem₁ hA =>
      intro f;
      exact WeakerThan.pbl (LogicGL.arithmetical_soundness hA);
    | mem₂ hA =>
      obtain ⟨B, ⟨n, hn, rfl⟩, rfl⟩ := hA;
      rw [LetterlessFormula.eq_lift_TBB];
      exact provable_TBB_of_mem_trace hn;
    | mdp _ _ ihAB ihA =>
      intro f;
      exact (ihAB f) ⨀ (ihA f);
    | subst _ ihA =>
      intro f;
      rw [Formula.interpret_subst];
      exact ihA _;

/--
  If the provability logic of `T` relative to `U` is not contained in `S`,
  then its trace is cofinite (the first half of the proof of Lemma 49 in [AB05]).
-/
lemma cofinite_trace_of_not_subset_LogicS [DecidableEq α]
    (hS : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ LogicS) :
    (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite := by
  by_contra hInf;
  apply hS;
  rw [eq_provabilityLogic_LogicGLAlpha_of_coinfinite_trace (by exact hInf)];
  exact subset_LogicGLAlpha_LogicS;


section

open LO.FirstOrder.ProvabilityAbstraction.Provability

variable {A B : Formula α}

omit [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] in
lemma provabilityLogic_mdp
    (h₁ : (A 🡒 B) ∈ (T.provabilityLogicRelativeTo U : Logic α))
    (h₂ : A ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    B ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun f => (h₁ f) ⨀ (h₂ f)

lemma provabilityLogic_of_GL (h : A ∈ LogicGL) :
    A ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun _ => WeakerThan.pbl (LogicGL.arithmetical_soundness h)

lemma provabilityLogic_lconj {Γ : FormulaList α}
    (h : ∀ B ∈ Γ, B ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    (⋀Γ) ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  match Γ with
  | [] => exact provabilityLogic_of_GL ProvableHilbert.top;
  | [B] => simpa using h B (by simp);
  | B :: C :: Γ =>
    exact provabilityLogic_mdp
      (provabilityLogic_mdp (provabilityLogic_of_GL ProvableHilbert.andIntro) (h B (by simp)))
      (provabilityLogic_lconj (Γ := C :: Γ) (by grind));

lemma provabilityLogic_fconj {Γ : FormulaFinset α}
    (h : ∀ B ∈ Γ, B ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    (⋀Γ) ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  provabilityLogic_lconj (by simpa)

private lemma spectrum_TBBMinus' {s : Set ℕ} (hs : s.Finite) :
    LetterlessFormula.spectrum (TBBMinus s) = s :=
  compl_inj_iff.mp (LetterlessFormula.trace_TBBMinus hs)

section

variable [DecidableEq α]

/--
  If the provability logic `L` of `T` relative to `U` is not contained in `S`, then it
  proves the lifted `TBBMinus` axiom of its trace (the key step of Lemma 49 in [AB05],
  via the Solovay construction and the reflexive main lemma).
-/
theorem provable_TBBMinus_of_not_subset_LogicS
    (hS : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ LogicS) :
    (LetterlessFormula.lift (TBBMinus _ (cofinite_trace_of_not_subset_LogicS hS)) : Formula α)
      ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  set L := (T.provabilityLogicRelativeTo U : Logic α) with hL;
  have hcof := cofinite_trace_of_not_subset_LogicS hS;
  -- Take `A ∈ L` with `A ∉ S`; then `GL ⊬ ⋀A.subfmlsS 🡒 A`.
  obtain ⟨A, hA₁, hA₂⟩ := Set.not_subset.mp hS;
  replace hA₂ : ((⋀A.subfmlsS) 🡒 A) ∉ LogicGL :=
    fun hc => hA₂ (LogicS.iff_provable_S_provable_GL.mpr hc);
  -- Extract a finite rooted countermodel `M₁` whose root is `A`-reflexive but refutes `A`.
  have := (LogicGL.iff_forces_root (A := (⋀A.subfmlsS) 🡒 A)).not.mp hA₂;
  push Not at this;
  obtain ⟨κ₁, hne, M₁, hfgl, hroot⟩ := this;
  haveI := hne; haveI := hfgl;
  haveI : Fintype M₁.World := Fintype.ofFinite _;
  obtain ⟨hconj, hnA⟩ := Model.World.not_forces_imp.mp hroot;
  have ha : ∀ B, (□B) ∈ A.subfmls → M₁.root.1 ⊩ ((□B) 🡒 B) := by
    intro B hB;
    exact Model.World.forces_fconj.mp hconj _
      (Finset.mem_image_of_mem _ (FormulaFinset.iff_mem_prebox_mem.mpr hB));
  -- `R`: the members of `L.trace` below the height of `M₁`; `B`: `A` with those `TBB`s.
  let R : Finset ℕ :=
    Set.Finite.inter_of_left (s := (Finset.range M₁.height : Set ℕ)) (t := L.trace)
      (Finset.finite_toSet _) |>.toFinset;
  let B : Formula α := A ⋏ ⋀(R.image (TBB (α := α)));
  have hB : B ∈ L := by
    apply provabilityLogic_mdp (provabilityLogic_mdp (provabilityLogic_of_GL ProvableHilbert.andIntro) hA₁);
    apply provabilityLogic_fconj;
    intro C hC;
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC;
    apply provable_TBB_of_mem_trace;
    have : i ∈ (Finset.range M₁.height : Set ℕ) ∩ L.trace := by simpa [R] using hi;
    exact this.2;
  -- The Solovay sentences of `M₁.extendRoot 1`.
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences T (M₁.extendRoot 1);
  -- Each Solovay sentence implies the interpretation of `B 🡒 lift (TBBMinus L.traceᶜ)`.
  have key : ∀ i : (M₁.extendRoot 1).World,
      𝗜𝚺₁ ⊢ S.σ i 🡒 ((B 🡒 (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α)).interpret S.realization) := by
    rintro (x | i);
    . -- original worlds: semantic claim through the main lemma
      apply S.mainlemma (i := Sum.inl x) (by simp [RootedModel.extendRoot, Fin.posLast]);
      intro hBx;
      apply Model.iff_forces_lift_rank_mem_spectrum.mpr;
      rw [spectrum_TBBMinus' hcof];
      rw [show Sum.inl x = RootedModel.extendRoot.embed (M := M₁) (n := 1) x from rfl,
        RootedModel.extendRoot.Ext1.eq_embed_original_rank_original_rank];
      intro hmem;
      replace hBx : x ⊩ B := RootedModel.extendRoot.same_forces_embed.mp hBx;
      obtain ⟨hAx, hTx⟩ := Model.World.forces_and.mp hBx;
      by_cases hx : x = M₁.root.1;
      . subst hx; exact hnA hAx;
      . have hlt : Model.World.rank x < M₁.height := RootedModel.rank_lt_height (M₁.root.2 x hx);
        have : x ⊩ TBB (Model.World.rank x) := by
          apply Model.World.forces_fconj.mp hTx;
          apply Finset.mem_image_of_mem;
          simp only [R, Set.Finite.mem_toFinset, Set.mem_inter_iff, Finset.coe_range, Set.mem_Iio];
          exact ⟨hlt, hmem⟩;
        exact Model.iff_forces_TBB_neq_rank.mp this rfl;
    . -- the new root: the reflexive main lemma kills `A`, hence `B`
      have H₁ : 𝗜𝚺₁ ⊢ S.σ (Sum.inr i) 🡒 ∼(A.interpret S.realization) := by
        rw [show (Sum.inr i : (M₁.extendRoot 1).World) = (M₁.extendRoot 1).root.1 by
          congr 1;
          apply Fin.ext;
          have := i.2;
          simp only [Fin.posLast, PNat.natPred, PNat.val_ofNat] at this ⊢;
          omega];
        exact SolovaySentences.rfl_mainlemma ha (Formula.mem_subfmls_self) |>.2 hnA;
      simp only [B, Formula.interpret];
      cl_prover [H₁];
  have main : 𝗜𝚺₁ ⊢ ((B 🡒 (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α)).interpret S.realization) := by
    have := left_Udisj!_intro _ key;
    cl_prover [this, S.SC4];
  -- Conclude membership in `L` via letterless independence of the realization.
  intro f;
  have h₃ : U ⊢ ((LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret S.realization) := by
    have h₁ : U ⊢ (B.interpret S.realization) 🡒
        ((LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret S.realization) :=
      WeakerThan.pbl main;
    exact h₁ ⨀ (hB S.realization);
  have e : ∀ g : StandardRealization α T,
      (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret g
      = LetterlessFormula.interpret T.standardProvability (TBBMinus _ hcof) := by
    intro g;
    rw [LetterlessFormula.interpret_lift];
  show U ⊢ (LetterlessFormula.lift (TBBMinus _ hcof) : Formula α).interpret f;
  rw [e f];
  rw [e S.realization] at h₃;
  exact h₃;

/--
  **Lemma 49 in [AB05]**: if the provability logic `L` of `T` relative to `U` is not
  contained in `S`, then `L.trace` is cofinite and `L = GLβ⁻ (L.trace)`.
-/
theorem eq_provabilityLogic_LogicGLBetaMinus_of_not_subset_LogicS
    (hS : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ LogicS) :
    (T.provabilityLogicRelativeTo U : Logic α)
      = LogicGLBetaMinus (T.provabilityLogicRelativeTo U : Logic α).trace
          (cofinite_trace_of_not_subset_LogicS hS) := by
  apply Set.Subset.antisymm;
  . exact subset_LogicGLBetaMinus_of_trace_cofinite _;
  . intro A hA;
    induction hA with
    | mem₁ hA =>
      exact provabilityLogic_of_GL hA;
    | mem₂ hA =>
      obtain ⟨B, hB, rfl⟩ := hA;
      rw [show B = TBBMinus _ (cofinite_trace_of_not_subset_LogicS hS) from hB];
      exact provable_TBBMinus_of_not_subset_LogicS hS;
    | mdp _ _ ihAB ihA =>
      exact provabilityLogic_mdp ihAB ihA;
    | subst _ ihA =>
      intro f;
      rw [Formula.interpret_subst];
      exact ihA _;

end

end


/-- `n ∈ L.trace` whenever `TBB n ∈ L`. -/
lemma mem_trace_of_provable_TBB {L : Logic α} {n : ℕ} (h : (TBB n : Formula α) ∈ L) :
    n ∈ L.trace := by
  apply Set.mem_iUnion₂.mpr;
  exact ⟨TBB n, h, by rw [Formula.trace_TBB]; simp⟩;

/--
  If the trace of the provability logic of `T` relative to `U` is `ω` (i.e. all of `ℕ`),
  then it contains `GLαω`. Corollary 50 (half) in [AB05].
-/
theorem subset_LogicA_of_univ_trace :
    letI L : Logic α := T.provabilityLogicRelativeTo U;
    L.trace = Set.univ → LogicA ⊆ L := by
  intro hT A hA;
  induction hA with
  | mem₁ hA =>
    intro f;
    exact WeakerThan.pbl (LogicGL.arithmetical_soundness hA);
  | mem₂ hA =>
    obtain ⟨B, ⟨n, _, rfl⟩, rfl⟩ := hA;
    rw [LetterlessFormula.eq_lift_TBB];
    exact provable_TBB_of_mem_trace (hT ▸ Set.mem_univ n);
  | mdp _ _ ihAB ihA =>
    intro f;
    exact (ihAB f) ⨀ (ihA f);
  | subst _ ihA =>
    intro f;
    rw [Formula.interpret_subst];
    exact ihA _;


end
