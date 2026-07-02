module

public import SeqPL.ProvabilityLogic.Classification.Trace
public import SeqPL.Formula.Map

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u v

section interpret

variable {α β : Type*}
variable {L : FirstOrder.Language} [L.ReferenceableBy L] {T₀ T : FirstOrder.Theory L}
  {𝔅 : Provability T₀ T}

/-- Interpreting a renamed formula is interpreting under the pulled-back realization. -/
lemma Formula.interpret_map {f : Realization β 𝔅} {g : α → β} {A : Formula α} :
    Formula.interpret f (A.map g) = Formula.interpret (⟨f.val ∘ g⟩ : Realization α 𝔅) A := by
  induction A with
  | atom a => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [Formula.map_imp, Formula.interpret, ihA, ihB]
  | box A ih => simp only [Formula.map_box, Formula.interpret, ih]

/-- Two realizations agreeing on the atoms of `A` interpret `A` identically. -/
lemma Formula.interpret_congr_atoms [DecidableEq α] {f₁ f₂ : Realization α 𝔅} {A : Formula α}
    (h : ∀ a ∈ A.atoms, f₁.val a = f₂.val a) :
    Formula.interpret f₁ A = Formula.interpret f₂ A := by
  induction A with
  | atom a => exact h a (by simp [Formula.atoms])
  | bot => rfl
  | imp A B ihA ihB =>
    simp only [Formula.interpret];
    rw [ihA (fun a ha => h a (by simp [Formula.atoms, ha])),
      ihB (fun a ha => h a (by simp [Formula.atoms, ha]))];
  | box A ih =>
    simp only [Formula.interpret];
    rw [ih (fun a ha => h a (by simpa [Formula.atoms] using ha))];

end interpret


section kripke

variable {α β : Type u} {κ : Type v} [Nonempty κ]

/-- Forcing only depends on the model through its frame and valuation. -/
lemma Model.forces_congr {M₁ M₂ : Model κ α} (hR : M₁.Rel' = M₂.Rel')
    (hV : ∀ x a, M₁.Val' x a ↔ M₂.Val' x a) {A : Formula α} {x : κ} :
    Model.World.Forces (M := M₁) x A ↔ Model.World.Forces (M := M₂) x A := by
  induction A generalizing x with
  | atom a => exact hV x a
  | bot => exact Iff.rfl
  | imp A B ihA ihB => simp only [Model.World.Forces]; rw [ihA, ihB]
  | box A ih =>
    simp only [Model.World.Forces];
    constructor;
    · intro h y hy;
      have hy' : M₁.Rel' x y := by rw [hR]; exact hy;
      exact ih.mp (h y hy');
    · intro h y hy;
      have hy' : M₂.Rel' x y := by rw [← hR]; exact hy;
      exact ih.mpr (h y hy');

/-- Pulling back the valuation along an atom renaming (frame unchanged). -/
abbrev Model.mapModel (M : Model κ β) (f : α → β) : Model κ α where
  Rel' := M.Rel'
  Val' x a := M.Val' x (f a)

/-- Forcing a renamed formula is forcing in the pulled-back model. -/
lemma Model.forces_map {M : Model κ β} {f : α → β} {A : Formula α} {x : M.World} :
    x ⊩ A.map f ↔ Model.World.Forces (M := M.mapModel f) x A := by
  induction A generalizing x with
  | atom a => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp A B ihA ihB => simp only [Formula.map_imp, Model.World.Forces]; rw [ihA, ihB]
  | box A ih =>
    simp only [Formula.map_box, Model.World.Forces];
    constructor;
    · intro h y hy; exact ih.mp (h y hy);
    · intro h y hy; exact ih.mpr (h y hy);

/-- Extending the atom type of a model by a fresh atom which is false everywhere. -/
abbrev Model.optionExtend (M : Model κ α) : Model κ (Option α) where
  Rel' := M.Rel'
  Val' x a := match a with | some a => M.Val' x a | none => False

instance {M : Model κ α} [h : M.IsFiniteGL] : (M.optionExtend).IsFiniteGL where
  trans := h.trans
  irrefl := h.irrefl
  finite := h.finite

/--
  Non-provability in `D` transfers along the fresh-atom embedding, semantically via
  pseudo-tail models.
-/
lemma LogicD.not_provable_map_some [DecidableEq α] {A : Formula α}
    (h : A ∉ LogicD) : (A.map some) ∉ LogicD := by
  intro hc;
  apply h;
  apply LogicD.provability_TFAE.out 1 0 |>.mp;
  intro κ _ M _ r o;
  have hall := LogicD.provability_TFAE (A := A.map some) |>.out 0 1 |>.mp hc;
  have hfrc := hall (κ := κ) (M.optionExtend) r
    (fun a => match a with | some a => o a | none => False);
  have e : Model.World.Forces
      (M := ((M.optionExtend).toPseudoTail r
        (fun a => match a with | some a => o a | none => False)).toModel)
      (((M.optionExtend).toPseudoTail r
        (fun a => match a with | some a => o a | none => False)).root.1) (A.map some)
      ↔ Model.World.Forces (M := (M.toPseudoTail r o).toModel)
        ((M.toPseudoTail r o).root.1) A := by
    apply Iff.trans Model.forces_map;
    apply Model.forces_congr rfl;
    intro x a;
    match x with
    | .inl x => exact Iff.rfl
    | .inr i =>
      by_cases hi : i = (⊤ : ℕ∞) <;> simp [hi];
  exact e.mp hfrc;

end kripke
