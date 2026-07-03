module

public import SeqPL.ProvabilityLogic.Classification.Trace
public import SeqPL.Formula.Map
public import SeqPL.Kripke.Map

@[expose] public section

open Classical
open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open Model Model.World

universe u v

section kripke

variable {α β : Type u} {κ : Type v} [Nonempty κ]

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
