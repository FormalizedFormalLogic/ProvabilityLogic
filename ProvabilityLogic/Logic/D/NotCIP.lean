module

public import ProvabilityLogic.Logic.D.Basic
public import ProvabilityLogic.Logic.GL.Fixedpoint

/-!
# Dzhaparidze's logic `D` does not possess Craig's interpolation property

The counterexample is `∼A 🡒 B` for `A = □(□b ⋎ a) 🡒 □b` and `B = □(a 🡒 □c) 🡒 □c`: it is
provable in `D`, but has no interpolant.

## References

- [Bek89, Section 8]
-/

@[expose]
public section

universe u
variable {α : Type u}

namespace LogicD

variable [DecidableEq α]

abbrev counterexampleCIP_A (a b : Formula α) : Formula α := □(□b ⋎ a) 🡒 □b

abbrev counterexampleCIP_B (a c : Formula α) : Formula α := □(a 🡒 □c) 🡒 □c

section

variable {a b c : Formula α}

/-- - [Bek89, Lemma 9] -/
lemma provable_counterexample_imp :
  (∼(counterexampleCIP_A a b) 🡒 counterexampleCIP_B a c) ∈ LogicD := by
  have step2 : ((□(□b ⋎ a) ⋏ □(a 🡒 □c)) 🡒 □(□b ⋎ □c)) ∈ LogicGL := by
    apply LogicGL.provable_of_valid;
    intro κ _ M _ x;
    grind;
  have step4 : ((□(□b ⋎ a) ⋏ □(a 🡒 □c)) 🡒 (□b ⋎ □c)) ∈ LogicD :=
    provable_imp_trans (provable_of_provable_GL step2) provable_axiomD;
  have taut :
      (((□(□b ⋎ a) ⋏ □(a 🡒 □c)) 🡒 (□b ⋎ □c)) 🡒
        (∼(counterexampleCIP_A a b) 🡒 counterexampleCIP_B a c)) ∈ LogicGL := by
    apply LogicGL.provable_of_valid;
    intro κ _ M _ x;
    grind;
  exact provable_of_provable_GL_imp taut step4;

end

open Model

section

/-!
### D-models as pseudo-tails

A D-model is realized here as the pseudo-tail `M.toPseudoTail M.root o` of a rooted finite
`GL` model `M`: the root `chainPoint ⊤` is the lower element, carrying the free valuation
`o`, and the descending chain `chainPoint n` together with `M` is the tail scale, carrying
the reference valuation `M.Val M.root`. Basing the pseudo-tail at the root of `M` is what
makes the counter-valuations below — which flip an atom on the chain, hence also at
`embed M.root` — leave `□b`/`□c` undisturbed at the other worlds of `M`.
-/

variable {κ : Type u} [Nonempty κ] {M₁ M₂ : Model κ α} {a b c : α} {C : Formula α}

open Model.World

/-- A refinement of `Model.forces_congr`, sensitive only to the atoms of `A`. -/
lemma forces_congr_atoms
  (hR : M₁.Rel' = M₂.Rel') {A : Formula α} {x : κ}
  (hV : ∀ x a, a ∈ A.atoms → (M₁.Val' x a ↔ M₂.Val' x a)) :
  x ⊩[M₁] A ↔ x ⊩[M₂] A := by
  induction A generalizing x with
  | atom a => exact hV x a (by simp [Formula.atoms])
  | bot => exact Iff.rfl
  | imp A B ihA ihB =>
    simp only [Model.World.Forces];
    rw [ihA (fun x a ha => hV x a (by simp [Formula.atoms, ha])),
      ihB (fun x a ha => hV x a (by simp [Formula.atoms, ha]))];
  | box A ih =>
    simp only [Model.World.Forces];
    constructor;
    . intro h y hy;
      have hy' : M₁.Rel' x y := by rw [hR]; exact hy;
      exact (ih (fun x a ha => hV x a (by simpa [Formula.atoms] using ha))).mp (h y hy');
    . intro h y hy;
      have hy' : M₂.Rel' x y := by rw [← hR]; exact hy;
      exact (ih (fun x a ha => hV x a (by simpa [Formula.atoms] using ha))).mpr (h y hy');

omit [DecidableEq α] in
lemma not_rel_root_of_rooted (M : RootedModel κ α)
  [M.IsFiniteGL] (x : κ) : ¬M.toModel.Rel x M.root.1 := by
  intro h;
  by_cases hx : x = M.root.1;
  . subst hx; exact Std.Irrefl.irrefl _ h;
  . exact Std.Irrefl.irrefl _ (IsTrans.trans _ _ _ (M.root.2 x hx) h);

/-- The model `M` with the valuation of the atom `d` overwritten to hold exactly off the
root. -/
abbrev flipModel (M : RootedModel κ α) (d : α) :
  Model κ α where
  Rel' := M.toModel.Rel'
  Val' x a := if a = d then x ≠ M.root.1 else M.toModel.Val' x a

instance {M : RootedModel κ α} [h : M.IsFiniteGL] {d : α} :
  (flipModel M d).IsFiniteGL where
  trans := h.trans
  irrefl := h.irrefl
  finite := h.finite

variable {a b c d : α}

lemma val_toPseudoTail_flipModel {M : RootedModel κ α}
  {o : α → Prop} (had : a ≠ d) (x : M.World ⊕ ℕ∞) :
  (M.toModel.toPseudoTail M.root.1 o).Val' x a ↔ ((flipModel M d).toPseudoTail M.root.1 o).Val' x a := by
  grind;

/--
An interpolant `C` for `∼A 🡒 B` is forced at the lower element of a pseudo-tail D-model
exactly when the shared atom `a` holds on its tail scale; in particular, independently of
the lower valuation `o`.

- [Bek89, Lemma 10]
-/
lemma interpolant_root_forces_iff
  (hab : a ≠ b) (hac : a ≠ c)
  (hCant : (∼(counterexampleCIP_A (#a) (#b)) 🡒 C) ∈ LogicD)
  (hCsuc : (C 🡒 counterexampleCIP_B (#a) (#c)) ∈ LogicD)
  (hCatoms : C.atoms ⊆ {a})
  (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop) :
  (M.toModel.toPseudoTail M.root.1 o).root.1
    ⊩[(M.toModel.toPseudoTail M.root.1 o).toModel] C ↔ M.Val M.root.1 a := by
  have hCp : ∀ e ∈ C.atoms, e = a := fun e ha => Finset.mem_singleton.mp (hCatoms ha);
  constructor;
  . intro hC;
    by_contra hp;
    -- Flip `c`, so that `□c` fails at the lower element but nowhere else.
    have hB := forces_pseudoTail_root_of_provable hCsuc (flipModel M c) M.root.1 o;
    have hC' : toPseudoTail.chainPoint ⊤ ⊩[((flipModel M c).toPseudoTail M.root.1 o).toModel] C :=
      (forces_congr_atoms
        (M₁ := (M.toModel.toPseudoTail M.root.1 o).toModel)
        (M₂ := ((flipModel M c).toPseudoTail M.root.1 o).toModel)
        (by funext x y; rcases x with x | i <;> rcases y with y | j <;> rfl)
        (fun x e ha => by rw [hCp e ha]; exact val_toPseudoTail_flipModel hac x)).mp hC;
    have hBf := hB hC';
    have hant : toPseudoTail.chainPoint ⊤ ⊩[((flipModel M c).toPseudoTail M.root.1 o).toModel]
        (□((#a) 🡒 □(#c))) := by
      rintro (x | m) hy;
      . intro _;
        rintro (z | j) hz;
        . show (if c = c then z ≠ M.root.1 else M.toModel.Val' z c);
          rw [ite_eq_left rfl];
          rintro rfl;
          exact not_rel_root_of_rooted M x hz;
        . exact False.elim hz;
      . intro hpm;
        exfalso;
        apply hp;
        have : (
          if m = (⊤ : ℕ∞) then o a
          else if a = c then M.root.1 ≠ M.root.1
          else M.toModel.Val' M.root.1 a
        ) := hpm;
        grind;
    have hc0 : ¬(toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞) ⊩[((flipModel M c).toPseudoTail M.root.1 o).toModel] (#c)) := by
      show ¬(if ((0 : ℕ) : ℕ∞) = (⊤ : ℕ∞) then o c else
        if c = c then M.root.1 ≠ M.root.1 else M.toModel.Val' M.root.1 c);
      rw [ite_eq_right (ENat.natCast_lt_top 0).ne, ite_eq_left rfl];
      simp;
    exact hc0 (hBf hant (toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞)) (ENat.natCast_lt_top 0));
  . intro hp;
    by_contra hC;
    -- Flip `b`, so that `□b` fails at the lower element but nowhere else.
    have hA := forces_pseudoTail_root_of_provable hCant (flipModel M b) M.root.1 o;
    have hnA : toPseudoTail.chainPoint ⊤ ⊩[((flipModel M b).toPseudoTail M.root.1 o).toModel]
        (∼(counterexampleCIP_A (#a) (#b))) := by
      intro hAf;
      have hante : toPseudoTail.chainPoint ⊤ ⊩[((flipModel M b).toPseudoTail M.root.1 o).toModel]
          (□(□(#b) ⋎ (#a))) := by
        rintro (x | m) hy;
        . apply forces_or.mpr;
          left;
          rintro (z | j) hz;
          . show (if b = b then z ≠ M.root.1 else M.toModel.Val' z b);
            rw [ite_eq_left rfl];
            rintro rfl;
            exact not_rel_root_of_rooted M x hz;
          . grind;
        . apply forces_or.mpr;
          right;
          show (
            if m = (⊤ : ℕ∞) then o a
            else if a = b then M.root.1 ≠ M.root.1
            else M.toModel.Val' M.root.1 a
          );
          grind;
      have hb0 : ¬(toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞) ⊩[((flipModel M b).toPseudoTail M.root.1 o).toModel] (#b)) := by
        show ¬(if ((0 : ℕ) : ℕ∞) = (⊤ : ℕ∞) then o b else
          if b = b then M.root.1 ≠ M.root.1 else M.toModel.Val' M.root.1 b);
        rw [ite_eq_right (ENat.natCast_lt_top 0).ne, ite_eq_left rfl];
        simp;
      exact hb0 (hAf hante (toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞)) (ENat.natCast_lt_top 0));
    apply hC;
    exact (forces_congr_atoms
      (M₁ := (M.toModel.toPseudoTail M.root.1 o).toModel)
      (M₂ := ((flipModel M b).toPseudoTail M.root.1 o).toModel)
      (by funext x y; rcases x with x | i <;> rcases y with y | j <;> rfl)
      (fun x e ha => by rw [hCp e ha]; exact val_toPseudoTail_flipModel hab x)).mpr (hA hnA);

end

section

/-!
### Modalization

Lemmas relating `Formula.modalize` and `Formula.Modalized` to forcing in pseudo-tail
D-models.
-/

variable {A : Formula α}

variable {κ : Type u} [Nonempty κ] {C : Formula α} {M : Model κ α}
  {r : M.World} {o o' : α → Prop}

lemma forces_modalize {x : κ}
  (h : ∀ a ∈ A.atoms, ¬M x a) :
  x ⊩[M] A.modalize ↔ x ⊩[M] A := by
  induction A <;> grind;

omit [DecidableEq α] in
lemma forces_pseudoTail_ne_root_o_indep (A : Formula α) :
  ∀ z : (M.toPseudoTail r o).World, z ≠ toPseudoTail.chainPoint ⊤ →
    (z ⊩[(M.toPseudoTail r o).toModel] A ↔
      z ⊩[(M.toPseudoTail r o').toModel] A) := by
  have hsucc : ∀ z y : (M.toPseudoTail r o).World,
      (M.toPseudoTail r o).Rel z y → y ≠ toPseudoTail.chainPoint ⊤ := by
    rintro (x | i) y hy rfl;
    . exact toPseudoTail.not_rel_embed_chainPoint hy;
    . exact absurd (toPseudoTail.rel_chainPoint_chainPoint.mp hy) not_top_lt;
  induction A with
  | atom a =>
    rintro (x | i) hz;
    . exact Iff.rfl;
    . grind;
  | bot => exact fun z _ => Iff.rfl
  | imp A B ihA ihB =>
    intro z hz;
    simp only [Model.World.Forces];
    rw [ihA z hz, ihB z hz];
  | box A ih =>
    intro z hz;
    constructor;
    . intro h y hy;
      exact (ih y (hsucc z y hy)).mp (h y hy);
    . intro h y hy;
      exact (ih y (hsucc z y hy)).mpr (h y hy);

omit [DecidableEq α] in
/-- A `Modalized` formula is forced at the pseudo-tail root independently of the lower
valuation `o`. -/
lemma forces_root_modalized_o_indep {A : Formula α} (hA : A.Modalized) :
  toPseudoTail.chainPoint ⊤ ⊩[(M.toPseudoTail r o).toModel] A ↔
    toPseudoTail.chainPoint ⊤ ⊩[(M.toPseudoTail r o').toModel] A := by
  have hsucc : ∀ y : (M.toPseudoTail r o).World,
      (M.toPseudoTail r o).Rel (toPseudoTail.chainPoint ⊤) y → y ≠ toPseudoTail.chainPoint ⊤ := by
    rintro y hy rfl;
    exact absurd (toPseudoTail.rel_chainPoint_chainPoint.mp hy) not_top_lt;
  induction A with
  | atom a => exact (hA a rfl).elim
  | bot => exact Iff.rfl
  | imp A B ihA ihB =>
    have hA1 : A.Modalized := fun a => (hA a).1;
    have hA2 : B.Modalized := fun a => (hA a).2;
    constructor;
    . intro h hA';
      exact (ihB hA2).mp (h ((ihA hA1).mpr hA'));
    . intro h hA';
      exact (ihB hA2).mpr (h ((ihA hA1).mp hA'));
  | box A _ =>
    constructor;
    . intro h y hy;
      exact (forces_pseudoTail_ne_root_o_indep (o := o) (o' := o') A y (hsucc y hy)).mp (h y hy);
    . intro h y hy;
      exact (forces_pseudoTail_ne_root_o_indep (o := o) (o' := o') A y (hsucc y hy)).mpr (h y hy);

/-- - [Bek89, Lemma 11] -/
lemma exists_modalized_equiv_of_indep
  (hindep :
    ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL]
    (r : M.World) (o o' : α → Prop),
    (M.toPseudoTail r o).root.1 ⊩[(M.toPseudoTail r o).toModel] C ↔
    (M.toPseudoTail r o').root.1 ⊩[(M.toPseudoTail r o').toModel] C
  )
  : ∃ C', C'.Modalized ∧ (C 🡘 C') ∈ LogicD ∧ C'.atoms ⊆ C.atoms := by
  use C.modalize;
  and_intros;
  . exact Formula.modalized_modalize;
  . apply iff_forces_pseudoTail_root.mpr;
    intro κ _ M _ r o;
    -- The all-false lower valuation, at which `C` and `C.modalize` agree at the root.
    let o₀ : α → Prop := fun _ => False;
    have h0 : ∀ a ∈ C.atoms, ¬(M.toPseudoTail r o₀).toModel.Val (toPseudoTail.chainPoint ⊤) a := by
      intro a _;
      show ¬(if (⊤ : ℕ∞) = (⊤ : ℕ∞) then o₀ a else M r a);
      rw [ite_eq_left rfl];
      exact not_false;
    have key : toPseudoTail.chainPoint ⊤ ⊩[(M.toPseudoTail r o).toModel] C ↔
        toPseudoTail.chainPoint ⊤ ⊩[(M.toPseudoTail r o).toModel] (C.modalize) :=
      (hindep M r o o₀).trans ((forces_modalize h0).symm.trans
        (forces_root_modalized_o_indep Formula.modalized_modalize));
    exact Model.World.forces_iff.mpr key;
  . exact Formula.atoms_modalize_subset;

/-- - [Bek89, Lemma 12] -/
lemma not_exists_modalized_equiv_atom [Nontrivial α] :
  ¬ ∃ (C : Formula α) (a : α), C.Modalized ∧ C.atoms ⊆ {a} ∧ (C 🡘 #a) ∈ LogicS := by
  rintro ⟨C, a, hMod, hAtoms, hCp⟩;
  obtain ⟨d, hqp⟩ := exists_ne a;
  have hA : (∼C).ModalizedIn a := ⟨hMod a, trivial⟩;
  have hq : d ∉ (∼C).atoms := by
    intro hmem;
    have : d ∈ C.atoms := by simpa [Formula.atoms] using hmem;
    exact hqp (Finset.mem_singleton.mp (hAtoms this));
  -- The de Jongh–Sambin fixed point `E` of `∼C`.
  obtain ⟨E, -, hfp, -⟩ := LogicGL.fixpointTheorem (Ne.symm hqp) hA hq;
  have hSnCE : ((∼(C⟦a ↦ E⟧)) 🡘 E) ∈ LogicS :=
    LogicS.provable_of_provable_GL (by simpa using hfp);
  have hSCE : ((C⟦a ↦ E⟧) 🡘 E) ∈ LogicS := by
    have h := Logic.sumQuasiNormal.subst (s := Formula.Substitution.single a E) hCp;
    simp only [Formula.subst_iff, Formula.subst_atom,
      Formula.Substitution.single_self] at h;
    exact h;
  have taut : (((C⟦a ↦ E⟧) 🡘 E) 🡒 (((∼(C⟦a ↦ E⟧)) 🡘 E) 🡒 ⊥)) ∈ @LogicGL α := by
    apply LogicGL.provable_of_valid;
    intro κ _ M _ x;
    grind;
  exact LogicS.consistent
    (Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mdp (LogicS.provable_of_provable_GL taut) hSCE) hSnCE);

end

/--
**Dzhaparidze's logic `D` does not have Craig's interpolation property.**

- [Bek89, Theorem 2]
-/
theorem notCIP {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
  ∃ A B : Formula α, (A 🡒 B) ∈ LogicD ∧
    ¬ ∃ C : Formula α, (A 🡒 C) ∈ LogicD ∧ (C 🡒 B) ∈ LogicD ∧
      C.atoms ⊆ A.atoms ∩ B.atoms := by
  have : Nontrivial α := ⟨⟨a, b, hab⟩⟩;
  use ∼(counterexampleCIP_A (#a) (#b)), counterexampleCIP_B (#a) (#c), provable_counterexample_imp;
  rintro ⟨C, hCant, hCsuc, hCatoms⟩;
  have hAB : (∼(counterexampleCIP_A (#a) (#b))).atoms ∩
      (counterexampleCIP_B (#a) (#c)).atoms = {a} := by
    ext e;
    simp only [Formula.atoms, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton];
    grind;
  rw [hAB] at hCatoms;
  have hC'mod : C.modalize.Modalized := Formula.modalized_modalize;
  have hC'atoms : C.modalize.atoms ⊆ {a} := Formula.atoms_modalize_subset.trans hCatoms;
  have hS : (C.modalize 🡘 #a) ∈ @LogicS α := by
    apply LogicS.iff_forces_root_subfmlsS_imp.mpr;
    intro κ _ M _ hant;
    have hΓ : ∀ E ∈ (C.modalize 🡘 #a).subfmls.prebox,
        M.root.1 ⊩[M.toModel] (□E 🡒 E) := by
      intro E hE;
      exact Model.World.forces_fconj.mp hant _ (by
        simp only [Formula.subfmlsS, Finset.mem_image];
        exact ⟨E, hE, rfl⟩);
    have hC'mem : C.modalize ∈ (C.modalize 🡘 #a).subfmls := by grind;
    have hstep1 : M.root.1 ⊩[M.toModel] C.modalize ↔
        toTail.chainPoint ⊤ ⊩[(M.toModel.toTail M.root.1).toModel]
          (C.modalize) := by
      constructor;
      . intro h;
        exact (toTail.tailLemma (C.modalize)).mpr ⟨0, fun n _ =>
          (toTail.root_forces_iff_forces_nat (fun E hE => Formula.subfmls_trans hE) hΓ
            (C.modalize) hC'mem n).mp h⟩;
      . intro h;
        obtain ⟨k, hk⟩ := (toTail.tailLemma (C.modalize)).mp h;
        exact (toTail.root_forces_iff_forces_nat (fun E hE => Formula.subfmls_trans hE) hΓ
          (C.modalize) hC'mem k).mpr (hk k le_rfl);
    -- The tail model is the pseudo-tail whose lower valuation is that of the root.
    have hstep2 : toTail.chainPoint ⊤ ⊩[(M.toModel.toTail M.root.1).toModel]
        (C.modalize) ↔
        toPseudoTail.chainPoint ⊤
          ⊩[(M.toModel.toPseudoTail M.root.1 (M.toModel.Val M.root.1)).toModel] (C.modalize) :=
      Model.forces_congr
        (M₁ := (M.toModel.toTail M.root.1).toModel)
        (M₂ := (M.toModel.toPseudoTail M.root.1 (M.toModel.Val M.root.1)).toModel)
        (by funext x y; rcases x with x | i <;> rcases y with y | j <;> rfl)
        (fun x e => by
          rcases x with x | i;
          . exact Iff.rfl;
          . show M.toModel.Val M.root.1 e ↔
              (if i = (⊤ : ℕ∞) then M.toModel.Val M.root.1 e else M.toModel.Val M.root.1 e);
            rw [ite_self]);
    -- The all-false lower valuation.
    let o₀ : α → Prop := fun _ => False;
    have h0 : ∀ a ∈ C.atoms,
        ¬(M.toModel.toPseudoTail M.root.1 o₀).toModel.Val (toPseudoTail.chainPoint ⊤) a := by
      intro a _;
      show ¬(if (⊤ : ℕ∞) = (⊤ : ℕ∞) then o₀ a else M.toModel.Val M.root.1 a);
      rw [ite_eq_left rfl];
      exact not_false;
    have hiff : M.root.1 ⊩[M.toModel] C.modalize ↔ M.Val M.root.1 a :=
      calc
        M.root.1 ⊩[M.toModel] C.modalize
          ↔ toTail.chainPoint ⊤ ⊩[(M.toModel.toTail M.root.1).toModel] (C.modalize) := hstep1
        _ ↔ toPseudoTail.chainPoint ⊤
              ⊩[(M.toModel.toPseudoTail M.root.1 (M.toModel.Val M.root.1)).toModel]
              (C.modalize) := hstep2
        _ ↔ toPseudoTail.chainPoint ⊤ ⊩[(M.toModel.toPseudoTail M.root.1 o₀).toModel]
              (C.modalize) := forces_root_modalized_o_indep hC'mod
        _ ↔ toPseudoTail.chainPoint ⊤ ⊩[(M.toModel.toPseudoTail M.root.1 o₀).toModel] C :=
              forces_modalize h0
        _ ↔ M.Val M.root.1 a := interpolant_root_forces_iff hab hac hCant hCsuc hCatoms M o₀;
    exact Model.World.forces_iff.mpr hiff;
  exact not_exists_modalized_equiv_atom ⟨C.modalize, a, hC'mod, hC'atoms, hS⟩;

end LogicD

end
