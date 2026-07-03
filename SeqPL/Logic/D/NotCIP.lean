module

public import SeqPL.Logic.D.Basic
public import SeqPL.Logic.GL.Fixedpoint
public import SeqPL.Logic.S.Basic

@[expose]
public section

/-!
# Dzhaparidze's logic `D` does not possess Craig's interpolation property

Formalization of Beklemishev 1989, "Provability Logic Without Craig's Interpolation
Property", Section 8.

The counterexample uses the two formulas
* `A = □(□b ⋎ a) 🡒 □b`
* `B = □(a 🡒 □c) 🡒 □c`

and shows that `∼A 🡒 B` is provable in `D` (Lemma 9) while no interpolant exists.
-/

universe u
variable {α : Type u}

namespace Formula

/-!
### Modalization

Write `C = f(□C₁, …, □Cₙ, p₁, …, pₘ)`, where `f` uses only `→`, `⊥`, the `□Cᵢ` are the
maximal boxed subformulas and the `pⱼ` are the remaining (non-modalized, top-level)
atoms.  The *modalization* `C.modalize = f(□C₁, …, □Cₙ, ⊥, …, ⊥)` replaces every
non-modalized atom by `⊥`; the result is a `Modalized` formula (every atom lies inside a
`□`).  These utilities underpin Beklemishev 1989, Section 8, Lemmas 11 and 12.
-/

variable {A : Formula α}

/-- Replace every non-modalized (top-level, unboxed) atom of `A` by `⊥`, keeping the
maximal boxed subformulas.  Turns `f(□C₁, …, □Cₙ, p₁, …, pₘ)` into
`f(□C₁, …, □Cₙ, ⊥, …, ⊥)` (Beklemishev 1989, Section 8, Lemma 11). -/
@[grind]
def modalize : Formula α → Formula α
  | #_    => ⊥
  | ⊥     => ⊥
  | A 🡒 B => A.modalize 🡒 B.modalize
  | □A    => □A

/-- `A` is modalized: every atom of `A` occurs within the scope of a `□`. -/
abbrev Modalized (A : Formula α) : Prop := ∀ a, A.ModalizedIn a

/-- The modalization of any formula is `Modalized`. -/
@[simp, grind .]
lemma modalized_modalize : A.modalize.Modalized := by
  intro a; induction A <;> grind;

/-- Modalization only removes atoms. -/
@[simp, grind .]
lemma atoms_modalize_subset [DecidableEq α] : A.modalize.atoms ⊆ A.atoms := by
  induction A <;> grind;

end Formula

namespace LogicD

variable [DecidableEq α]

/-- The formula `A = □(□b ⋎ a) 🡒 □b` of the counterexample. -/
abbrev counterexampleCIP_A (a b : Formula α) : Formula α := □(□b ⋎ a) 🡒 □b

/-- The formula `B = □(a 🡒 □c) 🡒 □c` of the counterexample. -/
abbrev counterexampleCIP_B (a c : Formula α) : Formula α := □(a 🡒 □c) 🡒 □c

section

variable {a b c : Formula α}

/-- Beklemishev 1989, Section 8, Lemma 9: `D ⊢ ∼A 🡒 B`, where
`A = □(□b ⋎ a) 🡒 □b` and `B = □(a 🡒 □c) 🡒 □c`. -/
lemma provable_counterexample_imp :
    (∼(counterexampleCIP_A a b) 🡒 counterexampleCIP_B a c) ∈ LogicD := by
  -- K-distribution over the two boxed premises, proved semantically in GL.
  have step2 : ((□(□b ⋎ a) ⋏ □(a 🡒 □c)) 🡒 □(□b ⋎ □c)) ∈ LogicGL := by
    apply LogicGL.provable_of_valid;
    intro κ _ M _ x;
    grind;
  -- Chain the distribution with the instance of axiom D (`A := b`, `B := c`).
  have step4 : ((□(□b ⋎ a) ⋏ □(a 🡒 □c)) 🡒 (□b ⋎ □c)) ∈ LogicD :=
    provable_imp_trans (provable_of_provable_GL step2) provable_axiomD;
  -- Propositional reshaping into `∼A 🡒 B`, a GL tautology.
  have taut :
      (((□(□b ⋎ a) ⋏ □(a 🡒 □c)) 🡒 (□b ⋎ □c)) 🡒
        (∼(counterexampleCIP_A a b) 🡒 counterexampleCIP_B a c)) ∈ LogicGL := by
    apply LogicGL.provable_of_valid;
    intro κ _ M _ x;
    grind;
  exact provable_of_provable_GL_imp taut step4;

end

open Model
open Model.World (Forces)

section

/-!
### Lemma 10

Beklemishev 1989, Section 8, Lemma 10.

The paper works with abstract D-models `𝒳 = (K, ≺, ⊩)` having a distinguished lower
element, limit element and tail element.  In SeqPL a D-model is realized concretely as
the pseudo-tail `M.toPseudoTail r o` of a *rooted* finite GL model `M` with base point
`r = M.root`:

* the root `chainPoint ⊤` (`ω`) is the lower element, whose valuation is the free function
  `o` (the "value at the lower point"); truth in the D-model, `𝒳 ⊩ C`, is forcing at this
  root;
* the tail scale is the descending chain `chainPoint n` together with the tree `M`, all
  carrying the reference valuation `M.Val r`; the truth of an atom at the limit element
  of the tail scale is therefore its reference value `M.Val r`.

Taking `r` to be the *root* of `M` (rather than an arbitrary point) matters: the chain
worlds `chainPoint n` share their valuation with the world `r`, so the counter-valuation
used in the proof (which flips the atoms `b`/`c` on the chain) also flips it at `embed r`.
When `r` is the root, no world of `M` accesses `r`, so this does not disturb `□b`/`□c` at
the other worlds.  This is faithful: the paper's D-scales likewise have a least element,
and the tail models used in Theorem 2 are rooted.

So Lemma 10, "for any D-model, the interpolant `C` is true at the lower element iff the
shared atom `a` is true at the limit element", becomes: for every rooted finite GL model
`M` and lower valuation `o`, `C` is forced at the pseudo-tail root iff `M.Val M.root a`.
In particular the root-forcing of `C` is independent of `o` — the content fed into
Lemma 11.
-/

variable {κ : Type u} [Nonempty κ] {M₁ M₂ : Model κ α} {a b c : α} {C : Formula α}

open Model.World

/-- Forcing depends only on the frame and on the valuation at the atoms of the formula
(a refinement of `Model.forces_congr`). -/
lemma forces_congr_atoms
    (hR : M₁.Rel' = M₂.Rel') {A : Formula α} {x : κ}
    (hV : ∀ x a, a ∈ A.atoms → (M₁.Val' x a ↔ M₂.Val' x a)) :
    Forces (M := M₁) x A ↔ Forces (M := M₂) x A := by
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
/-- In a rooted model with a transitive irreflexive relation, no world accesses the root. -/
lemma not_rel_root_of_rooted (M : RootedModel κ α)
    [M.IsFiniteGL] (x : κ) : ¬M.toModel.Rel x M.root.1 := by
  intro h;
  by_cases hx : x = M.root.1;
  . subst hx; exact Std.Irrefl.irrefl _ h;
  . exact Std.Irrefl.irrefl _ (IsTrans.trans _ _ _ (M.root.2 x hx) h);

/-- The rooted model `M` with the valuation of the atom `d` overwritten so that `d` holds
exactly off the root (the frame is unchanged). -/
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

/-- Off the flipped atom, the pseudo-tails of `M` and `flipModel M d` carry the same
valuation at every world. -/
lemma val_toPseudoTail_flipModel {M : RootedModel κ α}
    {o : α → Prop} (had : a ≠ d) (x : M.World ⊕ ℕ∞) :
    (M.toModel.toPseudoTail M.root.1 o).Val' x a ↔ ((flipModel M d).toPseudoTail M.root.1 o).Val' x a := by
  grind;

/-- Beklemishev 1989, Section 8, Lemma 10: if `C` is an interpolant for `∼A 🡒 B` in
`D` (so `D ⊢ ∼A 🡒 C`, `D ⊢ C 🡒 B`, and `C` contains only the atom `a`), then in every
pseudo-tail D-model `M.toPseudoTail M.root o` of a rooted finite GL model `M`, `C` is
forced at the root (`ω`, the lower element) iff the atom `a` holds on the tail scale
(`M.Val M.root a`, its value at the limit element). -/
lemma interpolant_root_forces_iff
    (hab : a ≠ b) (hac : a ≠ c)
    (hCant : (∼(counterexampleCIP_A (#a) (#b)) 🡒 C) ∈ LogicD)
    (hCsuc : (C 🡒 counterexampleCIP_B (#a) (#c)) ∈ LogicD)
    (hCatoms : C.atoms ⊆ {a})
    (M : RootedModel κ α) [M.IsFiniteGL] (o : α → Prop) :
    Forces (M := (M.toModel.toPseudoTail M.root.1 o).toModel)
      (M.toModel.toPseudoTail M.root.1 o).root.1 C ↔ M.Val M.root.1 a := by
  have hCp : ∀ e ∈ C.atoms, e = a := fun e ha => Finset.mem_singleton.mp (hCatoms ha);
  constructor;
  . -- If the root forces `C`, then `a` holds on the tail scale; by contradiction.
    intro hC;
    by_contra hp;
    -- Flip `c` to hold exactly off the root and apply soundness to `D ⊢ C 🡒 B`.
    have hB := forces_pseudoTail_root_of_provable hCsuc (flipModel M c) M.root.1 o;
    -- `C` does not contain `c`, so its root-forcing transfers to the flipped model.
    have hC' : Forces (M := ((flipModel M c).toPseudoTail M.root.1 o).toModel) (toPseudoTail.chainPoint ⊤) C :=
      (forces_congr_atoms
        (M₁ := (M.toModel.toPseudoTail M.root.1 o).toModel)
        (M₂ := ((flipModel M c).toPseudoTail M.root.1 o).toModel) rfl
        (fun x e ha => by rw [hCp e ha]; exact val_toPseudoTail_flipModel hac x)).mp hC;
    have hBf := hB hC';
    -- The root forces `□(a 🡒 □c)` in the flipped pseudo-tail.
    have hant : Forces (M := ((flipModel M c).toPseudoTail M.root.1 o).toModel)
        (toPseudoTail.chainPoint ⊤) (□((#a) 🡒 □(#c))) := by
      rintro (x | m) hy;
      . -- Worlds of `M`: all their successors avoid the root, where `c` holds.
        intro _;
        rintro (z | j) hz;
        . show (if c = c then z ≠ M.root.1 else M.toModel.Val' z c);
          rw [if_pos rfl];
          rintro rfl;
          exact not_rel_root_of_rooted M x hz;
        . exact False.elim hz;
      . -- Chain worlds: `a` fails there since `M.Val M.root.1 a` fails.
        intro hpm;
        exfalso;
        apply hp;
        have : (
          if m = (⊤ : ℕ∞) then o a
          else if a = c then M.root.1 ≠ M.root.1
          else M.toModel.Val' M.root.1 a
        ) := hpm;
        grind;
    -- But `□c` fails at the root: `c` is false at the chain world `chainPoint 0`.
    have hc0 : ¬Forces (M := ((flipModel M c).toPseudoTail M.root.1 o).toModel)
        (toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞)) (#c) := by
      show ¬(if ((0 : ℕ) : ℕ∞) = (⊤ : ℕ∞) then o c else
        if c = c then M.root.1 ≠ M.root.1 else M.toModel.Val' M.root.1 c);
      rw [if_neg (ENat.coe_lt_top 0).ne, if_pos rfl];
      simp;
    exact hc0 (hBf hant (toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞)) (ENat.coe_lt_top 0));
  . -- If `a` holds on the tail scale, the root forces `C`; by contradiction.
    intro hp;
    by_contra hC;
    -- Flip `b` to hold exactly off the root and apply soundness to `D ⊢ ∼A 🡒 C`.
    have hA := forces_pseudoTail_root_of_provable hCant (flipModel M b) M.root.1 o;
    -- The root of the flipped pseudo-tail forces `∼A`.
    have hnA : Forces (M := ((flipModel M b).toPseudoTail M.root.1 o).toModel)
        (toPseudoTail.chainPoint ⊤) (∼(counterexampleCIP_A (#a) (#b))) := by
      intro hAf;
      -- The root forces `□(□b ⋎ a)`.
      have hante : Forces (M := ((flipModel M b).toPseudoTail M.root.1 o).toModel)
          (toPseudoTail.chainPoint ⊤) (□(□(#b) ⋎ (#a))) := by
        rintro (x | m) hy;
        . -- Worlds of `M`: all their successors avoid the root, so `□b` holds.
          apply forces_or.mpr;
          left;
          rintro (z | j) hz;
          . show (if b = b then z ≠ M.root.1 else M.toModel.Val' z b);
            rw [if_pos rfl];
            rintro rfl;
            exact not_rel_root_of_rooted M x hz;
          . grind;
        . -- Chain worlds: `a` holds there since `M.Val M.root.1 a` holds.
          apply forces_or.mpr;
          right;
          show (
            if m = (⊤ : ℕ∞) then o a
            else if a = b then M.root.1 ≠ M.root.1
            else M.toModel.Val' M.root.1 a
          );
          grind;
      -- But `□b` fails at the root: `b` is false at the chain world `chainPoint 0`.
      have hb0 : ¬Forces (M := ((flipModel M b).toPseudoTail M.root.1 o).toModel)
          (toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞)) (#b) := by
        show ¬(if ((0 : ℕ) : ℕ∞) = (⊤ : ℕ∞) then o b else
          if b = b then M.root.1 ≠ M.root.1 else M.toModel.Val' M.root.1 b);
        rw [if_neg (ENat.coe_lt_top 0).ne, if_pos rfl];
        simp;
      exact hb0 (hAf hante (toPseudoTail.chainPoint ((0 : ℕ) : ℕ∞)) (ENat.coe_lt_top 0));
    -- Transfer the root-forcing of `C` back from the flipped pseudo-tail.
    apply hC;
    exact (forces_congr_atoms
      (M₁ := (M.toModel.toPseudoTail M.root.1 o).toModel)
      (M₂ := ((flipModel M b).toPseudoTail M.root.1 o).toModel) rfl
      (fun x e ha => by rw [hCp e ha]; exact val_toPseudoTail_flipModel hab x)).mpr (hA hnA);

end

section

/-!
### Modalization (utilities for Lemmas 11 and 12)

The syntactic modalization `Formula.modalize` and predicate `Formula.Modalized`
(defined above) underpin Beklemishev 1989, Section 8, Lemmas 11 and 12.  The lemmas
below relate them to forcing in pseudo-tail D-models.
-/

variable {A : Formula α}

variable {κ : Type u} [Nonempty κ] {C : Formula α} {M : Model κ α}
    {r : M.World} {o o' : α → Prop}

/-- If every atom of `A` is false at the world `x`, then modalization does not change the
forcing of `A` at `x` (the replaced atoms were false, i.e. equivalent to `⊥`). -/
lemma forces_modalize {x : κ}
  (h : ∀ a ∈ A.atoms, ¬M.Val x a) :
  Forces (M := M) x A.modalize ↔ Forces (M := M) x A := by
  induction A <;> grind;

omit [DecidableEq α] in
/-- The two pseudo-tails `M.toPseudoTail r o` and `M.toPseudoTail r o'` differ only in the
valuation at the root `chainPoint ⊤`; forcing at any other world is unaffected by `o`. -/
lemma forces_pseudoTail_ne_root_o_indep (A : Formula α) :
    ∀ z : (M.toPseudoTail r o).World, z ≠ toPseudoTail.chainPoint ⊤ →
      (Forces (M := (M.toPseudoTail r o).toModel) z A ↔
        Forces (M := (M.toPseudoTail r o').toModel) z A) := by
  -- No successor is the root `chainPoint ⊤` (used in the `box` case).
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
valuation `o`: its atoms occur only under boxes, and all successors of the root lie
outside the root, where the two pseudo-tails agree. -/
lemma forces_root_modalized_o_indep {A : Formula α} (hA : A.Modalized) :
    Forces (M := (M.toPseudoTail r o).toModel) (toPseudoTail.chainPoint ⊤) A ↔
      Forces (M := (M.toPseudoTail r o').toModel) (toPseudoTail.chainPoint ⊤) A := by
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

/-- Beklemishev 1989, Section 8, Lemma 11: if the root-forcing of `C` in the pseudo-tail
D-models is independent of the lower valuation `o`, then there is a modalized formula `C'`
(concretely `C.modalize`) with `D ⊢ C 🡘 C'` and `C'.atoms ⊆ C.atoms`. -/
lemma exists_modalized_equiv_of_indep
    (hindep : ∀ {κ : Type u} [Nonempty κ] (M : Model κ α) [M.IsFiniteGL]
        (r : M.World) (o o' : α → Prop),
      Forces (M := (M.toPseudoTail r o).toModel) (M.toPseudoTail r o).root.1 C ↔
        Forces (M := (M.toPseudoTail r o').toModel) (M.toPseudoTail r o').root.1 C) :
    ∃ C', C'.Modalized ∧ (C 🡘 C') ∈ LogicD ∧ C'.atoms ⊆ C.atoms := by
  use C.modalize, Formula.modalized_modalize, ?_, Formula.atoms_modalize_subset;
  -- By the semantic characterization of `D`, it suffices to force `C 🡘 C.modalize` at the
  -- root of every pseudo-tail D-model.
  apply (LogicD.provability_TFAE.out 1 0).mp;
  intro κ _ M _ r o;
  -- The all-false lower valuation, at which `C` and `C.modalize` agree at the root.
  let o₀ : α → Prop := fun _ => False;
  -- Every atom of `C` is false at the root of the `o₀`-pseudo-tail.
  have h0 : ∀ a ∈ C.atoms, ¬(M.toPseudoTail r o₀).toModel.Val (toPseudoTail.chainPoint ⊤) a := by
    intro a _;
    show ¬(if (⊤ : ℕ∞) = (⊤ : ℕ∞) then o₀ a else M.Val r a);
    rw [if_pos rfl];
    exact not_false;
  -- Chain: `𝒳_o ⊩ C ↔ 𝒳_{o₀} ⊩ C ↔ 𝒳_{o₀} ⊩ C.modalize ↔ 𝒳_o ⊩ C.modalize`.
  have key : Forces (M := (M.toPseudoTail r o).toModel) (toPseudoTail.chainPoint ⊤) C ↔
      Forces (M := (M.toPseudoTail r o).toModel) (toPseudoTail.chainPoint ⊤) (C.modalize) :=
    (hindep M r o o₀).trans ((forces_modalize h0).symm.trans
      (forces_root_modalized_o_indep Formula.modalized_modalize));
  exact Model.World.forces_iff.mpr key;

/-- Beklemishev 1989, Section 8, Lemma 12: there is no modalized single-variable formula
`C(a)` with `S ⊢ C(a) 🡘 a`.  If there were, the de Jongh–Sambin fixed point of `∼C(a)`
(via `LogicGL.fixpointTheorem`) would give `E` with `GL ⊢ ∼C(E) 🡘 E`; substituting `a ↦ E`
into `S ⊢ C(a) 🡘 a` yields `S ⊢ C(E) 🡘 E`, whence `S ⊢ E 🡘 ∼E`, contradicting the
consistency of `S` (`LogicS.consistent`). -/
lemma not_exists_modalized_equiv_atom [Nontrivial α] :
    ¬ ∃ (C : Formula α) (a : α), C.Modalized ∧ C.atoms ⊆ {a} ∧ (C 🡘 #a) ∈ LogicS := by
  rintro ⟨C, a, hMod, hAtoms, hCp⟩;
  -- A fresh atom `d ≠ a` for the fixed point theorem.
  obtain ⟨d, hqp⟩ := exists_ne a;
  -- `a` is modalized in `∼C = C 🡒 ⊥` since `C` is fully modalized.
  have hA : (∼C).ModalizedIn a := ⟨hMod a, trivial⟩;
  -- `d` is fresh for `∼C`.
  have hq : d ∉ (∼C).atoms := by
    intro hmem;
    have : d ∈ C.atoms := by simpa [Formula.atoms] using hmem;
    exact hqp (Finset.mem_singleton.mp (hAtoms this));
  -- The de Jongh–Sambin fixed point `E` of `∼C`: `GL ⊢ ∼C(E) 🡘 E`.
  obtain ⟨E, -, hfp⟩ := LogicGL.fixpointTheorem (Ne.symm hqp) hA hq;
  have hSnCE : ((∼(C⟦a ↦ E⟧)) 🡘 E) ∈ LogicS :=
    LogicS.provable_of_provable_GL (by simpa using hfp);
  -- Substituting `a ↦ E` into `S ⊢ C 🡘 a` gives `S ⊢ C(E) 🡘 E`.
  have hSCE : ((C⟦a ↦ E⟧) 🡘 E) ∈ LogicS := by
    have h := Logic.sumQuasiNormal.subst (s := Formula.Substitution.single a E) hCp;
    simp only [Formula.subst_iff, Formula.subst_atom,
      Formula.Substitution.single_self] at h;
    exact h;
  -- `X 🡘 E` and `∼X 🡘 E` are jointly inconsistent, propositionally.
  have taut : (((C⟦a ↦ E⟧) 🡘 E) 🡒 (((∼(C⟦a ↦ E⟧)) 🡘 E) 🡒 ⊥)) ∈ @LogicGL α := by
    apply LogicGL.provable_of_valid;
    intro κ _ M _ x;
    grind;
  -- Hence `S ⊢ ⊥`, contradicting consistency.
  exact LogicS.consistent
    (Logic.sumQuasiNormal.mdp
      (Logic.sumQuasiNormal.mdp (LogicS.provable_of_provable_GL taut) hSCE) hSnCE);

end

/-- Beklemishev 1989, Section 8, Theorem 2: Dzhaparidze's logic `D` does not have Craig's
interpolation property.  The implication `∼A 🡒 B` with `A = □(□b ⋎ a) 🡒 □b` and
`B = □(a 🡒 □c) 🡒 □c` is provable in `D` (Lemma 9), but no interpolant `C` in the sole
common atom `a` exists: by Lemma 10 the root-forcing of `C` in the pseudo-tail D-models is
independent of the lower valuation, so the modalization `C' = C.modalize` satisfies
`S ⊢ C' 🡘 a` (via the tail lemma and the GL-characterization of `S`), contradicting
Lemma 12. -/
theorem notCIP {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ A B : Formula α, (A 🡒 B) ∈ LogicD ∧
      ¬ ∃ C : Formula α, (A 🡒 C) ∈ LogicD ∧ (C 🡒 B) ∈ LogicD ∧
        C.atoms ⊆ A.atoms ∩ B.atoms := by
  haveI : Nontrivial α := ⟨⟨a, b, hab⟩⟩;
  use ∼(counterexampleCIP_A (#a) (#b)), counterexampleCIP_B (#a) (#c), provable_counterexample_imp;
  rintro ⟨C, hCant, hCsuc, hCatoms⟩;
  -- The only common atom of `∼A` and `B` is `a`.
  have hAB : (∼(counterexampleCIP_A (#a) (#b))).atoms ∩
      (counterexampleCIP_B (#a) (#c)).atoms = {a} := by
    ext e;
    simp only [Formula.atoms, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton];
    grind;
  rw [hAB] at hCatoms;
  -- The modalization `C'` of the interpolant is modalized and still only contains `a`.
  have hC'mod : C.modalize.Modalized := Formula.modalized_modalize;
  have hC'atoms : C.modalize.atoms ⊆ {a} := Formula.atoms_modalize_subset.trans hCatoms;
  -- `S ⊢ C' 🡘 a`, via the GL-characterization of `S` (item 3 of `provability_TFAE`).
  have hS : (C.modalize 🡘 #a) ∈ @LogicS α := by
    apply (LogicS.provability_TFAE.out 2 0).mp;
    intro κ _ M _ hant;
    -- Each `□E 🡒 E` with `□E` a subformula of `C' 🡘 a` holds at the root.
    have hΓ : ∀ E ∈ (C.modalize 🡘 #a).subfmls.prebox,
        M.root.1 ⊩ (□E 🡒 E) := by
      intro E hE;
      exact Model.World.forces_fconj.mp hant _ (by
        simp only [Formula.subfmlsS, Finset.mem_image];
        exact ⟨E, hE, rfl⟩);
    have hC'mem : C.modalize ∈ (C.modalize 🡘 #a).subfmls := by grind;
    -- Step 1: root-forcing of `C'` transfers to the root of the tail model.
    have hstep1 : M.root.1 ⊩ C.modalize ↔
        Forces (M := (M.toModel.toTail M.root.1).toModel) (toTail.chainPoint ⊤)
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
    -- Step 2: the tail model is the pseudo-tail whose lower valuation is that of the root.
    have hstep2 : Forces (M := (M.toModel.toTail M.root.1).toModel)
        (toTail.chainPoint ⊤) (C.modalize) ↔
        Forces (M := (M.toModel.toPseudoTail M.root.1 (M.toModel.Val M.root.1)).toModel)
          (toPseudoTail.chainPoint ⊤) (C.modalize) :=
      Model.forces_congr
        (M₁ := (M.toModel.toTail M.root.1).toModel)
        (M₂ := (M.toModel.toPseudoTail M.root.1 (M.toModel.Val M.root.1)).toModel)
        rfl
        (fun x e => by
          rcases x with x | i;
          · exact Iff.rfl;
          · show M.toModel.Val M.root.1 e ↔
              (if i = (⊤ : ℕ∞) then M.toModel.Val M.root.1 e else M.toModel.Val M.root.1 e);
            rw [ite_self]);
    -- The all-false lower valuation.
    let o₀ : α → Prop := fun _ => False;
    -- Every atom of `C` is false at the root of the `o₀`-pseudo-tail.
    have h0 : ∀ a ∈ C.atoms,
        ¬(M.toModel.toPseudoTail M.root.1 o₀).toModel.Val (toPseudoTail.chainPoint ⊤) a := by
      intro a _;
      show ¬(if (⊤ : ℕ∞) = (⊤ : ℕ∞) then o₀ a else M.toModel.Val M.root.1 a);
      rw [if_pos rfl];
      exact not_false;
    -- Chain of equivalences (steps 3 and 4 are `o`-independence and de-modalization),
    -- ending in Lemma 10.
    have hiff : M.root.1 ⊩ C.modalize ↔ M.Val M.root.1 a :=
      hstep1.trans (hstep2.trans
        ((forces_root_modalized_o_indep hC'mod).trans
          ((forces_modalize h0).trans
            (interpolant_root_forces_iff hab hac hCant hCsuc hCatoms M o₀))));
    exact Model.World.forces_iff.mpr hiff;
  exact not_exists_modalized_equiv_atom ⟨C.modalize, a, hC'mod, hC'atoms, hS⟩;

end LogicD

end
