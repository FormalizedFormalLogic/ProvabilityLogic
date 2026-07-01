module

public import SeqPL.Kripke.Basic

@[expose]
public section

variable [Nonempty κ₁] [Nonempty κ₂] [Nonempty κ₃] {α}

namespace Model

section Bisimulation

structure Bisimulation (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) where
  toRel : M₁.World → M₂.World → Prop
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : α} : toRel x₁ x₂ → (M₁.Val x₁ a ↔ M₂.Val x₂ a)
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

infix:80 " ⇄ " => Bisimulation

variable {M₁ : Model κ₁ α} {M₂ : Model κ₂ α}

instance : CoeFun (M₁ ⇄ M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨Bisimulation.toRel⟩

def Bisimulation.symm (bi : M₁ ⇄ M₂) : M₂ ⇄ M₁ where
  toRel x y := bi.toRel y x
  atomic h := (bi.atomic h).symm
  forth := by
    intro x₂ y₂ x₁ hxy h;
    obtain ⟨y₁, hy₁, hxy⟩ := bi.back hxy h;
    exact ⟨y₁, hy₁, hxy⟩;
  back := by
    intro x₂ x₁ y₁ hxy h;
    obtain ⟨y₂, hy₂, hxy⟩ := bi.forth hxy h;
    exact ⟨y₂, hy₂, hxy⟩;

end Bisimulation


section ModalEquivalent

def World.ModalEquivalent {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} (x₁ : M₁.World) (x₂ : M₂.World) : Prop :=
  ∀ {A : Formula α}, x₁ ⊩ A ↔ x₂ ⊩ A
infix:50 " ↭ " => World.ModalEquivalent

variable {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} {x₁ : M₁.World} {x₂ : M₂.World}

lemma World.modal_equivalent_of_bisimilar (Bi : M₁ ⇄ M₂) (bisx : Bi x₁ x₂) : x₁ ↭ x₂ := by
  intro A;
  induction A generalizing x₁ x₂ with
  | atom a => exact Bi.atomic bisx;
  | bot => simp [World.Forces];
  | imp A B ihA ihB =>
    constructor;
    . intro hAB hA;
      exact ihB bisx |>.mp $ hAB $ ihA bisx |>.mpr hA;
    . intro hAB hA;
      exact ihB bisx |>.mpr $ hAB $ ihA bisx |>.mp hA;
  | box A ih =>
    constructor;
    . intro h y₂ Rx₂y₂;
      obtain ⟨y₁, bisy, Rx₁y₁⟩ := Bi.back bisx Rx₂y₂;
      exact ih bisy |>.mp $ h _ Rx₁y₁;
    . intro h y₁ Rx₁y₁;
      obtain ⟨y₂, bisy, Rx₂y₂⟩ := Bi.forth bisx Rx₁y₁;
      exact ih bisy |>.mpr $ h _ Rx₂y₂;

def World.ModalEquivalent.symm (h : x₁ ↭ x₂) : x₂ ↭ x₁ := fun {_} => Iff.symm h

end ModalEquivalent


section PseudoEpimorphism

structure PseudoEpimorphism (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) where
  toFun : M₁.World → M₂.World
  forth {x y : M₁.World} : x ≺ y → toFun x ≺ toFun y
  back {w : M₁.World} {v : M₂.World} : toFun w ≺ v → ∃ u, toFun u = v ∧ w ≺ u
  atomic {w : M₁.World} {a : α} : M₁.Val w a ↔ M₂.Val (toFun w) a

infix:80 " →ₚ " => PseudoEpimorphism

variable [Nonempty κ] {M : Model κ α} {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} {M₃ : Model κ₃ α}

instance : CoeFun (M₁ →ₚ M₂) (λ _ => M₁.World → M₂.World) := ⟨PseudoEpimorphism.toFun⟩

namespace PseudoEpimorphism

protected def id : M →ₚ M where
  toFun := _root_.id
  forth := by simp;
  back := by simp;
  atomic := by simp;

def comp (f : M₁ →ₚ M₂) (g : M₂ →ₚ M₃) : M₁ →ₚ M₃ where
  toFun := g ∘ f
  forth hxy := g.forth $ f.forth hxy
  back := by
    intro x w hxw;
    obtain ⟨y, rfl, hxy⟩ := g.back hxw;
    obtain ⟨u, rfl, hfu⟩ := f.back hxy;
    exact ⟨u, rfl, hfu⟩;
  atomic := f.atomic.trans g.atomic

variable (f : M₁ →ₚ M₂)

lemma forth_iterate {x y : M₁.World} {n : ℕ} : x ≺^[n] y → f x ≺^[n] f y := by
  induction n generalizing x with
  | zero => rintro rfl; rfl;
  | succ n ih =>
    rintro ⟨z, Rxz, Rzy⟩;
    exact ⟨f z, f.forth Rxz, ih Rzy⟩;

lemma back_iterate {w : M₁.World} {v : M₂.World} {n : ℕ} : f w ≺^[n] v → ∃ u, f u = v ∧ w ≺^[n] u := by
  induction n generalizing w with
  | zero => rintro rfl; exact ⟨w, rfl, rfl⟩;
  | succ n ih =>
    rintro ⟨z, Rfwz, Rzv⟩;
    obtain ⟨u, rfl, Rwu⟩ := f.back Rfwz;
    obtain ⟨t, rfl, Rut⟩ := ih Rzv;
    exact ⟨t, rfl, u, Rwu, Rut⟩;

lemma toFun_rel_toFun_iff_of_inj (inj : Function.Injective f.toFun) {x y : M₁.World} :
    f x ≺ f y ↔ x ≺ y := by
  constructor;
  . intro h;
    obtain ⟨z, he, hz⟩ := f.back h;
    exact inj he ▸ hz;
  . exact f.forth;

lemma toFun_relItr_toFun_iff_of_inj (inj : Function.Injective f.toFun) {x y : M₁.World} {n : ℕ} :
    f x ≺^[n] f y ↔ x ≺^[n] y := by
  constructor;
  . intro h;
    obtain ⟨z, he, hz⟩ := f.back_iterate h;
    exact inj he ▸ hz;
  . exact f.forth_iterate;

def bisimulation : M₁ ⇄ M₂ where
  toRel x y := y = f x
  atomic := by rintro x₁ x₂ a rfl; exact f.atomic;
  forth := by
    rintro x₁ y₁ x₂ rfl Rxy;
    exact ⟨f y₁, rfl, f.forth Rxy⟩;
  back := by
    rintro x₁ x₂ y₂ rfl Rxy;
    obtain ⟨u, rfl, Rwu⟩ := f.back Rxy;
    exact ⟨u, rfl, Rwu⟩;

lemma modal_equivalence (w : M₁.World) : w ↭ f w :=
  World.modal_equivalent_of_bisimilar f.bisimulation rfl

end PseudoEpimorphism

lemma validate_of_surjective_pseudoEpimorphism {A : Formula α}
    (f : M₁ →ₚ M₂) (f_surjective : Function.Surjective f.toFun) : M₁ ⊧ A → M₂ ⊧ A := by
  intro h u;
  obtain ⟨x, rfl⟩ := f_surjective u;
  exact f.modal_equivalence x |>.mp $ h x;

end PseudoEpimorphism


section Generation

structure GeneratedSub (M₁ : Model κ₁ α) (M₂ : Model κ₂ α) extends M₁ →ₚ M₂ where
  monic : Function.Injective toFun

infix:80 " ⥹ " => GeneratedSub

namespace GeneratedSub

variable {M₁ : Model κ₁ α} {M₂ : Model κ₂ α} (g : M₁ ⥹ M₂)

def bisimulation : M₁ ⇄ M₂ := g.toPseudoEpimorphism.bisimulation

lemma modal_equivalence (w : M₁.World) : w ↭ g.toFun w :=
  g.toPseudoEpimorphism.modal_equivalence w

end GeneratedSub

end Generation

end Model

end
