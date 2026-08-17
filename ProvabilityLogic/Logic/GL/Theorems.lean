module

public import ProvabilityLogic.Logic.GL.Basic
meta import ProvabilityLogic.Logic.GL.Basic

@[expose]
public section

namespace LogicGL

variable {α : Type*} {A B C D : Formula α}

open ProvableHilbert Model.World

theorem imp_trans : ((A 🡒 B) 🡒 (B 🡒 C) 🡒 A 🡒 C) ∈ LogicGL := by
  classical
  apply Kripke.completeness;
  grind;

theorem contra (h : (A 🡒 B) ∈ LogicGL) : (∼B 🡒 ∼A) ∈ LogicGL :=
  mdp (elimContra (A := ∼A) (B := ∼B))
    (impTrans dne (impTrans h dni))

theorem dia4 : (◇◇A 🡒 ◇A) ∈ LogicGL :=
  contra (impTrans modal4 (boxImp dni))

theorem imp_of_not_and_not [DecidableEq α] : (∼(A ⋏ ∼B) 🡒 (A 🡒 B)) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem conj_comm [DecidableEq α] : ((A ⋏ B) 🡒 (B ⋏ A)) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem and_congr_right (h : (B 🡒 C) ∈ LogicGL) : ((A ⋏ B) 🡒 (A ⋏ C)) ∈ LogicGL :=
  ctxAndIntroRule andL (impTrans andR h)

theorem distrib_and_or [DecidableEq α] : ((A ⋏ (B ⋎ C)) 🡒 ((A ⋏ B) ⋎ (A ⋏ C))) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem bridge_impL_imp [DecidableEq α] :
  (((C 🡒 (A ⋎ D)) ⋏ ((B ⋏ C) 🡒 D)) 🡒 (((A 🡒 B) ⋏ C) 🡒 D)) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem bridge_impR_imp [DecidableEq α] :
  (((A ⋏ C) 🡒 (B ⋎ D)) 🡒 (C 🡒 ((A 🡒 B) ⋎ D))) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem or_imp_left (h : (A 🡒 B) ∈ LogicGL) : ((A ⋎ C) 🡒 (B ⋎ C)) ∈ LogicGL :=
  orElim' (impTrans h orL) orR

theorem dia_bot [DecidableEq α] : (◇(⊥ : Formula α) 🡒 ⊥) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem diaImp (h : (A 🡒 B) ∈ LogicGL) : (◇A 🡒 ◇B) ∈ LogicGL :=
  contra (boxImp (contra h))

theorem dia_neg_imp_not_box : (◇(∼A) 🡒 ∼□A) ∈ LogicGL := contra (boxImp dni)

theorem not_box_imp_dia_neg : (∼□A 🡒 ◇(∼A)) ∈ LogicGL := contra (boxImp dne)

theorem dia_of_not_box_imp_not_box : (◇(∼□A) 🡒 ∼□A) ∈ LogicGL :=
  impTrans (diaImp not_box_imp_dia_neg) (impTrans dia4 dia_neg_imp_not_box)

theorem imp_dia_and [DecidableEq α] : ((□A ⋏ ◇B) 🡒 ◇(A ⋏ B)) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem dia_cases [DecidableEq α] : (◇A 🡒 (◇(A ⋏ B) ⋎ ◇(A ⋏ ∼B))) ∈ LogicGL := by
  apply Kripke.completeness;
  grind;

theorem dia_boxRefuter [DecidableEq α] : (∼□A 🡒 ◇(□A ⋏ ∼A)) ∈ LogicGL :=
  contra (impTrans (boxImp (imp_of_not_and_not (A := □A) (B := A))) modalL)

theorem weakPoint3_dichotomy [DecidableEq α] :
  (((□((⊡(∼A)) 🡒 ∼B)) ⋎ (□((⊡(∼B)) 🡒 ∼A))) 🡒
    ((◇A ⋏ ◇B) 🡒 ((◇(A ⋏ B) ⋎ ◇(A ⋏ ◇B)) ⋎ ◇(B ⋏ ◇A)))) ∈ LogicGL := by
  apply Kripke.completeness;
  intro κ _ M _ x h hAB;
  have hAB' := forces_and.mp hAB;
  obtain ⟨y, hxy, hyA⟩ := forces_dia.mp hAB'.1;
  obtain ⟨z, hxz, hzB⟩ := forces_dia.mp hAB'.2;
  rcases forces_or.mp h with h1 | h2;
  · have hz := forces_box.mp h1 z hxz;
    by_cases hzA : z ⊩[_] A;
    · exact forces_or.mpr (Or.inl (forces_or.mpr (Or.inl
        (forces_dia.mpr ⟨z, hxz, forces_and.mpr ⟨hzA, hzB⟩⟩))));
    · have hnbd : ¬ z ⊩[_] (⊡(∼A)) := by
        intro hc;
        rcases forces_imp.mp hz with hc' | hb;
        · exact hc' hc;
        · exact absurd hzB (forces_neg.mp hb);
      obtain ⟨w, hzw, hwA⟩ : ∃ w, z ≺ w ∧ w ⊩[_] A := by
        by_contra hcon;
        push Not at hcon;
        exact hnbd (forces_boxdot.mpr
          ⟨forces_neg.mpr hzA, fun w hzw => forces_neg.mpr (hcon w hzw)⟩);
      exact forces_or.mpr (Or.inr (forces_dia.mpr
        ⟨z, hxz, forces_and.mpr ⟨hzB, forces_dia.mpr ⟨w, hzw, hwA⟩⟩⟩));
  · have hy := forces_box.mp h2 y hxy;
    by_cases hyB : y ⊩[_] B;
    · exact forces_or.mpr (Or.inl (forces_or.mpr (Or.inl
        (forces_dia.mpr ⟨y, hxy, forces_and.mpr ⟨hyA, hyB⟩⟩))));
    · have hnbd : ¬ y ⊩[_] (⊡(∼B)) := by
        intro hc;
        rcases forces_imp.mp hy with hc' | hb;
        · exact hc' hc;
        · exact absurd hyA (forces_neg.mp hb);
      obtain ⟨w, hyw, hwB⟩ : ∃ w, y ≺ w ∧ w ⊩[_] B := by
        by_contra hcon;
        push Not at hcon;
        exact hnbd (forces_boxdot.mpr
          ⟨forces_neg.mpr hyB, fun w hyw => forces_neg.mpr (hcon w hyw)⟩);
      exact forces_or.mpr (Or.inl (forces_or.mpr (Or.inr
        (forces_dia.mpr ⟨y, hxy, forces_and.mpr ⟨hyA, forces_dia.mpr ⟨w, hyw, hwB⟩⟩⟩))));

section

variable {Γ Δ : FormulaFinset α}

theorem imp_fconj_box_box [DecidableEq α] : (⋀Γ.box 🡒 ⋀Γ.box.box) ∈ LogicGL := by
  apply imp_fconj_of_forall;
  intro C hC;
  obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hC;
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB';
  exact impTrans (imp_fconj_of_mem (Finset.mem_image_of_mem _ hB)) modal4;

theorem imp_box_conj_box [DecidableEq α] : (⋀Γ.box 🡒 □⋀Γ.box) ∈ LogicGL :=
  impTrans imp_fconj_box_box imp_conj_box

theorem imp_box_union [DecidableEq α] : (⋀Γ.box 🡒 □(⋀(Γ.box ∪ Γ))) ∈ LogicGL :=
  impTrans (impTrans (ctxAndIntroRule imp_box_conj_box imp_conj_box) imp_box_and)
    (boxImp (imp_fconj_union Γ.box Γ))

theorem imp_not_fdisj_of_forall (h : ∀ A ∈ Δ, (B 🡒 ∼A) ∈ LogicGL) : (B 🡒 ∼(⋁ Δ)) ∈ LogicGL :=
  impTrans dni (contra (imp_fdisj_elim (fun A hA => impTrans dni (contra (h A hA)))))

theorem imp_not_fdisj_fconj_not [DecidableEq α] :
  (∼(⋁ Δ) 🡒 ⋀ (Δ.image (fun A => ∼A))) ∈ LogicGL := by
  apply imp_fconj_of_forall;
  intro C hC;
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hC;
  exact contra (imp_mem_fdisj hA);

end

/-! ### Examples from the meta-mathematical applications of `GL`

- [MPB23, §6.3]
-/

example : ∼□□⊥ 🡒 (∼□(∼□⊥) ⋏ ∼□(∼∼□⊥)) ∈ @LogicGL ℕ := by native_decide

example : (□((#0) 🡘 ∼□#0) ⋏ ∼□□⊥) 🡒 (∼□#0 ⋏ ∼□(∼#0)) ∈ @LogicGL ℕ := by native_decide

example : □((□(#0) 🡒 #0) 🡒 ◇◇⊤) 🡒 ◇◇⊤ 🡒 □#0 🡒 #0 ∈ @LogicGL ℕ := by native_decide

example : ∼□⊥ 🡒 ∼□◇⊤ ∈ @LogicGL ℕ := by native_decide

end LogicGL

end
