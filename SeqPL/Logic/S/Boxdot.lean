module

public import SeqPL.Logic.S.Basic
public import SeqPL.Kripke.RootExtension

@[expose]
public section

universe u
variable {α : Type u} {A : Formula α}

namespace LogicS

open Model.World

/--
  **boxdot 変換された論理式について GL と S は一致する**（tail model による意味論的証明）：
  `GL ⊢ Aᵇ` ↔ `S ⊢ Aᵇ`．
  Foundation の `iff_provable_boxdot_GL_provable_boxdot_S` の算術的完全性を経由しない証明．
-/
theorem iff_provable_boxdot_GL_provable_boxdot_S [DecidableEq α] :
    (Aᵇ) ∈ LogicGL ↔ (Aᵇ) ∈ LogicS := by
  constructor;
  . exact provable_of_provable_GL;
  . intro h;
    replace h := iff_provable_S_provable_GL.mp h;
    apply LogicGL.iff_forces_root.mpr;
    intro κ _ M _;
    let Γ := (Aᵇ).subfmls.prebox;
    let n : ℕ+ := ⟨Γ.card + 1, by omega⟩;
    obtain ⟨i, hi⟩ := RootedModel.extendRoot.exists_tail_forces_forall_axiomT
      (M := M) (n := n) (Γ := Γ) (by simp [n]);
    apply RootedModel.extendRoot.tail_forces_boxdotTranslate_iff (n := n) (i := i) |>.mp;
    apply LogicGL.iff_forces.mp h ((M.extendRoot n).toModel) (.inr i);
    apply forces_fconj.mpr;
    rintro B hB;
    obtain ⟨C, hC, rfl⟩ : ∃ C ∈ Γ, (□C 🡒 C) = B := by
      simpa [Formula.subfmlsS] using hB;
    exact hi C hC;

end LogicS

end
