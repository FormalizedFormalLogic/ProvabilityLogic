module

public import SeqPL.Formula.Basic
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Nat.Pairing

@[expose]
public section

namespace Formula

variable {α : Type*} [Encodable α]

/-- `Formula α` を `ℕ` へ単射符号化する． -/
def toNat : Formula α → ℕ
  | atom a => Nat.pair 0 (Encodable.encode a)
  | ⊥      => Nat.pair 1 0
  | A 🡒 B  => Nat.pair 2 (Nat.pair A.toNat B.toNat)
  | □A     => Nat.pair 3 A.toNat

lemma toNat_injective : Function.Injective (toNat : Formula α → ℕ) := by
  suffices H : ∀ A B : Formula α, toNat A = toNat B → A = B by intro a b; exact H a b;
  intro A;
  induction A with
  | atom a => intro B h; cases B <;> simp_all [toNat, Nat.pair_eq_pair, Encodable.encode_inj];
  | bot => intro B h; cases B <;> simp_all [toNat, Nat.pair_eq_pair];
  | imp A₁ A₂ ih1 ih2 =>
    intro B h; cases B;
    case imp B₁ B₂ =>
      simp only [toNat, Nat.pair_eq_pair] at h;
      obtain ⟨-, h1, h2⟩ := h;
      rw [ih1 _ h1, ih2 _ h2];
    all_goals simp [toNat, Nat.pair_eq_pair] at h;
  | box A₁ ih =>
    intro B h; cases B;
    case box B₁ =>
      simp only [toNat, Nat.pair_eq_pair] at h;
      rw [ih _ h.2];
    all_goals simp [toNat, Nat.pair_eq_pair] at h;

instance : Countable (Formula α) := toNat_injective.countable

end Formula

end
