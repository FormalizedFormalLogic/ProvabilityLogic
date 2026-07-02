module

public import SeqPL.ProvabilityLogic.SolovaySentences
public import Foundation.FirstOrder.Bootstrapping.FixedPoint
public import Foundation.FirstOrder.Incompleteness.WitnessComparison
public import Foundation.FirstOrder.Incompleteness.Consistency

/-!
# Construction of Solovay sentences

Port of the construction in `Foundation.ProvabilityLogic.SolovaySentences`
(`LO.FirstOrder.Arithmetic.Bootstrapping.SolovaySentences`) to SeqPL's Kripke models.
-/

@[expose] public section

open Classical

noncomputable section

namespace LO.FirstOrder.Arithmetic.Bootstrapping

namespace SolovaySentences

open LO LO.Entailment
open Model Model.World

variable {κ : Type*} [Nonempty κ] {α : Type*}

variable {T : ArithmeticTheory} [T.Δ₁]

section model

variable (T) {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

def NegativeSuccessor (φ ψ : V) : Prop := T.ProvabilityComparisonLE (neg ℒₒᵣ φ) (neg ℒₒᵣ ψ)

lemma NegativeSuccessor.quote_iff_provabilityComparisonLE {φ ψ : Sentence ℒₒᵣ} :
    NegativeSuccessor (V := V) T ⌜φ⌝ ⌜ψ⌝ ↔ T.ProvabilityComparisonLE (V := V) ⌜∼φ⌝ ⌜∼ψ⌝ := by
  simp [NegativeSuccessor, Sentence.quote_def, Semiformula.quote_def]

section

def negativeSuccessor : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ nφ, ∃ nψ, !(negGraph ℒₒᵣ) nφ φ ∧ !(negGraph ℒₒᵣ) nψ ψ ∧ !T.provabilityComparisonLE nφ nψ”

instance negativeSuccessor_defined : 𝚺₁-Relation[V] NegativeSuccessor T via (negativeSuccessor T) := .mk fun v ↦ by
  simp [negativeSuccessor, NegativeSuccessor]

instance negativeSuccessor_definable : 𝚺₁-Relation (NegativeSuccessor T : V → V → Prop) := (negativeSuccessor_defined T).to_definable

/-- instance for definability tactic-/
instance negativeSuccessor_definable' : 𝚺-[0 + 1]-Relation (NegativeSuccessor T : V → V → Prop) := (negativeSuccessor_defined T).to_definable

end

end model

section stx

variable (T) (M : RootedModel κ α) [Fintype M.World] [M.IsGL]

abbrev WChain (i j : M.World) := {l : List M.World // l.ChainI (fun x y ↦ y ≺ x) j i}

instance (i j : M.World) : Finite (WChain M i j) :=
  List.ChainI.finite_of_irreflexive_of_transitive
    (by intro x; exact Std.Irrefl.irrefl (r := M.Rel) x)
    (by intro x y z hxy hyz
        exact IsTrans.trans (r := M.Rel) z y x hyz hxy)
    j i

def twoPointAux (t : M.World → FirstOrder.Semiterm ℒₒᵣ Empty N) (i j : M.World) : Semisentence ℒₒᵣ N :=
  ⩕ k ∈ { k : M.World | i ≺ k }, (negativeSuccessor T)/[t j, t k]

def θChainAux (t : M.World → FirstOrder.Semiterm ℒₒᵣ Empty N) : List M.World → Semisentence ℒₒᵣ N
  |          [] => ⊥
  |         [_] => ⊤
  | j :: i :: ε => (θChainAux t (i :: ε)) ⋏ (twoPointAux T M t i j)

omit [M.IsGL] in
lemma rew_twoPointAux (w : Fin N → FirstOrder.Semiterm ℒₒᵣ Empty N') (t : M.World → FirstOrder.Semiterm ℒₒᵣ Empty N) :
    Rew.subst w ▹ twoPointAux T M t i j = twoPointAux T M (fun i ↦ Rew.subst w (t i)) i j := by
  simp [twoPointAux, Finset.map_conj', Function.comp_def, ←TransitiveRewriting.comp_app,
    Rew.subst_comp_subst, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

omit [M.IsGL] in
lemma rew_θChainAux (w : Fin N → FirstOrder.Semiterm ℒₒᵣ Empty N') (t : M.World → FirstOrder.Semiterm ℒₒᵣ Empty N) (ε : List M.World) :
    Rew.subst w ▹ θChainAux T M t ε = θChainAux T M (fun i ↦ Rew.subst w (t i)) ε := by
  match ε with
  |          [] => simp [θChainAux]
  |         [_] => simp [θChainAux]
  | j :: i :: ε => simp [θChainAux, rew_θChainAux w _ (i :: ε), rew_twoPointAux]

def θAux (t : M.World → FirstOrder.Semiterm ℒₒᵣ Empty N) (i : M.World) : Semisentence ℒₒᵣ N :=
  haveI := Fintype.ofFinite (WChain M M.root.1 i);
  ⩖ ε : WChain M M.root.1 i, θChainAux T M t ε

lemma rew_θAux (w : Fin N → FirstOrder.Semiterm ℒₒᵣ Empty N') (t : M.World → FirstOrder.Semiterm ℒₒᵣ Empty N) (i : M.World) :
    Rew.subst w ▹ θAux T M t i = θAux T M (fun i ↦ Rew.subst w (t i)) i := by
  simp [Finset.map_udisj, θAux, rew_θChainAux]

def _root_.LO.FirstOrder.Theory.solovay (i : M.World) : Sentence ℒₒᵣ := exclusiveMultifixedpoint
  (fun j ↦
    let jj := (Fintype.equivFin M.World).symm j
    (θAux T M (fun i ↦ #(Fintype.equivFin M.World i)) jj) ⋏ (⩕ k ∈ { k : M.World | jj ≺ k }, T.consistentWith/[#(Fintype.equivFin M.World k)]))
  (Fintype.equivFin M.World i)

def twoPoint (i j : M.World) : Sentence ℒₒᵣ := twoPointAux T M (fun i ↦ ⌜T.solovay M i⌝) i j

def θChain (ε : List M.World) : Sentence ℒₒᵣ := θChainAux T M (fun i ↦ ⌜T.solovay M i⌝) ε

def θ (i : M.World) : Sentence ℒₒᵣ := θAux T M (fun i ↦ ⌜T.solovay M i⌝) i

lemma solovay_diag (i : M.World) :
    𝗜𝚺₁ ⊢ (T.solovay M i) 🡘 ((θ T M i) ⋏ (⩕ j ∈ { j : M.World | i ≺ j }, T.consistentWith/[⌜T.solovay M j⌝])) := by
  have : 𝗜𝚺₁ ⊢ (T.solovay M i) 🡘
      (Rew.subst fun j ↦ ⌜T.solovay M ((Fintype.equivFin M.World).symm j)⌝) ▹
        ((θAux T M (fun i ↦ #(Fintype.equivFin M.World i)) i) ⋏ (⩕ k ∈ { k : M.World | i ≺ k }, T.consistentWith/[#(Fintype.equivFin M.World k)])) := by
    simpa [Theory.solovay, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using!
      exclusiveMultidiagonal (T := 𝗜𝚺₁) (i := Fintype.equivFin M.World i)
        (fun j ↦
          let jj := (Fintype.equivFin M.World).symm j
          (θAux T M (fun i ↦ #(Fintype.equivFin M.World i)) jj) ⋏ (⩕ k ∈ { k : M.World | jj ≺ k }, T.consistentWith/[#(Fintype.equivFin M.World k)]))
  simpa [θ, Finset.map_conj', Function.comp_def, rew_θAux, ←TransitiveRewriting.comp_app,
    Rew.subst_comp_subst, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using! this

@[simp] lemma solovay_exclusive {i j : M.World} : T.solovay M i = T.solovay M j ↔ i = j := by
  simp [Theory.solovay]

omit [M.IsGL] in
private lemma θChainAux_sigma1 (ε : List M.World) : Hierarchy 𝚺 1 (θChainAux T M t ε) := by
  match ε with
  |          [] => simp [θChainAux]
  |         [_] => simp [θChainAux]
  | _ :: i :: ε =>
    simp [θChainAux, twoPointAux, θChainAux_sigma1 (i :: ε)]

@[simp] lemma θ_sigma1 (i : M.World) : Hierarchy 𝚺 1 (θ T M i) := by
  simp [θ, θAux, θChainAux_sigma1]

end stx

section model

variable (T) (M : RootedModel κ α) [Fintype M.World] [M.IsGL]

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]

@[simp] lemma val_twoPoint (i j : M.World) :
    V ⊧/![] (twoPoint T M i j) ↔ ∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝ := by
  simp [twoPoint, twoPointAux]

variable (V)

inductive ΘChain : List M.World → Prop where
  | singleton (i : M.World) : ΘChain [i]
  | cons {i j : M.World} :
    (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝) → ΘChain (i :: ε) → ΘChain (j :: i :: ε)

def Θ (i : M.World) : Prop := ∃ ε : List M.World, ε.ChainI (fun x y ↦ y ≺ x) i M.root.1 ∧ ΘChain T M V ε

def _root_.LO.FirstOrder.Theory.Solovay (i : M.World) := Θ T M V i ∧ ∀ j, i ≺ j → T.ConsistentWith (⌜T.solovay M j⌝ : V)

variable {T M V}

attribute [simp] ΘChain.singleton

@[simp] lemma ΘChain.not_nil : ¬ΘChain T M V ([] : List M.World) := by rintro ⟨⟩

lemma ΘChain.doubleton_iff {i j : M.World} :
    ΘChain T M V [j, i] ↔ (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝) := by
  constructor
  · rintro ⟨⟩; simp_all
  · rintro h; exact .cons h (by simp)

lemma ΘChain.cons_cons_iff {i j : M.World} {ε} :
    ΘChain T M V (j :: i :: ε) ↔
    ΘChain T M V (i :: ε) ∧ (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝) := by
  constructor
  · rintro ⟨⟩; simp_all
  · rintro ⟨ih, h⟩; exact .cons h ih

lemma ΘChain.cons_cons_iff' {i j : M.World} {ε} :
    ΘChain T M V (j :: i :: ε) ↔ ΘChain T M V [j, i] ∧ ΘChain T M V (i :: ε) := by
  constructor
  · rintro ⟨⟩; simpa [ΘChain.doubleton_iff, *]
  · rintro ⟨ih, h⟩; exact h.cons (by rcases ih; assumption)

lemma ΘChain.cons_of {m i j : M.World} {ε}
    (hc : List.ChainI (fun x y ↦ y ≺ x) i m ε)
    (hΘ : ΘChain T M V ε)
    (H : (∀ k, i ≺ k → NegativeSuccessor (V := V) T ⌜T.solovay M j⌝ ⌜T.solovay M k⌝))
    (hij : i ≺ j) :
    ΘChain T M V (j :: ε) := by
  rcases hc
  case singleton => exact .cons H hΘ
  case cons => exact .cons H hΘ

section

@[simp] lemma val_θChain (ε : List M.World) : V ⊧/![] (θChain T M ε) ↔ ΘChain T M V ε := by
  unfold θChain θChainAux
  match ε with
  |          [] => simp
  |         [i] => simp
  | j :: i :: ε =>
    suffices
      V ⊧/![] (θChain T M (i :: ε)) ∧ V ⊧/![] (twoPoint T M i j) ↔
      ΘChain T M V (j :: i :: ε) by simpa [-val_twoPoint] using! this
    simp [ΘChain.cons_cons_iff, val_θChain (i :: ε)]

@[simp] lemma val_θ {i : M.World} : V ⊧/![] (θ T M i) ↔ Θ T M V i := by
  suffices (∃ ε, List.ChainI (fun x y ↦ y ≺ x) i M.root.1 ε ∧ V ⊧/![] (θChain T M ε)) ↔ Θ T M V i by
    simpa [-val_θChain, θ, θAux]
  simp [Θ]

@[simp] lemma val_solovay {i : M.World} : V ⊧/![] (T.solovay M i) ↔ T.Solovay M V i := by
  simpa [models_iff] using!
    consequence_iff.mp (sound! (solovay_diag T M i)) V inferInstance

end

lemma ΘChain.append_iff {ε₁ ε₂ : List M.World} : ΘChain T M V (ε₁ ++ i :: ε₂) ↔ ΘChain T M V (ε₁ ++ [i]) ∧ ΘChain T M V (i :: ε₂) := by
  match ε₁ with
  |           [] => simp
  |          [x] => simp [ΘChain.cons_cons_iff' (ε := ε₂)]
  | x :: y :: ε₁ =>
    have : ΘChain T M V (y :: (ε₁ ++ i :: ε₂)) ↔ ΘChain T M V (y :: (ε₁ ++ [i])) ∧ ΘChain T M V (i :: ε₂) :=
      append_iff (ε₁ := y :: ε₁) (ε₂ := ε₂) (i := i)
    simp [cons_cons_iff' (ε := ε₁ ++ i :: ε₂), cons_cons_iff' (ε := ε₁ ++ [i]), and_assoc, this]

private lemma Solovay.exclusive.comparable {i₁ i₂ : M.World} {ε₁ ε₂ : List M.World}
    (ne : i₁ ≠ i₂)
    (h : ε₁ <:+ ε₂)
    (Hi₁ : ∀ j, i₁ ≺ j → T.ConsistentWith (⌜T.solovay M j⌝ : V))
    (cε₁ : List.ChainI (fun x y ↦ y ≺ x) i₁ r ε₁)
    (cε₂ : List.ChainI (fun x y ↦ y ≺ x) i₂ r ε₂)
    (Θε₂ : ΘChain T M V ε₂) : False := by
  have : ∃ a, a :: ε₁ <:+ ε₂ := by
    rcases List.IsSuffix.eq_or_cons_suffix h with (e | h)
    · have : ε₁ ≠ ε₂ := by
        rintro rfl
        have : i₁ = i₂ := (List.ChainI.eq_of cε₁ cε₂).1
        contradiction
      contradiction
    · exact h
  rcases this with ⟨j, hj⟩
  have hji₁ε₂ : [j, i₁] <:+: ε₂ := by
    rcases cε₁.tail_exists with ⟨ε₁', rfl⟩
    exact List.infix_iff_prefix_suffix.mpr ⟨j :: i₁ :: ε₁', by simp, hj⟩
  have hij₁ : i₁ ≺ j := cε₂.rel_of_infix j i₁ hji₁ε₂
  have : ¬T.Provable (⌜∼T.solovay M j⌝ : V) := by simpa [Theory.ConsistentWith.quote_iff] using! Hi₁ j hij₁
  have : T.Provable (⌜∼T.solovay M j⌝ : V) := by
    have : ΘChain T M V [j, i₁] := by
      rcases hji₁ε₂ with ⟨η₁, η₂, rfl⟩
      have Θε₂ : ΘChain T M V (η₁ ++ j :: i₁ :: η₂) := by simpa using! Θε₂
      exact ΘChain.cons_cons_iff'.mp (ΘChain.append_iff.mp Θε₂).2 |>.1
    have : ∀ k, i₁ ≺ k → T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M j⌝ ⌜∼T.solovay M k⌝ := by
      simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using! ΘChain.cons_cons_iff.mp this
    exact (ProvabilityComparison.iff_le_refl_provable (L := ℒₒᵣ)).mp (this j hij₁)
  contradiction

/-- Condition 1.-/
lemma Solovay.exclusive {i₁ i₂ : M.World} (ne : i₁ ≠ i₂) : T.Solovay M V i₁ → ¬T.Solovay M V i₂ := by
  intro S₁ S₂
  rcases S₁ with ⟨⟨ε₁, cε₁, Θε₁⟩, Hi₁⟩
  rcases S₂ with ⟨⟨ε₂, cε₂, Θε₂⟩, Hi₂⟩
  by_cases hε₁₂ : ε₁ <:+ ε₂
  · exact Solovay.exclusive.comparable ne hε₁₂ Hi₁ cε₁ cε₂ Θε₂
  by_cases hε₂₁ : ε₂ <:+ ε₁
  · exact Solovay.exclusive.comparable (Ne.symm ne) hε₂₁ Hi₂ cε₂ cε₁ Θε₁
  have : ∃ ε k j₁ j₂, j₁ ≠ j₂ ∧ j₁ :: k :: ε <:+ ε₁ ∧ j₂ :: k :: ε <:+ ε₂ := by
    rcases List.suffix_trichotomy hε₁₂ hε₂₁ with ⟨ε', j₁, j₂, nej, h₁, h₂⟩
    match ε' with
    |     [] =>
      rcases show j₁ = M.root.1 from List.single_suffix_uniq h₁ cε₁.prefix_suffix.2
      rcases show j₂ = M.root.1 from List.single_suffix_uniq h₂ cε₂.prefix_suffix.2
      contradiction
    | k :: ε =>
      exact ⟨ε, k, j₁, j₂, nej, h₁, h₂⟩
  rcases this with ⟨ε, k, j₁, j₂, nej, hj₁, hj₂⟩
  have C₁ : ΘChain T M V [j₁, k] := by
    rcases hj₁ with ⟨_, rfl⟩
    have : ΘChain T M V ([j₁] ++ k :: ε) := (ΘChain.append_iff.mp Θε₁).2
    simpa using! (ΘChain.append_iff.mp this).1
  have C₂ : ΘChain T M V [j₂, k] := by
    rcases hj₂ with ⟨_, rfl⟩
    have : ΘChain T M V ([j₂] ++ k :: ε) := (ΘChain.append_iff.mp Θε₂).2
    simpa using! (ΘChain.append_iff.mp this).1
  have P₁ : T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M j₁⌝ ⌜∼T.solovay M j₂⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using!
      ΘChain.doubleton_iff.mp C₁ j₂
        (cε₂.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨j₂ :: k :: ε, by simp, hj₂⟩)
  have P₂ : T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M j₂⌝ ⌜∼T.solovay M j₁⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using!
      ΘChain.doubleton_iff.mp C₂ j₁
        (cε₁.rel_of_infix _ _ <| List.infix_iff_prefix_suffix.mpr ⟨j₁ :: k :: ε, by simp, hj₁⟩)
  have : j₁ = j₂ := by simpa using! ProvabilityComparison.le_antisymm (V := V) P₁ P₂
  contradiction

/-- Condition 2.-/
lemma Solovay.consistent {i j : M.World} (hij : i ≺ j) : T.Solovay M V i → ¬T.Provable (⌜∼T.solovay M j⌝ : V) := fun h ↦
  (Theory.ConsistentWith.quote_iff T).mp (h.2 j hij)

lemma Solovay.refute (ne : M.root.1 ≠ i) : T.Solovay M V i → T.Provable (⌜∼T.solovay M i⌝ : V) := by
  intro h
  rcases show Θ T M V i from h.1 with ⟨ε, hε, cε⟩
  rcases List.ChainI.prec_exists_of_ne hε (Ne.symm ne) with ⟨ε', i', hii', rfl, hε'⟩
  have : ∀ k, i' ≺ k → NegativeSuccessor T ⌜T.solovay M i⌝ ⌜T.solovay M k⌝ := (ΘChain.cons_cons_iff.mp cε).2
  have : T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M i⌝ ⌜∼T.solovay M i⌝ := by
    simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE] using! this i hii'
  exact (ProvabilityComparison.iff_le_refl_provable (T := T)).mp this

lemma Θ.disjunction (i : M.World) : Θ T M V i → T.Solovay M V i ∨ ∃ j, i ≺ j ∧ T.Solovay M V j := by
  have : IsConverseWellFounded M.World M.Rel := inferInstance
  apply WellFounded.induction this.cwf i
  intro i ih hΘ
  by_cases hS : T.Solovay M V i
  · left; exact hS
  · right
    have : ∃ j, i ≺ j ∧ ∀ k, i ≺ k → T.ProvabilityComparisonLE (V := V) ⌜∼T.solovay M j⌝ ⌜∼T.solovay M k⌝ := by
      have : ∃ j, i ≺ j ∧ T.Provable (⌜∼T.solovay M j⌝ : V) := by
        have : Θ T M V i → ∃ x, i ≺ x ∧ T.Provable (⌜∼T.solovay M x⌝ : V) := by
          simpa [Theory.ConsistentWith.quote_iff, Theory.Solovay] using! hS
        exact this hΘ
      rcases this with ⟨j', hij', hj'⟩
      have := ProvabilityComparison.find_minimal_proof_fintype (T := T) (ι := {j : M.World // i ≺ j}) (i := ⟨j', hij'⟩)
        (fun k ↦ ⌜∼T.solovay M k.val⌝) (by simpa)
      simpa using! this
    rcases this with ⟨j, hij, hj⟩
    have : Θ T M V j := by
      rcases hΘ with ⟨ε, hε, cε⟩
      exact ⟨
        j :: ε,
        hε.cons hij,
        cε.cons_of hε (by simpa [NegativeSuccessor.quote_iff_provabilityComparisonLE]) hij⟩
    have : T.Solovay M V j ∨ ∃ k, j ≺ k ∧ T.Solovay M V k := ih j hij this
    rcases this with (hSj | ⟨k, hjk, hSk⟩)
    · exact ⟨j, hij, hSj⟩
    · exact ⟨k, IsTrans.trans _ _ _ hij hjk, hSk⟩

/-- Condition 4.-/
lemma disjunctive : ∃ i : M.World, T.Solovay M V i := by
  rcases Θ.disjunction (V := V) (T := T) M.root.1 ⟨[M.root.1], by simp⟩ with (H | ⟨i, _, H⟩);
  . use M.root.1;
  . use i;

/-- Condition 3.-/
lemma Solovay.box_disjunction [𝗜𝚺₁ ⪯ T] {i : M.World} (ne : M.root.1 ≠ i) :
    T.Solovay M V i → T.Provable (⌜⩖ j ∈ {j : M.World | i ≺ j}, T.solovay M j⌝ : V) := by
  intro hS
  have TP : T.internalize V ⊢ ⌜(θ T M i) 🡒 ((T.solovay M i) ⋎ (⩖ j ∈ {j : M.World | i ≺ j}, T.solovay M j))⌝ :=
    internal_provable_of_outer_provable <| by
      have : 𝗜𝚺₁ ⊢ (θ T M i) 🡒 ((T.solovay M i) ⋎ (⩖ j ∈ {j : M.World | i ≺ j}, T.solovay M j)) :=
        provable_of_models _ _ fun (V : Type) _ _ ↦ by
          simpa [models_iff] using! Θ.disjunction i
      exact Entailment.WeakerThan.pbl this
  have Tθ : T.internalize V ⊢ ⌜θ T M i⌝ :=
    Bootstrapping.Arithmetic.sigma_one_provable_of_models T (show Hierarchy 𝚺 1 (θ T M i) by simp) (by simpa [models_iff] using! hS.1)
  have hP : T.internalize V ⊢ (⌜T.solovay M i⌝ ⋎ ⌜⩖ j ∈ {j : M.World | i ≺ j}, T.solovay M j⌝ : Arithmetic.Bootstrapping.Formula V ℒₒᵣ) := (by simpa using! TP) ⨀ Tθ
  have : T.internalize V ⊢ (∼⌜T.solovay M i⌝ : Arithmetic.Bootstrapping.Formula V ℒₒᵣ) := by simpa using! (tprovable_tquote_iff_provable_quote (T := T)).mpr (Solovay.refute ne hS)
  have : T.internalize V ⊢ ⌜⩖ j ∈ {j : M.World | i ≺ j}, T.solovay M j⌝ := Entailment.of_a!_of_n! hP this
  exact (tprovable_tquote_iff_provable_quote (T := T)).mp this

end model

section

variable {T : ArithmeticTheory} [T.Δ₁] {M : RootedModel κ α} [Fintype M.World] [M.IsGL]

/--
  The Solovay sentence of the root is true in the standard model `ℕ`
  (port of `SolovaySentences.solovay_root_sound` in Foundation).
-/
lemma solovay_root_sound [𝗜𝚺₁ ⪯ T] [sound : T.SoundOn (Arithmetic.Hierarchy 𝚷 2)] :
    T.Solovay M ℕ M.root.1 := by
  have : 𝗜𝚺₁ ⪯ T := inferInstance
  haveI : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans inferInstance this
  have NS : ∀ i, M.root.1 ≠ i → ¬T.Solovay M ℕ i := by
    intro i hi H
    have Bi : T ⊢ ∼T.solovay M i := (provable_iff_provable (T := T)).mp (Solovay.refute hi H)
    have : ¬T.Solovay M ℕ i := by
      set π := θ T M i ⋏ ⩕ j ∈ { j : M.World | i ≺ j }, T.consistentWith/[⌜T.solovay M j⌝]
      have sπ : 𝗜𝚺₁ ⊢ T.solovay M i 🡘 π := solovay_diag T M i
      have : T ⊢ ∼π := by
        have : T ⊢ T.solovay M i 🡘 π := Entailment.WeakerThan.wk (inferInstanceAs (𝗜𝚺₁ ⪯ T)) sπ
        exact Entailment.K!_left (Entailment.ENN!_of_E! this) ⨀ Bi
      have : ¬ℕ ⊧/![] π := by
        simpa [models_iff] using!
          sound.sound
            (σ := ∼π)
            this
            (by simp [π,
              (show Hierarchy 𝚷 1 T.consistentWith.val by simp).strict_mono 𝚺 (show 1 < 2 by simp),
              (show Hierarchy 𝚺 1 (θ T M i) by simp).mono (show 1 ≤ 2 by simp)])
      have : T.Solovay M ℕ i ↔ ℕ ⊧/![] π := by
        simpa [models_iff] using! consequence_iff.mp (sound! sπ) ℕ inferInstance
      simpa [this]
    contradiction
  have : T.Solovay M ℕ M.root.1 ∨ ∃ j, M.root.1 ≺ j ∧ T.Solovay M ℕ j :=
    Θ.disjunction (V := ℕ) (T := T) M.root.1 ⟨[M.root.1], by simp⟩
  rcases this with (H | ⟨i, hri, Hi⟩)
  · assumption
  · have : ¬T.Solovay M ℕ i := NS i (by rintro rfl; exact Std.Irrefl.irrefl M.root.1 hri)
    contradiction

end

end SolovaySentences

end LO.FirstOrder.Arithmetic.Bootstrapping


section

open LO LO.Entailment
open LO.FirstOrder LO.FirstOrder.ProvabilityAbstraction
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping SolovaySentences
open Model Model.World

variable {κ : Type*} [Nonempty κ] {α : Type*} {A : _root_.Formula α}

noncomputable def LO.FirstOrder.Theory.standardProvability.solovaySentences
    (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    (M : RootedModel κ α) [Fintype M.World] [M.IsGL] :
    T.standardProvability.SolovaySentences M where
  σ := T.solovay M
  SC1 i j ne :=
    provable_of_models _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! Solovay.exclusive ne
  SC2 i j h :=
    provable_of_models _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! Solovay.consistent h
  SC3 i h :=
    provable_of_models _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff, standardProvability_def] using! Solovay.box_disjunction h
  SC4 :=
    provable_of_models _ _ fun (V : Type) _ _ ↦ by
      simpa [models_iff] using! disjunctive


theorem unprovable_realization_exists
  (T : FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
  (M : RootedModel κ α) [Fintype M.World] [M.IsGL]
  (hA : M.root.1 ⊮ A) (h : M.height < T.height)
  : ∃ f : StandardRealization α T, T ⊬ f A := by
  let S := LO.FirstOrder.Theory.standardProvability.solovaySentences (M := M.extendRoot 1) (T := T);
  use S.realization;
  contrapose! h;
  apply Order.le_of_lt_add_one;
  calc
    T.height < (M.extendRoot 1).height := S.theory_height (T.standardProvability.syntactical_sound ℕ) (A := A) ?_ h
    _        = _                       := by
      have := RootedModel.extendRoot.Ext1.eq_height_original_height_succ (M := M);
      simp_all only [ne_eq, PNat.val_ofNat, Nat.cast_add, Nat.cast_one];
  . apply Model.World.forces_dia.mpr;
    use M.root;
    constructor;
    . tauto;
    . exact RootedModel.extendRoot.same_forces_embed.not.mpr hA;

end

end

end
