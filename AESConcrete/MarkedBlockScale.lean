import AESConcrete.MarkedBlockShortening

/-!
# Exact activity-choice counts and marked-code normalization scale

Physical residual marks, uniform activity choices and zero activity choices
partition the eight graph positions. The resulting scale is derived from
the actual shortened-source cardinality, without an energy premise or an
enumeration of byte values. Constructive mathematics only; no attacks or
edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MarkedBlockScale
open AESMixing AESMixing.AES
open AESConcrete.MarkedBlockVectorization AESConcrete.MarkedBlockShortening

attribute [local instance] Classical.propDecidable

section Counts
variable {I : Type*} [Fintype I] [DecidableEq I]

def indexPartitionEquiv (m : I → Bool) : I ≃ Marked m ⊕ Activity m where
  toFun i := if h : m i = true then Sum.inl ⟨i,h⟩ else Sum.inr ⟨i,h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv i := by
    by_cases h : m i = true <;> simp [h]
  right_inv i := by
    cases i with
    | inl i => simp [i.property]
    | inr i => simp [i.property]

theorem partition_card (m : I → Bool) :
    Fintype.card (Marked m) + Fintype.card (Activity m) = Fintype.card I := by
  simpa only [Fintype.card_sum] using (Fintype.card_congr (indexPartitionEquiv m)).symm

def falseIndexEquiv (s : I → Bool) : Activity s ≃ {i : I // s i = false} :=
  Equiv.subtypeEquivRight (fun i => by cases s i <;> simp)

theorem uniform_false_count (s : I → Bool) :
    uniformCount s + Fintype.card {i : I // s i = false} = Fintype.card I := by
  have h := partition_card s
  rw [Fintype.card_congr (falseIndexEquiv s)] at h
  exact h

end Counts

def zeroActivityEquiv (m : GraphPosition → Bool) (s : Activity m → Bool) :
    {i : Activity m // s i = false} ≃ {p : GraphPosition // p ∈ zeroPositions m s} where
  toFun i := ⟨i.val.val, (mem_zeroPositions m s i.val.val).mpr ⟨i.val.property,i.property⟩⟩
  invFun p := ⟨⟨p.val, ((mem_zeroPositions m s p.val).mp p.property).choose⟩,
    ((mem_zeroPositions m s p.val).mp p.property).choose_spec⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

def zeroPositionEquiv (m : GraphPosition → Bool) (s : Activity m → Bool) :
    {p : GraphPosition // p ∈ zeroPositions m s} ≃
      MaskCoordinates (outputZeros m s) ⊕ MaskCoordinates (inputZeros m s) where
  toFun p := match p with
    | ⟨Sum.inl i,h⟩ => Sum.inl ⟨i,(outputPositionMask_bit (zeroPositions m s) i).mpr h⟩
    | ⟨Sum.inr i,h⟩ => Sum.inr ⟨i,(inputPositionMask_bit (zeroPositions m s) i).mpr h⟩
  invFun p := match p with
    | Sum.inl i => ⟨Sum.inl i.val,(outputPositionMask_bit (zeroPositions m s) i.val).mp i.property⟩
    | Sum.inr i => ⟨Sum.inr i.val,(inputPositionMask_bit (zeroPositions m s) i.val).mp i.property⟩
  left_inv p := by rcases p with ⟨p,h⟩; cases p <;> rfl
  right_inv p := by cases p <;> rfl

theorem zero_count (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Fintype.card {i : Activity m // s i = false} =
      maskSize (outputZeros m s) + maskSize (inputZeros m s) := by
  simpa only [Fintype.card_sum, maskCoordinates_card] using
    Fintype.card_congr ((zeroActivityEquiv m s).trans (zeroPositionEquiv m s))

/-- This counts all eight physical graph positions without case tables. -/
theorem count_balance (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Fintype.card (Marked m) + uniformCount s +
      (maskSize (outputZeros m s) + maskSize (inputZeros m s)) = 8 := by
  have hm : Fintype.card (Marked m) + Fintype.card (Activity m) = 8 := by
    simpa only [GraphPosition, Fintype.card_sum, Fintype.card_fin] using partition_card m
  have hs := uniform_false_count s
  rw [zero_count m s] at hs
  omega

theorem dimension_balance (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) ≤ 4) :
    (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))) + 4 =
      Fintype.card (Marked m) + uniformCount s := by
  have h := count_balance m s
  omega

section Scale
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Multiplying by q converts the exact source-normalization square to
256^ell whenever the shortening has at most four zero constraints. -/
theorem normalization_scale (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hz : maskSize (outputZeros m s) + maskSize (inputZeros m s) ≤ 4) :
    (256 : ℝ)^4 *
      (Real.sqrt (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s))) /
        (16 : ℝ)^uniformCount s)^2 = (256 : ℝ)^Fintype.card (Marked m) := by
  rw [normalization_square, source_card L hL, hV, Nat.cast_pow]
  simp only [Nat.cast_ofNat]
  rw [← mul_div_assoc]
  apply (div_eq_iff (pow_ne_zero _ (by norm_num : (256 : ℝ) ≠ 0))).mpr
  rw [← pow_add, ← pow_add]
  congr 1
  have h := dimension_balance m s hz
  omega

end Scale

end AESConcrete.MarkedBlockScale
