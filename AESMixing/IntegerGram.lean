import AESMixing.ConstraintCount

/-! The activity Gram calculation can be done with signed integers over the
single denominator 255^4. This avoids repeated rational normalization in
the finite certificate check. The equality to the real projection formula
is proved separately from every supplied rank table. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def atomNumerator (b : Bool) (m : Fin 5) : ℤ :=
  if b then ![-1,1,1,-256,255] m else ![1,-1,-1,256,0] m

theorem atomCoefficient_numerator (b : Bool) (m : Fin 5) :
    atomCoefficient 256 b m = (atomNumerator b m : ℝ)/255 := by
  cases b <;> fin_cases m <;> norm_num [atomCoefficient,atomNumerator]

def degreeAtomNumerator (j : Fin 5) (m : Fin 4 → Fin 5) : ℤ :=
  ∑ p : Fin 4 → Bool, if degreeIndex p = j then ∏ i, atomNumerator (p i) (m i) else 0

def rankGramNumerator (rank : (Fin 4 → Fin 5) → ℕ) (j : Fin 5) : ℤ :=
  ∑ m : Fin 4 → Fin 5, degreeAtomNumerator j m * 256^(8-rank m)

theorem atomCoefficient_product_numerator (p : Fin 4 → Bool) (m : Fin 4 → Fin 5) :
    (∏ i, atomCoefficient 256 (p i) (m i)) =
      ((∏ i, atomNumerator (p i) (m i) : ℤ) : ℝ)/255^4 := by
  simp_rw [atomCoefficient_numerator]
  rw [Finset.prod_div_distrib]
  norm_num

theorem rankGramNumerator_formula (rank : (Fin 4 → Fin 5) → ℕ) (j : Fin 5) :
    (∑ p : Fin 4 → Bool, if degreeIndex p = j then
      ∑ m : Fin 4 → Fin 5, (∏ i, atomCoefficient 256 (p i) (m i)) *
        (256 : ℝ)^(8-rank m) else 0) = (rankGramNumerator rank j : ℝ)/255^4 := by
  simp_rw [atomCoefficient_product_numerator]
  unfold rankGramNumerator degreeAtomNumerator
  push_cast
  rw [Finset.sum_div]
  simp_rw [Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : degreeIndex p = j
  · simp only [hp, if_true]
    apply Finset.sum_congr rfl
    intro m _
    ring
  · simp [hp]

theorem byte_activity_degree_gram_from_ranks (j : Fin 5) (a b : Fin 16)
    (rank : (Fin 4 → Fin 5) → ℕ)
    (hcount : ∀ m, Nat.card {x : (MaskCoordinates a → BinaryWord 8) ×
        (MaskCoordinates b → BinaryWord 8) // ∀ i,
      atomCondition (m i) (AES.columnMatrix AES.mixEntry (extendCoordinates a x.1) i)
        (AES.columnMatrix AES.mixEntry (extendCoordinates b x.2) i)} = 256^(8-rank m)) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn byteDiffusionEquiv a) y *
      degreeComponent 0 j (diffusedActivityColumn byteDiffusionEquiv b) y) =
        (rankGramNumerator rank j : ℝ)/255^4 := by
  rw [byte_activity_degree_gram]
  simp only [← Nat.card_eq_fintype_card]
  simp_rw [hcount, Nat.cast_pow, Nat.cast_ofNat]
  exact rankGramNumerator_formula rank j

end AESMixing
