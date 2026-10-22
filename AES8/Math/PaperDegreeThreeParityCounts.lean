import AESConcrete.ActivityGramDominance

/-! The paper's odd/even mask partition and its symbolic row multiplicities.
Only four-bit subset combinatorics is evaluated. Matrix bounds belong to callers.
Constructive proof work only; no attacks or canonical/vendor/manuscript edits. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeParityCounts
open AESMixing AESMixing.AES
set_option autoImplicit false
set_option maxRecDepth 100000

def IsOdd (A : Fin 16) : Prop := maskSize A = 1 ∨ maskSize A = 3
def IsEven (A : Fin 16) : Prop := maskSize A = 2
abbrev Odd := {A : Fin 16 // IsOdd A}
abbrev Even := {A : Fin 16 // IsEven A}

instance (A : Fin 16) : Decidable (IsOdd A) := inferInstanceAs (Decidable (_ ∨ _))
instance (A : Fin 16) : Decidable (IsEven A) := inferInstanceAs (Decidable (_ = _))

def bitCount (n : ℕ) : ℕ :=
  (if n%2 = 1 then 1 else 0) + (if n/2%2 = 1 then 1 else 0) +
    (if n/4%2 = 1 then 1 else 0) + (if n/8%2 = 1 then 1 else 0)
def commonCount (n m : ℕ) : ℕ :=
  (if n%2 = 1 ∧ m%2 = 1 then 1 else 0) +
    (if n/2%2 = 1 ∧ m/2%2 = 1 then 1 else 0) +
    (if n/4%2 = 1 ∧ m/4%2 = 1 then 1 else 0) +
    (if n/8%2 = 1 ∧ m/8%2 = 1 then 1 else 0)

theorem mask_size_numeric : ∀ A : Fin 16, maskSize A = bitCount A.val := by decide
theorem intersection_numeric : ∀ A B : Fin 16,
    maskSize (maskIntersection A B) = commonCount A.val B.val := by decide

theorem sum_fin_sixteen (f : Fin 16 → ℝ) :
    (∑ B : Fin 16, f B) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 +
        (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + 0))))))))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

theorem sum_subtype (P : Fin 16 → Prop) [DecidablePred P] (f : Fin 16 → ℝ) :
    (∑ B : {B // P B}, f B.val) = ∑ B : Fin 16, if P B then f B else 0 := by
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

def oddRow (F : ℕ → ℕ → ℕ → ℝ) (w : ℕ) : ℝ :=
  if w = 1 then F 1 1 1 + 3*F 1 1 0 + 3*F 1 3 1 + F 1 3 0
  else if w = 2 then 2*F 2 1 1 + 2*F 2 1 0 + 2*F 2 3 2 + 2*F 2 3 1
  else if w = 3 then F 3 3 3 + 3*F 3 3 2 + 3*F 3 1 1 + F 3 1 0
  else 0

def evenRow (F : ℕ → ℕ → ℕ → ℝ) (w : ℕ) : ℝ :=
  if w = 1 then 3*F 1 2 1 + 3*F 1 2 0
  else if w = 2 then F 2 2 2 + 4*F 2 2 1 + F 2 2 0
  else if w = 3 then 3*F 3 2 2 + 3*F 3 2 1
  else 0

theorem odd_row_classification (F : ℕ → ℕ → ℕ → ℝ) (A : Fin 16)
    (hA : IsOdd A ∨ IsEven A) :
    (∑ B : Odd, F (maskSize A) (maskSize B.val)
      (maskSize (maskIntersection A B.val))) = oddRow F (maskSize A) := by
  rw [sum_subtype IsOdd (fun B => F (maskSize A) (maskSize B)
    (maskSize (maskIntersection A B))), sum_fin_sixteen]
  simp_rw [intersection_numeric, mask_size_numeric]
  simp only [IsOdd, IsEven, mask_size_numeric] at hA
  fin_cases A <;> norm_num [oddRow, IsOdd, mask_size_numeric, bitCount, commonCount,
    Fin.ext_iff] at * <;> ring

theorem even_row_classification (F : ℕ → ℕ → ℕ → ℝ) (A : Fin 16)
    (hA : IsOdd A ∨ IsEven A) :
    (∑ B : Even, F (maskSize A) (maskSize B.val)
      (maskSize (maskIntersection A B.val))) = evenRow F (maskSize A) := by
  rw [sum_subtype IsEven (fun B => F (maskSize A) (maskSize B)
    (maskSize (maskIntersection A B))), sum_fin_sixteen]
  simp_rw [intersection_numeric, mask_size_numeric]
  simp only [IsOdd, IsEven, mask_size_numeric] at hA
  fin_cases A <;> norm_num [evenRow, IsEven, mask_size_numeric, bitCount, commonCount,
    Fin.ext_iff] at * <;> ring

theorem odd_interior (A : Odd) : A.val ≠ 0 ∧ A.val ≠ 15 := by
  constructor <;> intro h <;> have ha := A.property <;> rw [h] at ha
  all_goals norm_num [IsOdd, mask_size_numeric, bitCount] at ha

theorem even_interior (A : Even) : A.val ≠ 0 ∧ A.val ≠ 15 := by
  constructor <;> intro h <;> have ha := A.property <;> rw [h] at ha
  all_goals norm_num [IsEven, mask_size_numeric, bitCount] at ha

end AES8.PaperDegreeThreeParityCounts
