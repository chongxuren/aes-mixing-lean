import AESMixing.WeightedRectangularSchur
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fin.VecNotation

/-! Exact rational positive-vector certificates for the three byte-level
residual comparison matrices. The formula is explicit; no external table
is trusted. The analytic support-to-degree aggregation remains separate. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def incidenceSupportRaw (i j a b : ℕ) : ℚ :=
  ∑ d ∈ Finset.range (i+j), if 0 < d ∧ 4+d ≤ a+b then
    ((a+b-i-j).choose (a+b-(4+d)) : ℚ) * 16^(2*d-(min i d+min j d)) else 0

def incidenceSupportWeight (i a : ℕ) : ℚ :=
  ((Nat.choose 4 i * Nat.choose (4-i) (a-i) : ℕ) : ℚ) / 255^(a-i)

def incidenceWitness11 : Fin 4 → ℚ := ![1000001,193956027,3474236482,13922390079]
def incidenceWitness12Out : Fin 4 → ℚ := ![1000001,56237559,1006076152,6475669233]
def incidenceWitness12In : Fin 3 → ℚ := ![2661172,73220780,785565986]
def incidenceWitness22 : Fin 3 → ℚ := ![1001,16912,281554]

theorem incidence_comparison_11_rows (a : Fin 4) :
    (∑ b : Fin 4, incidenceSupportRaw 1 1 (a.val+1) (b.val+1) *
      incidenceSupportWeight 1 (b.val+1) * incidenceWitness11 b) <
      (27/8000 : ℚ)*incidenceWitness11 a := by
  fin_cases a <;> norm_num [incidenceSupportRaw, incidenceSupportWeight, incidenceWitness11,
    Fin.sum_univ_succ, Finset.sum_range_succ, Nat.choose]

theorem incidence_comparison_12_rows (a : Fin 4) :
    (∑ b : Fin 3, incidenceSupportRaw 1 2 (a.val+1) (b.val+2) *
      incidenceSupportWeight 2 (b.val+2) * incidenceWitness12In b) <
      (43/500 : ℚ)*incidenceWitness12Out a := by
  fin_cases a <;> norm_num [incidenceSupportRaw, incidenceSupportWeight, incidenceWitness12Out,
    incidenceWitness12In, Fin.sum_univ_succ, Finset.sum_range_succ, Nat.choose]

theorem incidence_comparison_12_columns (b : Fin 3) :
    (∑ a : Fin 4, incidenceSupportRaw 1 2 (a.val+1) (b.val+2) *
      incidenceSupportWeight 1 (a.val+1) * incidenceWitness12Out a) <
      (43/500 : ℚ)*incidenceWitness12In b := by
  fin_cases b <;> norm_num [incidenceSupportRaw, incidenceSupportWeight, incidenceWitness12Out,
    incidenceWitness12In, Fin.sum_univ_succ, Finset.sum_range_succ, Nat.choose]

theorem incidence_comparison_22_rows (a : Fin 3) :
    (∑ b : Fin 3, incidenceSupportRaw 2 2 (a.val+2) (b.val+2) *
      incidenceSupportWeight 2 (b.val+2) * incidenceWitness22 b) <
      (9/10 : ℚ)*incidenceWitness22 a := by
  fin_cases a <;> norm_num [incidenceSupportRaw, incidenceSupportWeight, incidenceWitness22,
    Fin.sum_univ_succ, Finset.sum_range_succ, Nat.choose]

theorem incidence_witnesses_positive :
    (∀ a, 0 < incidenceWitness11 a) ∧ (∀ a, 0 < incidenceWitness12Out a) ∧
      (∀ a, 0 < incidenceWitness12In a) ∧ (∀ a, 0 < incidenceWitness22 a) := by
  norm_num [incidenceWitness11, incidenceWitness12Out, incidenceWitness12In,
    incidenceWitness22, Fin.forall_fin_succ]

end AESMixing
