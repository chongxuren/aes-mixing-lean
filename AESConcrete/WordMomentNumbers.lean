import AESConcrete.SharpDampedWordNorm

/-!
# Exact scalar tables for the word trace and second moment

These comparisons certify the source tables only. Actual Hilbert--Schmidt
block estimates and their orthogonal assembly are separate obligations.
All decimals in the source are represented by exact rationals here.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators Matrix
namespace AESConcrete.WordMomentNumbers
open AESMixing

set_option maxRecDepth 100000

def hs : Fin 5 → Fin 5 → ℝ :=
  ![![85/10,0,118/10,94/10,46/10],
    ![0,193/10,230/10,182/10,69/10],
    ![118/10,230/10,272/10,168/10,59/10],
    ![94/10,182/10,168/10,97/10,34/10],
    ![46/10,69/10,59/10,34/10,12/10]]

def op : Fin 5 → Fin 5 → ℝ :=
  ![![63/10,0,46/10,33/10,161/100],
    ![0,116/100,2,161/100,113/1000],
    ![46/10,2,145/100,113/1000,8/1000],
    ![33/10,161/100,113/1000,8/1000,56/100000],
    ![161/100,113/1000,8/1000,56/100000,4/100000]]

def gramCap : Fin 5 → Fin 5 → ℝ :=
  ![![1463/10,393/10,574/10,295/10,138/10],
    ![393/10,985/10,622/10,239/10,24/10],
    ![574/10,622/10,1417/10,786/10,219/10],
    ![295/10,239/10,786/10,623/10,174/10],
    ![138/10,24/10,219/10,174/10,83/10]]

def markedCap : ℕ → ℝ
  | 0 => 71
  | 1 => 0
  | 2 => 2311/100
  | 3 => 22
  | 4 => 205/10
  | 5 => 1176/100
  | 6 => 58/10
  | 7 => 284/100
  | 8 => 1412/1000
  | _ => 0

private theorem sum_fin_five (f : Fin 5 → ℝ) :
    (∑ i, f i) = f 0 + (f 1 + (f 2 + (f 3 + f 4))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem hs_nonneg (i j : Fin 5) : 0 ≤ hs i j := by
  fin_cases i <;> fin_cases j <;> norm_num [hs]

theorem op_nonneg (i j : Fin 5) : 0 ≤ op i j := by
  fin_cases i <;> fin_cases j <;> norm_num [op]

theorem gramCap_nonneg (i j : Fin 5) : 0 ≤ gramCap i j := by
  fin_cases i <;> fin_cases j <;> norm_num [gramCap]

theorem directComparison_le (i j : Fin 5) :
    SharpDampedWordNorm.directComparison i j ≤ op i j / 65536 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [op, SharpDampedWordNorm.directComparison, WordNorm.dampedCaps,
      SharpDampedWordNorm.rawZeroCaps, byteComparison, Fin.ext_iff]

theorem marked_to_degree (i j : Fin 5) :
    (Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val * markedCap (i.val+j.val) ≤
      hs i j ^ 2 := by
  fin_cases i <;> fin_cases j <;> norm_num [hs, markedCap, Nat.choose]

theorem hs_total : (∑ i : Fin 5, ∑ j : Fin 5, hs i j ^ 2) = 85011/20 := by
  simp only [sum_fin_five]
  norm_num [hs, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem hs_total_lt : (∑ i : Fin 5, ∑ j : Fin 5, hs i j ^ 2) < 4251 := by
  rw [hs_total]
  norm_num

theorem gram_row_cap (i j : Fin 5) :
    (∑ h : Fin 5, min (hs h i * op h j) (op h i * hs h j)) < gramCap i j := by
  rw [sum_fin_five]
  fin_cases i <;> fin_cases j <;>
    norm_num [hs, op, gramCap, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]

theorem gram_total :
    (∑ i : Fin 5, ∑ j : Fin 5, gramCap i j ^ 2) = 8974717/100 := by
  simp only [sum_fin_five]
  norm_num [gramCap, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]

theorem gram_total_lt : (∑ i : Fin 5, ∑ j : Fin 5, gramCap i j ^ 2) < 90000 := by
  rw [gram_total]
  norm_num

theorem activity_trace_number :
    (4294967296 : ℝ) * ((68*256^2+264*256+68)/(256-1)^6) < 71 := by
  norm_num

end AESConcrete.WordMomentNumbers
