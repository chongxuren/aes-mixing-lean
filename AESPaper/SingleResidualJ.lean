import AESPaper.ResidualMarginal

/-!
# One residual factor and three full-uniform factors
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.SingleResidualJ
open AESMixing AESConcrete
open AESPaper.StartingWord (q)
open AESPaper.ResidualMarginal (R)
open AESConcrete.RestrictedMarginalEnergy (marginal)

theorem sum_marginal {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (coord : X → Y) (f : X → ℝ) (a : Y → ℝ) :
    (∑ y, a y * marginal coord f y) = ∑ x, a (coord x) * f x := by
  simp only [marginal, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [mul_ite, eq_comm]

def kernel (c : Fin 4) (y x : AES.WordState) : ℝ :=
  ∏ i, if i=c then R (y i) (x i) else 1/q

theorem kernel_eq (c : Fin 4) (y x : AES.WordState) :
    kernel c y x = (1/q)^3 * R (y c) (x c) := by
  fin_cases c <;> simp [kernel, Fin.prod_univ_four] <;> norm_num [q] <;> ring

/-- Exact action of the actual tensor kernel on a possibly correlated law. -/
theorem action_eq (c : Fin 4) (f : AES.WordState → ℝ) (y : AES.WordState) :
    action (kernel c) f y = (1/q)^3 *
      action R (marginal (fun x : AES.WordState => x c) f) (y c) := by
  change (∑ x, kernel c y x * f x) = (1/q)^3 *
    (∑ v, R (y c) v * marginal (fun x : AES.WordState => x c) f v)
  rw [sum_marginal]
  simp only [kernel_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem coordinate_energy (c : Fin 4) (f : AES.Word → ℝ) :
    (∑ y : AES.WordState, f (y c)^2) = q^3 * ∑ v, f v^2 := by
  have hp (y : AES.WordState) :
      (∏ i : Fin 4, if i=c then f (y i)^2 else 1) = f (y c)^2 := by
    fin_cases c <;> simp [Fin.prod_univ_four]
  calc
    _ = ∑ y : AES.WordState, ∏ i : Fin 4, if i=c then f (y i)^2 else 1 := by
      simp only [hp]
    _ = ∏ i : Fin 4, ∑ v : AES.Word, if i=c then f v^2 else 1 :=
      (Fintype.prod_sum (fun i v => if i=c then f v^2 else (1 : ℝ))).symm
    _ = _ := by
      fin_cases c <;> simp [Fin.prod_univ_four] <;> norm_num [BinaryWord.card, q] <;> ring

/-- Three uniform output coordinates contribute q^(-3) to squared energy. -/
theorem energy_eq (c : Fin 4) (f : AES.WordState → ℝ) :
    (∑ y, action (kernel c) f y ^ 2) = (1/q)^3 *
      ∑ v, action R (marginal (fun x : AES.WordState => x c) f) v ^ 2 := by
  simp only [action_eq, mul_pow, ← Finset.mul_sum]
  rw [coordinate_energy]
  ring_nf
  norm_num [q]

theorem scaled_energy_le (c : Fin 4) (f : AES.WordState → ℝ)
    (hf : (∑ v, (marginal (fun x : AES.WordState => x c) f v - 1/q)^2) ≤
      1/(25*q)) :
    q^5 * (∑ y, action (kernel c) f y ^ 2) ≤ 441/100 := by
  rw [energy_eq]
  have h := ResidualMarginal.response_energy_le _ hf
  have hmul := mul_le_mul_of_nonneg_left h
    (show 0 ≤ q^5 * (1/q)^3 by norm_num [q])
  calc
    _ = (q^5 * (1/q)^3) *
        (∑ v, action R (marginal (fun x : AES.WordState => x c) f) v ^ 2) := by ring
    _ ≤ (q^5 * (1/q)^3) * (441/(100*q^2)) := hmul
    _ = 441/100 := by norm_num [q]

/-- Sum over the four literal residual positions, before the Z contributions. -/
theorem total_scaled_energy_lt (f : AES.WordState → ℝ)
    (hf : ∀ c : Fin 4,
      (∑ v, (marginal (fun x : AES.WordState => x c) f v-1/q)^2) ≤ 1/(25*q)) :
    q^5 * (∑ c : Fin 4, ∑ y, action (kernel c) f y ^ 2) < 92/5 := by
  calc
    _ = ∑ c : Fin 4, q^5 * (∑ y, action (kernel c) f y ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _ : Fin 4, (441/100 : ℝ) :=
      Finset.sum_le_sum (fun c _ => scaled_energy_le c f (hf c))
    _ < 92/5 := by norm_num

end AESPaper.SingleResidualJ
