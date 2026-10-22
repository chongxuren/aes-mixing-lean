import Mathlib.Algebra.Field.ZMod
import AES8.Model.Byte.PaperAESExpansion

noncomputable section
namespace AES8.PaperAESAlgebraic
open Polynomial AESMixing
open scoped BigOperators
set_option autoImplicit false

theorem generator_integral : IsIntegral (ZMod 2) generator :=
  ⟨modulus, modulus_monic, modulus_root⟩

set_option maxHeartbeats 200000 in
theorem generator_degree : (minpoly (ZMod 2) generator).natDegree = 8 := by
  have hn := minpoly.ne_zero generator_integral
  have hu : (minpoly (ZMod 2) generator).natDegree ≤ 8 := by
    calc
      _ ≤ modulus.natDegree := Polynomial.natDegree_le_of_dvd
        (minpoly.dvd (ZMod 2) generator (p := modulus) modulus_root) modulus_monic.ne_zero
      _ = 8 := modulus_degree
  have hl : 8 ≤ (minpoly (ZMod 2) generator).natDegree := by
    by_contra h
    have hdeg : (minpoly (ZMod 2) generator).natDegree < 8 := by omega
    let p := minpoly (ZMod 2) generator
    have he : p = ∑ i : Fin 8, monomial i.val (p.coeff i.val) := by
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => monomial n (p.coeff n))]
      exact p.as_sum_range' 8 hdeg
    have hz : byteEval (fun i : Fin 8 => p.coeff i.val) = 0 := by
      rw [← eval_coeff_sum, ← he]
      exact minpoly.aeval (ZMod 2) generator
    have hv := byteEval_zero _ hz
    have hc (i : Fin 8) : p.coeff i.val = 0 := congrFun hv i
    apply hn
    change p = 0
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_zero]
    by_cases hni : n < 8
    · exact hc ⟨n, hni⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by dsimp [p]; omega)
  omega

theorem generator_degree_gt_six : 6 < (minpoly (ZMod 2) generator).natDegree := by
  rw [generator_degree]
  omega

theorem matrix_is_AES (i j : Fin 4) :
    PaperSymbolicDiffusion.matrix generator i j = (⟨AES.mixEntry i j⟩ : Byte) := by
  fin_cases i <;> fin_cases j <;> decide

end AES8.PaperAESAlgebraic
