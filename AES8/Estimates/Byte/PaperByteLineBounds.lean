import AES8.Estimates.Byte.PaperByteCubePrinted
import AES8.Estimates.Byte.PaperByteMixedPrinted
import AESConcrete.ByteLineBounds

/-!
# Printed byte resources for line and plane contractions

The symbolic absolute cube and mixed-entry bound feed the existing generic
Fourier, max-times-square and three-leg line inequalities. The accepted Walsh
input stays explicit in conditional endpoints; concrete providers are separate.
Historical exact cube and Walsh-at-one facts are not called by this route.
Constructive source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperByteLineBounds
open AESMixing
open AESConcrete.ByteGramCore (Byte inversionGram)
open AESConcrete.ByteGramFourier
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ByteLineBounds (residual leg cubeBound a3 mixedCubeBound b3)
open AESConcrete.DampedLineGram
set_option maxRecDepth 100000

/-- Right Fourier multiplication preserves the full square sum. -/
theorem actual_mixed_square_moment_le_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (o : Orientation) :
    (∑ a, ∑ b,
      kernelCompose (residualGram (channel o)) byteFourierMatrix a b ^ 2) ≤
      (571447 / 2^27 : ℝ) := by
  rw [AESConcrete.ByteLineBounds.right_fourier_square_sum]
  exact AES8.PaperByteGramPrinted.actual_gram_square_moment_le_of_walsh hWalsh o

theorem actual_mixed_cube_bound_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (o : Orientation) :
    (∑ p : Byte × Byte,
      |kernelCompose (residualGram (channel o)) byteFourierMatrix p.1 p.2|^3) ≤
      mixedCubeBound := by
  apply cube_sum_le_max_mul_square_sum
  · norm_num
  · intro p
    exact AES8.PaperByteMixedPrinted.actual_gram_mixed_bound_of_walsh hWalsh o p.1 p.2
  · rw [Fintype.sum_prod_type]
    exact actual_mixed_square_moment_le_of_walsh hWalsh o

/-- Exact Fourier relabeling transports the symbolic absolute cube. -/
theorem gram_conjugate_cube_le_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (o : Orientation) :
    (∑ a, ∑ b, |byteConjugate (residualGram (channel o)) a b|^3) ≤ cubeBound := by
  have he : residualGram (channel o) =
      fun a b => inversionGram (gramRelabel o a) (gramRelabel o b) :=
    funext (fun a => funext (actual_gram_relabel o a))
  have hp (a b : Byte) : byteConjugate (residualGram (channel o)) a b =
      inversionGram (byteDualEquiv (gramRelabel o).symm a)
        (byteDualEquiv (gramRelabel o).symm b) := by
    rw [he]
    have h := fourier_relabel inversionGram (gramRelabel o).symm a b
    rw [inversion_gram_fourier_fixed] at h
    exact h
  simp_rw [hp]
  have hi (a : Byte) :
      (∑ b, |inversionGram (byteDualEquiv (gramRelabel o).symm a)
        (byteDualEquiv (gramRelabel o).symm b)|^3) =
      ∑ b, |inversionGram (byteDualEquiv (gramRelabel o).symm a) b|^3 :=
    Equiv.sum_comp (byteDualEquiv (gramRelabel o).symm)
      (fun b => |inversionGram (byteDualEquiv (gramRelabel o).symm a) b|^3)
  simp_rw [hi]
  rw [Equiv.sum_comp (byteDualEquiv (gramRelabel o).symm)
    (fun a => ∑ b, |inversionGram a b|^3)]
  exact AES8.PaperByteCubePrinted.inversion_absolute_cube_le_of_walsh hWalsh

theorem leg_gram_cube_le_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound) (o : Orientation) (s : Bool) :
    (∑ p : Byte × Byte, |crossGram (leg o s) (leg o s) p.1 p.2|^3) ≤ cubeBound := by
  cases s
  · change (∑ p : Byte × Byte, |residualGram (channel o) p.1 p.2|^3) ≤ cubeBound
    rw [Fintype.sum_prod_type]
    exact AES8.PaperByteCubePrinted.actual_gram_absolute_cube_le_of_walsh hWalsh o
  · change (∑ p : Byte × Byte,
      |crossGram (kernelCompose (residual o) byteFourierMatrix)
        (kernelCompose (residual o) byteFourierMatrix) p.1 p.2|^3) ≤ cubeBound
    rw [crossGram_compose_both _ _ _ byteFourier_symmetric]
    change (∑ p : Byte × Byte,
      |byteConjugate (residualGram (channel o)) p.1 p.2|^3) ≤ cubeBound
    rw [Fintype.sum_prod_type]
    exact gram_conjugate_cube_le_of_walsh hWalsh o

theorem actual_line_pair_bound_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (e f : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      |∑ y, lineResponse (fun i => leg (o i) (s i)) e y *
        lineResponse (fun i => leg (o i) (s i)) f y| ≤ a3 := by
  apply byte_lineResponse_scaled_bound
  intro i
  exact leg_gram_cube_le_of_walsh hWalsh (o i) (s i)

theorem actual_line_energy_bound_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (o : Fin 3 → Orientation) (s : Fin 3 → Bool) (e : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      (∑ y, lineResponse (fun i => leg (o i) (s i)) e y ^ 2) ≤ a3 := by
  have h := actual_line_pair_bound_of_walsh hWalsh o s e e
  simp only [← pow_two] at h
  rw [abs_of_nonneg (Finset.sum_nonneg (fun y _ => sq_nonneg _))] at h
  exact h

/-- Independent fixed orientations remain explicit on all three legs. -/
theorem actual_mixed_line_pair_bound_of_walsh
    (hWalsh : PaperCitedByteBounds.InversionWalshSqBound)
    (o : Fin 3 → Orientation) (e f : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      |∑ y, lineResponse (fun i => leg (o i) false) e y *
        lineResponse (fun i => leg (o i) true) f y| ≤ b3 := by
  apply byte_lineResponse_scaled_bound
  intro i
  change (∑ p : Byte × Byte,
    |crossGram (residual (o i)) (kernelCompose (residual (o i)) byteFourierMatrix)
      p.1 p.2|^3) ≤ mixedCubeBound
  rw [crossGram_compose_right]
  exact actual_mixed_cube_bound_of_walsh hWalsh (o i)

-- Concrete wrappers contain only input-provider instantiation.
theorem actual_mixed_square_moment_le (o : Orientation) :
    (∑ a, ∑ b,
      kernelCompose (residualGram (channel o)) byteFourierMatrix a b ^ 2) ≤
      (571447 / 2^27 : ℝ) :=
  actual_mixed_square_moment_le_of_walsh PaperCitedByteBounds.concreteWalshBound o

theorem actual_mixed_cube_bound (o : Orientation) :
    (∑ p : Byte × Byte,
      |kernelCompose (residualGram (channel o)) byteFourierMatrix p.1 p.2|^3) ≤
      mixedCubeBound :=
  actual_mixed_cube_bound_of_walsh PaperCitedByteBounds.concreteWalshBound o

theorem actual_line_pair_bound (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (e f : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      |∑ y, lineResponse (fun i => leg (o i) (s i)) e y *
        lineResponse (fun i => leg (o i) (s i)) f y| ≤ a3 :=
  actual_line_pair_bound_of_walsh PaperCitedByteBounds.concreteWalshBound o s e f

theorem actual_line_energy_bound (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (e : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      (∑ y, lineResponse (fun i => leg (o i) (s i)) e y ^ 2) ≤ a3 :=
  actual_line_energy_bound_of_walsh PaperCitedByteBounds.concreteWalshBound o s e

theorem actual_mixed_line_pair_bound (o : Fin 3 → Orientation)
    (e f : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      |∑ y, lineResponse (fun i => leg (o i) false) e y *
        lineResponse (fun i => leg (o i) true) f y| ≤ b3 :=
  actual_mixed_line_pair_bound_of_walsh PaperCitedByteBounds.concreteWalshBound o e f

#print axioms actual_mixed_cube_bound_of_walsh
#print axioms gram_conjugate_cube_le_of_walsh
#print axioms leg_gram_cube_le_of_walsh
#print axioms actual_line_pair_bound_of_walsh
#print axioms actual_line_energy_bound_of_walsh
#print axioms actual_mixed_line_pair_bound_of_walsh
#print axioms actual_line_energy_bound
#print axioms actual_mixed_line_pair_bound
end AES8.PaperByteLineBounds
