import AESConcrete.ByteGramResources
import AESConcrete.ByteGramMixed
import AESConcrete.DampedLineGram

/-!
# Concrete byte resources for damped three-leg lines

Each leg has its own fixed actual AES orientation. A Fourier flag acts on the
input of that leg's residual. The response vectors stay in their joint output
space. These are actual line-response estimates; identification with the MDS
shortenings and the activity-frame degree-three block remains a separate proof.
Constructive mathematics only; no attacks or manuscript edits.
-/
noncomputable section
open scoped BigOperators
namespace AESConcrete.ByteLineBounds
open AESMixing
open AESConcrete.ByteGramCore
open AESConcrete.ByteGramFourier
open AESConcrete.ByteGramResources
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.DampedLineGram

def residual (o : Orientation) : Byte → Byte → ℝ := residualMatrix (channel o) 0

def leg (o : Orientation) (fourier : Bool) : Byte → Byte → ℝ :=
  if fourier then kernelCompose (residual o) byteFourierMatrix else residual o

def cubeBound : ℝ := 255 * cubeNumerator / 4177920^3
def a3 : ℝ := 65536 * cubeBound
def mixedCubeBound : ℝ := (13276 / (4 * 4177920)) * (571447 / 2^27)
def b3 : ℝ := 65536 * mixedCubeBound

theorem a3_lt_eleven_tenths : a3 < (11 / 10 : ℝ) := by
  norm_num [a3, cubeBound, cubeNumerator]

theorem b3_lt_223_thousandths : b3 < (223 / 1000 : ℝ) := by
  norm_num [b3, mixedCubeBound]

/-- Right Fourier multiplication preserves the full counting-measure
square sum; it is not a statement about entrywise maxima. -/
theorem right_fourier_square_sum (T : Byte → Byte → ℝ) :
    (∑ a, ∑ b, kernelCompose T byteFourierMatrix a b ^ 2) =
      ∑ a, ∑ b, T a b ^ 2 := by
  have hp (a b : Byte) : kernelCompose T byteFourierMatrix a b =
      byteFourier (T a) b := by
    unfold kernelCompose byteFourier action
    apply Finset.sum_congr rfl
    intro z _
    rw [byteFourier_symmetric z b]
    exact mul_comm _ _
  simp_rw [hp, byteFourier_energy]

theorem actual_mixed_square_moment (o : Orientation) :
    (∑ a, ∑ b,
      kernelCompose (residualGram (channel o)) byteFourierMatrix a b ^ 2) =
      (571447 / 2^27 : ℝ) := by
  rw [right_fourier_square_sum]
  exact actual_gram_square_moment o

theorem actual_mixed_cube_bound (o : Orientation) :
    (∑ p : Byte × Byte,
      |kernelCompose (residualGram (channel o)) byteFourierMatrix p.1 p.2|^3) ≤
      mixedCubeBound := by
  apply cube_sum_le_max_mul_square_sum
  · norm_num
  · intro p
    exact ByteGramMixed.actual_gram_mixed_bound o p.1 p.2
  · rw [Fintype.sum_prod_type]
    exact le_of_eq (actual_mixed_square_moment o)

theorem gram_conjugate_cube (o : Orientation) :
    (∑ a, ∑ b, |byteConjugate (residualGram (channel o)) a b|^3) = cubeBound := by
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
  exact inversion_gram_absolute_cube

theorem leg_gram_cube (o : Orientation) (s : Bool) :
    (∑ p : Byte × Byte, |crossGram (leg o s) (leg o s) p.1 p.2|^3) = cubeBound := by
  cases s
  · change (∑ p : Byte × Byte, |residualGram (channel o) p.1 p.2|^3) = cubeBound
    rw [Fintype.sum_prod_type]
    exact actual_gram_absolute_cube o
  · change (∑ p : Byte × Byte,
      |crossGram (kernelCompose (residual o) byteFourierMatrix)
        (kernelCompose (residual o) byteFourierMatrix) p.1 p.2|^3) = cubeBound
    rw [crossGram_compose_both _ _ _ byteFourier_symmetric]
    change (∑ p : Byte × Byte,
      |byteConjugate (residualGram (channel o)) p.1 p.2|^3) = cubeBound
    rw [Fintype.sum_prod_type]
    exact gram_conjugate_cube o

/-- Uniform concrete line-pair bound with any fixed permitted orientation
and Fourier flag on each of the three legs. No numerical premise remains. -/
theorem actual_line_pair_bound (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (e f : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      |∑ y, lineResponse (fun i => leg (o i) (s i)) e y *
        lineResponse (fun i => leg (o i) (s i)) f y| ≤ a3 := by
  apply byte_lineResponse_scaled_bound
  intro i
  exact le_of_eq (leg_gram_cube (o i) (s i))

theorem actual_line_energy_bound (o : Fin 3 → Orientation) (s : Fin 3 → Bool)
    (e : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      (∑ y, lineResponse (fun i => leg (o i) (s i)) e y ^ 2) ≤ a3 := by
  have h := actual_line_pair_bound o s e e
  simp only [← pow_two] at h
  rw [abs_of_nonneg (Finset.sum_nonneg (fun y _ => sq_nonneg _))] at h
  exact h

/-- The actual mixed R/RF pair estimate used in the final line/plane case.
The same fixed residual orientation is used on both sides of each leg. -/
theorem actual_mixed_line_pair_bound (o : Fin 3 → Orientation)
    (e f : Fin 3 → Equiv.Perm Byte) :
    (4294967296 : ℝ) *
      |∑ y, lineResponse (fun i => leg (o i) false) e y *
        lineResponse (fun i => leg (o i) true) f y| ≤ b3 := by
  apply byte_lineResponse_scaled_bound
  intro i
  change (∑ p : Byte × Byte,
    |crossGram (residual (o i)) (kernelCompose (residual (o i)) byteFourierMatrix)
      p.1 p.2|^3) ≤ mixedCubeBound
  rw [crossGram_compose_right]
  exact actual_mixed_cube_bound (o i)

end AESConcrete.ByteLineBounds
