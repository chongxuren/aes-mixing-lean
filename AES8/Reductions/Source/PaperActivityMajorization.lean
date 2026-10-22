import AES8.Math.PaperSourceMajorization
import AESConcrete.ActualColumnActivity

/-!
# The affine majorant on the actual AES degree-zero response

This bridge uses the checked exact activity-energy identity, not a claimed
relation between probability and energy. The complete 14-event all-caps box
is used for every input with two, three or four active bytes; impossible events
have zero probability. Scalar cap comparisons remain explicit, allowing the
numerical resources to change independently of this reduction. No numerical
search or manuscript edit is performed.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityMajorization
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Word)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ActualZeroEventProbabilities
open AESConcrete.MultibyteColumnNumbers (zeroCap)

/-- The all-caps expression in the paper, before any numerical upper bound. -/
def allCaps (p rho : ℝ) : ℝ :=
  (1 - (4*rho + 6*p*rho + 4*p^2*rho))^2 +
    4*255*rho^2 + 6*255^2*(p*rho)^2 + 4*255^3*(p^2*rho)^2

/-- Count the nonempty proper four-coordinate masks by size, symbolically. -/
theorem quadratic_eq_allCaps (p rho : ℝ) :
    PaperSourceMajorization.quadratic
      (fun r : SmallMask 4 => (255 : ℝ)^maskSize r.val)
      (fun r : SmallMask 4 => p^(maskSize r.val-1)*rho) = allCaps p rho := by
  unfold PaperSourceMajorization.quadratic allCaps
  rw [sum_small_by_size (fun k => p^(k-1)*rho) 4 (by omega),
    sum_small_by_size (fun k => (255 : ℝ)^k * (p^(k-1)*rho)^2) 4 (by omega)]
  norm_num [Finset.sum_range_succ, Nat.choose]
  ring

/-- Exact probability caps supplied by the checked shortened source resource
imply the all-caps bound through the current paper's affine-majorant argument.
`hcap` is purely a scalar comparison with the previously checked local cap. -/
theorem actual_probability_collision_le (right : Orientation) (inverse : Bool)
    (a : Word) (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (p rho : ℝ) (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hcap : ∀ k : ℕ, 0 < k → k < t → zeroCap t k ≤ p^(k-1)*rho)
    (hbase : 2 < (255 : ℝ)*rho) (hgrowth : 1 ≤ (255 : ℝ)*p) :
    (∑ r : Fin 16, (255 : ℝ)^maskSize r * exactMass right inverse a r ^ 2)
      ≤ allCaps p rho := by
  have ha0 := input_nonzero_of_active_count a z ha (by omega)
  have hbig (r : Fin 16) (hr : 4 ≤ maskSize r) : exactMass right inverse a r = 0 :=
    exactMass_forbidden right inverse a r z ha0 ha (by omega)
  have hm : exactMass right inverse a 0 +
      (∑ r : SmallMask 4, exactMass right inverse a r.val) = 1 := by
    rw [← sum_empty_add_small 4 (by omega) _ hbig]
    exact exactMass_sum_one right inverse a
  have hw : (∑ r : Fin 16, (255 : ℝ)^maskSize r * exactMass right inverse a r ^ 2) =
      exactMass right inverse a 0 ^ 2 + ∑ r : SmallMask 4,
        (255 : ℝ)^maskSize r.val * exactMass right inverse a r.val ^ 2 := by
    have he := sum_empty_add_small 4 (by omega)
      (fun r => (255 : ℝ)^maskSize r * exactMass right inverse a r ^ 2)
      (fun r hr => by rw [hbig r hr]; simp)
    simpa only [show maskSize (0 : Fin 16) = 0 by decide, pow_zero, one_mul] using he
  rw [hw, ← quadratic_eq_allCaps]
  apply PaperSourceMajorization.collision_with_complement _ _ _ _ hm
  · intro r
    positivity
  · intro r
    exact exactMass_nonneg right inverse a r.val
  · intro r
    by_cases hsmall : maskSize r.val < t
    · exact (exactMass_le_zeroCap right inverse a r.val z t ht hcount ha
        ⟨r.property.1, hsmall⟩).trans (hcap _ r.property.1 hsmall)
    · rw [exactMass_forbidden right inverse a r.val z ha0 ha (by omega)]
      exact mul_nonneg (pow_nonneg hp _) hrho
  · intro r
    exact (PaperSourceMajorization.weighted_geometric_cap_gt_two 255 p rho
      (maskSize r.val) r.property.1 hbase hgrowth).le

/-- The literal actual degree-zero word response, in every channel orientation.
Only local scalar-resource comparisons remain; the energy identity,
probability caps, affine majorization and 4/6/4 multiplicities are proved. -/
theorem actual_activity_energy_le (left right : Orientation) (inverse : Bool)
    (a : Word) (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (p rho : ℝ) (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hcap : ∀ k : ℕ, 0 < k → k < t → zeroCap t k ≤ p^(k-1)*rho)
    (hbase : 2 < (255 : ℝ)*rho) (hgrowth : 1 ≤ (255 : ℝ)*p) :
    (∑ y : Word, degreeComponent (0 : AESConcrete.WordColumnGram.Byte) 0
      (fun v => wordKernel left right inverse v a) y ^ 2) ≤ allCaps p rho / 255^4 := by
  rw [AESConcrete.ActualColumnActivity.column_activity_energy]
  exact div_le_div_of_nonneg_right
    (actual_probability_collision_le right inverse a z t ht hcount ha p rho hp hrho
      hcap hbase hgrowth) (by norm_num)

end AES8.PaperActivityMajorization
