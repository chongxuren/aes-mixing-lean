import AESConcrete.ByteGramCore
import AESMixing.AESPairing
import AESMixing.FourierGram
import AESMixing.PointedProducts

/-!
# Fourier transport of actual byte residual Grams

Multiplicative invariance, symmetry, and the exact zero-row/row-sum data
give Fourier invariance of the inversion Gram. The same argument fixes
the activity projection. These entrywise identities, rather than norm
invariance alone, justify transporting signed profiles and absolute cube
sums between the four actual byte orientations. No finite overlap or
mixed-entry bound is assumed here. Constructive scope only; no attacks.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ByteGramFourier
open AESMixing
open AESConcrete.ByteGramCore
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)

def byteConjugate (T : Byte → Byte → ℝ) : Byte → Byte → ℝ :=
  kernelCompose byteFourierMatrix (kernelCompose T byteFourierMatrix)

theorem byteFourier_symmetric (a b : Byte) : byteFourierMatrix a b = byteFourierMatrix b a := by
  unfold byteFourierMatrix
  rw [mul_comm a b]

theorem byteFourier_pairing : byteFourierMatrix = pairingFourier bytePairing := by
  funext a b
  simp only [byteFourierMatrix, pairingFourier, bytePairing, BinaryWord.card]
  norm_num
  rw [show (256 : ℝ) = (16 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

theorem byteConjugate_pairing (T : Byte → Byte → ℝ) :
    byteConjugate T = fourierConjugate bytePairing T := by
  unfold byteConjugate fourierConjugate
  rw [byteFourier_pairing]

theorem byteFourier_twice (f : Byte → ℝ) :
    action byteFourierMatrix (action byteFourierMatrix f) = f := by
  rw [byteFourier_pairing]
  exact pairingFourier_twice bytePairing BinaryWord.add_self f

/-- A multiplicatively invariant kernel has a product-indexed one-sided
Fourier kernel when its zero row and row-one sum match. -/
theorem mixed_product (T : Byte → Byte → ℝ) (s : ℝ)
    (hzero : ∀ z, T 0 z = if z = 0 then s else 0)
    (hsum : (∑ z, T 1 z) = s)
    (hscale : ∀ (c : Byte), c ≠ 0 → ∀ a b, T (c * a) (c * b) = T a b)
    (a b : Byte) :
    kernelCompose T byteFourierMatrix a b =
      kernelCompose T byteFourierMatrix 1 (a * b) := by
  have hz : kernelCompose T byteFourierMatrix 1 0 = s / 16 := by
    unfold kernelCompose byteFourierMatrix
    simp only [mul_zero, byteCharacter_zero]
    rw [← Finset.sum_mul, hsum]
    ring
  by_cases ha : a = 0
  · subst a
    rw [zero_mul, hz]
    simp [kernelCompose, hzero, byteFourierMatrix, byteCharacter_zero, div_eq_mul_inv]
  · have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha)
      (fun z => T a z * byteFourierMatrix z b)
    change (∑ z, T a (a * z) * byteFourierMatrix (a * z) b) =
      kernelCompose T byteFourierMatrix a b at he
    rw [← he]
    unfold kernelCompose
    apply Finset.sum_congr rfl
    intro z _
    have ht : T a (a * z) = T 1 z := by simpa only [mul_one] using hscale a ha 1 z
    rw [ht]
    congr 1
    unfold byteFourierMatrix
    rw [show (a * z) * b = z * (a * b) by ring]

theorem multiplicative_fourier_commutes (T : Byte → Byte → ℝ) (s : ℝ)
    (hsym : ∀ a b, T a b = T b a)
    (hzero : ∀ z, T 0 z = if z = 0 then s else 0)
    (hsum : (∑ z, T 1 z) = s)
    (hscale : ∀ (c : Byte), c ≠ 0 → ∀ a b, T (c * a) (c * b) = T a b) :
    kernelCompose byteFourierMatrix T = kernelCompose T byteFourierMatrix := by
  funext a b
  calc
    _ = kernelCompose T byteFourierMatrix b a := by
      unfold kernelCompose
      apply Finset.sum_congr rfl
      intro z _
      rw [hsym z b, byteFourier_symmetric a z]
      exact mul_comm _ _
    _ = kernelCompose T byteFourierMatrix 1 (b * a) :=
      mixed_product T s hzero hsum hscale b a
    _ = kernelCompose T byteFourierMatrix 1 (a * b) := by rw [mul_comm b a]
    _ = _ := (mixed_product T s hzero hsum hscale a b).symm

theorem multiplicative_fourier_fixed (T : Byte → Byte → ℝ) (s : ℝ)
    (hsym : ∀ a b, T a b = T b a)
    (hzero : ∀ z, T 0 z = if z = 0 then s else 0)
    (hsum : (∑ z, T 1 z) = s)
    (hscale : ∀ (c : Byte), c ≠ 0 → ∀ a b, T (c * a) (c * b) = T a b) :
    byteConjugate T = T := by
  apply kernel_action_ext
  intro f
  rw [byteConjugate, kernelCompose_action, kernelCompose_action,
    ← kernelCompose_action,
    multiplicative_fourier_commutes T s hsym hzero hsum hscale,
    kernelCompose_action, byteFourier_twice]

theorem activity_scale (c : Byte) (hc : c ≠ 0) (a b : Byte) :
    activityMatrix 0 (c * a) (c * b) = activityMatrix 0 a b := by
  change activityMatrix 0 ((Equiv.mulLeft₀ c hc) a) ((Equiv.mulLeft₀ c hc) b) = _
  rw [activity_relabel_left _ (by simp), activity_relabel_right _ (by simp)]

theorem activity_fourier_fixed : byteConjugate (activityMatrix (0 : Byte)) = activityMatrix 0 := by
  apply multiplicative_fourier_fixed _ 1
  · exact ByteGramDiagonal.activity_symmetric
  · intro z
    simp [activityMatrix]
  · exact (activityMatrix_pointed (0 : Byte) (by norm_num [BinaryWord.card])).row_sum 1
  · exact activity_scale

theorem inversion_gram_scale (c : Byte) (hc : c ≠ 0) (a b : Byte) :
    inversionGram (c * a) (c * b) = inversionGram a b := by
  by_cases ha : a = 0
  · subst a
    simp only [mul_zero, inversion_gram_zero_row]
  by_cases hb : b = 0
  · subst b
    simp only [mul_zero, inversion_gram_zero_column]
  have hca := mul_ne_zero hc ha
  have hcb := mul_ne_zero hc hb
  have heq : c * a = c * b ↔ a = b := by
    constructor
    · exact mul_left_cancel₀ hc
    · rintro rfl
      rfl
  have hquot : (c * a) / (c * b) = a / b := by field_simp [hc, hb]
  have hquot' : (c * b) / (c * a) = b / a := by field_simp [hc, ha]
  rw [inversion_gram_nonzero _ _ hca hcb, inversion_gram_nonzero _ _ ha hb,
    hquot, hquot']
  simp only [heq]

theorem inversion_gram_fourier_fixed : byteConjugate inversionGram = inversionGram := by
  apply multiplicative_fourier_fixed _ 0 inversion_gram_symmetric
  · intro z
    simp only [inversion_gram_zero_row, ite_self]
  · exact inversion_gram_row_sum 1
  · exact inversion_gram_scale

theorem byteConjugate_sub (D E : Byte → Byte → ℝ) :
    byteConjugate (D - E) = byteConjugate D - byteConjugate E := by
  funext a b
  unfold byteConjugate kernelCompose
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]

theorem squared_walsh_conjugate : aesSquaredWalshChannel = byteConjugate aesByteChannel := by
  funext a b
  exact (byteFourier_ddt_coefficient a b).symm

theorem byteConjugate_transpose (T : Byte → Byte → ℝ) :
    byteConjugate (fun y x => T x y) = fun y x => byteConjugate T x y := by
  funext a b
  unfold byteConjugate kernelCompose
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [byteFourier_symmetric a x, byteFourier_symmetric y b]
  ring

/-- The Fourier residual Gram identity includes the actual activity
correction. The nonnegative channel interface alone does not supply it. -/
theorem residual_gram_conjugate {D E : Byte → Byte → ℝ}
    (hD : ByteResources D) (hE : ByteResources E) (hED : E = byteConjugate D) :
    residualGram E = byteConjugate (residualGram D) := by
  have hgram : gram E = byteConjugate (gram D) := by
    calc
      gram E = gram (fourierConjugate bytePairing D) := by
        rw [hED, byteConjugate_pairing]
      _ = fourierConjugate bytePairing (gram D) := by
        funext a b
        exact fourierConjugate_gram bytePairing BinaryWord.add_self D a b
      _ = byteConjugate (gram D) := (byteConjugate_pairing (gram D)).symm
  have hleft : residualGram E = gram E - activityMatrix 0 := by
    funext a b
    exact ByteGramDiagonal.residual_gram_formula hE a b
  have hright : residualGram D = gram D - activityMatrix 0 := by
    funext a b
    exact ByteGramDiagonal.residual_gram_formula hD a b
  rw [hleft, hright, byteConjugate_sub, activity_fourier_fixed, hgram]

theorem byteDualEquiv_apply (A : Byte ≃+ Byte) (v : Byte) :
    byteDualEquiv A v = byteCharacterDual A v := by
  simp [byteDualEquiv]

theorem dual_spec (A : Byte ≃+ Byte) (v x : Byte) :
    byteCharacter (v * A x) = byteCharacter (byteDualEquiv A v * x) := by
  rw [byteDualEquiv_apply]
  exact byteCharacterDual_spec A v x

theorem fourier_relabel (T : Byte → Byte → ℝ) (A : Byte ≃+ Byte) (a b : Byte) :
    byteConjugate (fun y x => T (A.symm y) (A.symm x)) a b =
      byteConjugate T (byteDualEquiv A a) (byteDualEquiv A b) := by
  have hleft (v x : Byte) : byteFourierMatrix v (A x) =
      byteFourierMatrix (byteDualEquiv A v) x := by
    unfold byteFourierMatrix
    rw [dual_spec]
  have hright (x : Byte) : byteFourierMatrix (A x) b =
      byteFourierMatrix x (byteDualEquiv A b) := by
    rw [byteFourier_symmetric (A x) b, hleft b x]
    exact byteFourier_symmetric _ _
  unfold byteConjugate kernelCompose
  calc
    _ = ∑ y, byteFourierMatrix a (A y) *
        ∑ x, T (A.symm (A y)) (A.symm x) * byteFourierMatrix x b :=
      (Equiv.sum_comp A.toEquiv
        (fun y => byteFourierMatrix a y *
          ∑ x, T (A.symm y) (A.symm x) * byteFourierMatrix x b)).symm
    _ = ∑ y, byteFourierMatrix (byteDualEquiv A a) y *
        ∑ x, T y (A.symm x) * byteFourierMatrix x b := by
      simp only [A.symm_apply_apply, hleft]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      calc
        _ = ∑ x, T y (A.symm (A x)) * byteFourierMatrix (A x) b :=
          (Equiv.sum_comp A.toEquiv
            (fun x => T y (A.symm x) * byteFourierMatrix x b)).symm
        _ = _ := by simp only [A.symm_apply_apply, hright]

theorem byteDualEquiv_add (A : Byte ≃+ Byte) (a b : Byte) :
    byteDualEquiv A (a + b) = byteDualEquiv A a + byteDualEquiv A b := by
  apply byte_character_index_unique
  intro x
  rw [← dual_spec, add_mul, byteCharacter_add,
    dual_spec, dual_spec, ← byteCharacter_add, ← add_mul]

def byteDualAddEquiv (A : Byte ≃+ Byte) : Byte ≃+ Byte :=
  { byteDualEquiv A with map_add' := byteDualEquiv_add A }

/-- Relabeling of the common inversion Gram, including the dual affine map. -/
def gramRelabel : Orientation → Byte ≃+ Byte
  | .ordinary => AddEquiv.refl Byte
  | .transposed => AES.affineLinearEquiv.symm
  | .fourier => AddEquiv.refl Byte
  | .fourierTransposed => byteDualAddEquiv AES.affineLinearEquiv

theorem actual_gram_relabel (o : Orientation) (a b : Byte) :
    residualGram (channel o) a b = inversionGram (gramRelabel o a) (gramRelabel o b) := by
  cases o
  · exact aes_gram a b
  · exact aes_transpose_gram a b
  · have h := residual_gram_conjugate aes_byte_resources aes_fourier_byte_resources
      squared_walsh_conjugate
    have hbase : residualGram aesByteChannel = inversionGram := funext (fun x => funext (aes_gram x))
    rw [hbase, inversion_gram_fourier_fixed] at h
    exact congrFun (congrFun h a) b
  · have hED : (fun y x => aesSquaredWalshChannel x y) =
        byteConjugate (fun y x => aesByteChannel x y) := by
      rw [byteConjugate_transpose, ← squared_walsh_conjugate]
    have h := residual_gram_conjugate aes_byte_transpose_resources
      aes_fourier_byte_transpose_resources hED
    have hbase : residualGram (fun y x => aesByteChannel x y) =
        fun y x => inversionGram (AES.affineLinearEquiv.symm y) (AES.affineLinearEquiv.symm x) :=
      funext (fun x => funext (aes_transpose_gram x))
    rw [hbase] at h
    have hentry := congrFun (congrFun h a) b
    rw [fourier_relabel, inversion_gram_fourier_fixed] at hentry
    exact hentry

/-- A common-Gram relabeling turns the one-sided Fourier kernel into
independent row and column relabelings. This preserves an entrywise cap. -/
theorem mixed_relabel (T : Byte → Byte → ℝ) (A : Byte ≃+ Byte) (a b : Byte) :
    kernelCompose (fun y x => T (A y) (A x)) byteFourierMatrix a b =
      kernelCompose T byteFourierMatrix (A a) (byteDualEquiv A.symm b) := by
  unfold kernelCompose
  calc
    _ = ∑ x, T (A a) (A (A.symm x)) * byteFourierMatrix (A.symm x) b :=
      (Equiv.sum_comp A.symm.toEquiv
        (fun x => T (A a) (A x) * byteFourierMatrix x b)).symm
    _ = _ := by
      simp only [A.apply_symm_apply]
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      unfold byteFourierMatrix
      rw [mul_comm (A.symm x) b, dual_spec, mul_comm (byteDualEquiv A.symm b) x]

end AESConcrete.ByteGramFourier
