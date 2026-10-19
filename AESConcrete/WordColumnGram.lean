import AESConcrete.WordOrientationClosure
import AESConcrete.ByteGramCore
import AESMixing.Gram

/-!
# Actual input columns and weighted tensor-response Grams

The generic response retains arbitrary, unnormalized real source weights.
Its Gram identity is exact and does not assume independence of output
coordinates. Actual first-substitution columns are product laws; the word
diffusion is retained inside the response coordinates. A source supported
in one input position reduces to one common byte source.

This module supplies no sharp column cap, restricted-MDS response estimate,
output-coordinate permutation theorem, or fourth-moment comparison.
Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordColumnGram
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ByteGramCore (NonzeroByte)

section GenericTensor

variable {I V X : Type*} [Fintype I] [DecidableEq I] [Fintype V] [Fintype X]

def tensorColumn (T : I → V → V → ℝ) (coords : X → I → V)
    (y : I → V) (x : X) : ℝ :=
  ∏ i : I, T i (y i) (coords x i)

def tensorResponse (T : I → V → V → ℝ) (coords : X → I → V)
    (mu : X → ℝ) (y : I → V) : ℝ :=
  ∑ x : X, tensorColumn T coords y x * mu x

/-- Full joint tensor Gram. The coordinate functions may be dependent. -/
theorem tensorColumn_gram (T : I → V → V → ℝ) (coords : X → I → V)
    (x z : X) :
    gram (tensorColumn T coords) x z =
      ∏ i : I, gram (T i) (coords x i) (coords z i) := by
  exact product_gram T (coords x) (coords z)

/-- Counting-measure energy for arbitrary signed, unnormalized source weights. -/
theorem tensorResponse_energy (T : I → V → V → ℝ) (coords : X → I → V)
    (mu : X → ℝ) :
    (∑ y : I → V, (tensorResponse T coords mu y)^2) =
      ∑ x : X, ∑ z : X, mu x*mu z*
        ∏ i : I, gram (T i) (coords x i) (coords z i) := by
  have h := gram_quadratic (tensorColumn T coords) mu
  simpa only [tensorResponse, tensorColumn_gram] using h

end GenericTensor

abbrev Byte := BinaryWord 8
abbrev Word := Fin 4 → Byte

/-- The actual law after the first substitution, before diffusion. -/
def inputColumn (right : Orientation) (a x : Word) : ℝ :=
  substitutionKernel (channel right) x a

theorem inputColumn_eq_product (right : Orientation) (a x : Word) :
    inputColumn right a x = ∏ i : Fin 4, channel right (x i) (a i) := rfl

theorem inputColumn_nonneg (right : Orientation) (a x : Word) :
    0 ≤ inputColumn right a x := by
  rw [inputColumn_eq_product]
  exact Finset.prod_nonneg (fun i _ => (channel_resources right).nonnegative _ _)

theorem inputColumn_mass (right : Orientation) (a : Word) :
    (∑ x : Word, inputColumn right a x) = 1 := by
  change (∑ x : Word, ∏ i : Fin 4, channel right (x i) (a i)) = 1
  calc
    _ = ∏ i : Fin 4, ∑ v : Byte, channel right v (a i) :=
      (Fintype.prod_sum (fun (i : Fin 4) (v : Byte) => channel right v (a i))).symm
    _ = 1 := by simp only [(channel_resources right).column_sum, Finset.prod_const_one]

theorem channel_column_collision (right : Orientation) (a : Byte) :
    (∑ b : Byte, channel right b a ^ 2) =
      if a = 0 then 1 else (65 : ℝ)/8192 := by
  by_cases ha : a = 0
  · subst a
    have hp (b : Byte) : channel right b 0 ^ 2 = if b = 0 then 1 else 0 := by
      rw [(channel_resources right).zero_column]
      split_ifs <;> norm_num
    simp_rw [hp]
    simp
  · rw [if_neg ha]
    exact (channel_resources right).collision_column a ha

/-- Exact collision before diffusion, for every concrete byte orientation. -/
theorem inputColumn_collision (right : Orientation) (a : Word) :
    (∑ x : Word, inputColumn right a x ^ 2) =
      ∏ i : Fin 4, if a i = 0 then 1 else (65 : ℝ)/8192 := by
  change (∑ x : Word, (∏ i : Fin 4, channel right (x i) (a i))^2) = _
  calc
    _ = ∏ i : Fin 4, ∑ v : Byte, channel right v (a i)^2 :=
      product_column_energy (fun (i : Fin 4) (v : Byte) => channel right v (a i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact channel_column_collision right (a i)

theorem channel_point_bound (right : Orientation) (a b : Byte) :
    channel right b a ≤ if a = 0 then 1 else (1 : ℝ)/64 := by
  by_cases ha : a = 0
  · subst a
    rw [(channel_resources right).zero_column]
    by_cases hb : b = 0 <;> simp [hb]
  · rw [if_neg ha]
    exact (channel_resources right).atom a b ha

theorem inputColumn_point_bound (right : Orientation) (a x : Word) :
    inputColumn right a x ≤ ∏ i : Fin 4, if a i = 0 then 1 else (1 : ℝ)/64 := by
  rw [inputColumn_eq_product]
  exact Finset.prod_le_prod
    (fun i _ => (channel_resources right).nonnegative _ _)
    (fun i _ => channel_point_bound right (a i) (x i))

theorem inputColumn_zero_of_inactive (right : Orientation) (a x : Word)
    (i : Fin 4) (ha : a i = 0) (hx : x i ≠ 0) :
    inputColumn right a x = 0 := by
  rw [inputColumn_eq_product]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [ha, (channel_resources right).zero_column, if_neg hx]

theorem inputColumn_zero_of_active (right : Orientation) (a x : Word)
    (i : Fin 4) (ha : a i ≠ 0) (hx : x i = 0) :
    inputColumn right a x = 0 := by
  rw [inputColumn_eq_product]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [hx, (channel_resources right).zero_row, if_neg ha]

/-- Nonzero source mass keeps precisely the original active positions. -/
theorem inputColumn_support (right : Orientation) (a x : Word)
    (hx : inputColumn right a x ≠ 0) (i : Fin 4) :
    a i = 0 ↔ x i = 0 := by
  constructor
  · intro ha
    by_contra hi
    exact hx (inputColumn_zero_of_inactive right a x i ha hi)
  · intro hi
    by_contra ha
    exact hx (inputColumn_zero_of_active right a x i ha hi)

/-- The actual middle-variable reindexing keeps diffusion inside the response. -/
theorem actual_word_column_response (left right : Orientation) (inverse : Bool) (a : Word) :
    (fun y => wordKernel left right inverse y a) =
      tensorResponse (fun _ : Fin 4 => channel left)
        (byteDiffusionOrientation inverse) (inputColumn right a) := by
  funext y
  let L := byteDiffusionOrientation inverse
  change (∑ z : Word, substitutionKernel (channel left) y z *
      substitutionKernel (channel right) (L.symm z) a) =
    ∑ x : Word, substitutionKernel (channel left) y (L x) *
      substitutionKernel (channel right) x a
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp L (fun z => substitutionKernel (channel left) y z *
      substitutionKernel (channel right) (L.symm z) a)).symm

theorem actual_word_column_gram (left right : Orientation) (inverse : Bool) (a : Word) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) =
      ∑ x : Word, ∑ z : Word, inputColumn right a x*inputColumn right a z*
        ∏ i : Fin 4, gram (channel left)
          (byteDiffusionOrientation inverse x i) (byteDiffusionOrientation inverse z i) := by
  have h := tensorResponse_energy (fun _ : Fin 4 => channel left)
    (byteDiffusionOrientation inverse) (inputColumn right a)
  rw [← actual_word_column_response left right inverse a] at h
  exact h

/-- One source byte in its physical input position. -/
def singleByteWord (k : Fin 4) (t : Byte) : Word :=
  fun i => if i = k then t else 0

theorem singleByteWord_injective (k : Fin 4) : Function.Injective (singleByteWord k) := by
  intro t u h
  have hk := congrFun h k
  simpa [singleByteWord] using hk

theorem inputColumn_single_active (right : Orientation) (a : Word) (k : Fin 4)
    (hsupport : ∀ i, i ≠ k → a i = 0) (t : Byte) :
    inputColumn right a (singleByteWord k t) = channel right t (a k) := by
  rw [inputColumn_eq_product]
  calc
    _ = ∏ i : Fin 4, if i = k then channel right t (a k) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = k
      · subst i
        simp [singleByteWord]
      · simp [singleByteWord, hi, hsupport i hi, (channel_resources right).zero_column]
    _ = _ := by simp

private theorem inputColumn_zero_outside_single (right : Orientation) (a : Word) (k : Fin 4)
    (hsupport : ∀ i, i ≠ k → a i = 0) (x : Word)
    (hx : x ∉ Finset.univ.image (singleByteWord k)) :
    inputColumn right a x = 0 := by
  by_contra hmu
  have he : singleByteWord k (x k) = x := by
    funext i
    by_cases hi : i = k
    · subst i
      simp [singleByteWord]
    · have hxi : x i = 0 := (inputColumn_support right a x hmu i).mp (hsupport i hi)
      simp [singleByteWord, hi, hxi]
  exact hx (Finset.mem_image.mpr ⟨x k, Finset.mem_univ _, he⟩)

private theorem sum_supported_embedding {X Z : Type*}
    [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    (e : Z → X) (he : Function.Injective e) (f : X → ℝ)
    (hz : ∀ x, x ∉ Finset.univ.image e → f x = 0) :
    (∑ x : X, f x) = ∑ z : Z, f (e z) := by
  calc
    _ = ∑ x ∈ Finset.univ.image e, f x := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hz x hx)
    _ = _ := Finset.sum_image (fun x _ y _ hxy => he hxy)

/-- A single-active column is a weighted response to one common source byte.
No equality or scalar relation between the four output coordinate maps is used. -/
theorem actual_single_active_response (left right : Orientation) (inverse : Bool)
    (a : Word) (k : Fin 4) (hsupport : ∀ i, i ≠ k → a i = 0) :
    (fun y => wordKernel left right inverse y a) =
      tensorResponse (fun _ : Fin 4 => channel left)
        (fun t => byteDiffusionOrientation inverse (singleByteWord k t))
        (fun t => channel right t (a k)) := by
  funext y
  calc
    _ = ∑ x : Word, tensorColumn (fun _ : Fin 4 => channel left)
        (byteDiffusionOrientation inverse) y x * inputColumn right a x :=
      congrFun (actual_word_column_response left right inverse a) y
    _ = ∑ t : Byte, tensorColumn (fun _ : Fin 4 => channel left)
        (byteDiffusionOrientation inverse) y (singleByteWord k t) *
          inputColumn right a (singleByteWord k t) := by
      apply sum_supported_embedding (singleByteWord k) (singleByteWord_injective k)
      intro x hx
      rw [inputColumn_zero_outside_single right a k hsupport x hx, mul_zero]
    _ = _ := by
      simp only [inputColumn_single_active right a k hsupport, tensorResponse, tensorColumn]

theorem actual_single_active_column_gram (left right : Orientation) (inverse : Bool)
    (a : Word) (k : Fin 4) (hsupport : ∀ i, i ≠ k → a i = 0) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) =
      ∑ t : Byte, ∑ u : Byte, channel right t (a k)*channel right u (a k)*
        ∏ i : Fin 4, gram (channel left)
          (byteDiffusionOrientation inverse (singleByteWord k t) i)
          (byteDiffusionOrientation inverse (singleByteWord k u) i) := by
  have h := tensorResponse_energy (fun _ : Fin 4 => channel left)
    (fun t => byteDiffusionOrientation inverse (singleByteWord k t))
    (fun t => channel right t (a k))
  rw [← actual_single_active_response left right inverse a k hsupport] at h
  exact h

/-- The actual nonzero source law has no discarded mass at the zero label. -/
theorem actual_single_active_nonzero_column_gram (left right : Orientation) (inverse : Bool)
    (a : Word) (k : Fin 4) (hsupport : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) :
    (∑ y : Word, wordKernel left right inverse y a ^ 2) =
      ∑ t : NonzeroByte, ∑ u : NonzeroByte,
        channel right t.val (a k)*channel right u.val (a k)*
          ∏ i : Fin 4, gram (channel left)
            (byteDiffusionOrientation inverse (singleByteWord k t.val) i)
            (byteDiffusionOrientation inverse (singleByteWord k u.val) i) := by
  rw [actual_single_active_column_gram left right inverse a k hsupport]
  have hz : channel right 0 (a k) = 0 := by
    rw [(channel_resources right).zero_row, if_neg ha]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : Byte)]
  simp only [hz, zero_mul, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : Byte)]
  simp only [hz, mul_zero, zero_mul, zero_add]

end AESConcrete.WordColumnGram
