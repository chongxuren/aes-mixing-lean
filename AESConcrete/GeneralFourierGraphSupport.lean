import AESConcrete.FourierGraphSupport
import AESConcrete.GeneralMDSGraphSupport

/-!
# Fourier graph support for an arbitrary invariant coordinate mask

Product-character
algebra is separated from MDS support geometry and from the actual AES word
specializations. Every source function is an arbitrary signed joint function;
translation invariance is the complete source premise. No independence,
positivity, normalization, tensor factorization or dual-diffusion premise is
introduced.

Constructive mathematics only: no attacks or workloads. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct pairs,
and the 10/14/16 target remain fixed. This new source changes no accepted root,
manuscript, historical source, goal or schedule. Energy and physical step caps
are separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.GeneralFourierGraphSupport
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates splitMask joinMask)

variable {V : Type*}

section ProductPairing
variable [AddCommGroup V]

/-- A frequency extended by zero contributes only its mask's character
factors. The coordinate labels are retained in the restricted pairing. -/
theorem product_pairing_extend_left
    (B : CharacterPairing V) (D : Fin 16) (a : MaskCoordinates D → V)
    (x : Fin 4 → V) :
    (B.product (Fin 4)).value (extendCoordinates D a) x =
      (B.product (MaskCoordinates D)).value a (restrictCoordinates D x) := by
  classical
  change (∏ i : Fin 4, B.value (extendCoordinates D a i) (x i)) =
    ∏ i : MaskCoordinates D, B.value (a i) (restrictCoordinates D x i)
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : Fin 4 => maskBit D i = true)]
  have hp : (∏ i : MaskCoordinates D,
      B.value (extendCoordinates D a i.val) (x i.val)) =
      ∏ i : MaskCoordinates D, B.value (a i) (x i.val) := by
    apply Finset.prod_congr rfl
    intro i _
    simp [extendCoordinates, i.property]
  have hn : (∏ i : OtherCoordinates D,
      B.value (extendCoordinates D a i.val) (x i.val)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [extendCoordinates, i.property, B.zero_left]
  simp only [hp, hn, mul_one, restrictCoordinates]

/-- Full product characters equal the restricted product character whenever
the left argument is supported on the mask. No exponent-two premise is needed
for this purely algebraic identity. -/
theorem product_pairing_supported_left
    (B : CharacterPairing V) (D : Fin 16) (η x : Fin 4 → V)
    (hsupport : maskProjection D η = η) :
    (B.product (Fin 4)).value η x =
      (B.product (MaskCoordinates D)).value
        (restrictCoordinates D η) (restrictCoordinates D x) := by
  classical
  have hext : extendCoordinates D (restrictCoordinates D η) = η := by
    funext i
    by_cases hi : maskBit D i = true
    · simp [extendCoordinates, restrictCoordinates, hi]
    · have hz : η i = 0 := by
        have hh := congrFun hsupport i
        simpa [maskProjection, hi] using hh.symm
      simp [extendCoordinates, hi, hz]
  calc
    (B.product (Fin 4)).value η x =
        (B.product (Fin 4)).value
          (extendCoordinates D (restrictCoordinates D η)) x := by rw [hext]
    _ = _ := product_pairing_extend_left B D (restrictCoordinates D η) x

end ProductPairing

section Support
variable [AddCommGroup V] [Fintype V]

/-- Invariance under the entire input mask makes complement-`D` projection
injective on Fourier support after inverse pullback by the actual MDS map.
The masks have equal size; none of their individual coordinates is singled
out or assumed independent of the others. -/
theorem uniform_pullback_fourier_support_injective
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (U D : Fin 16) (hsize : maskSize D = maskSize U)
    (f : (Fin 4 → V) → ℝ)
    (hinv : ∀ (x : Fin 4 → V) (t : MaskCoordinates U → V),
      f (x + extendCoordinates U t) = f x)
    (z z' : Fin 4 → V)
    (hz : action (coordinateKernel (fun _ : Fin 4 => pairingFourier B))
      (fun x => f (L.symm x)) z ≠ 0)
    (hz' : action (coordinateKernel (fun _ : Fin 4 => pairingFourier B))
      (fun x => f (L.symm x)) z' ≠ 0)
    (heq : restrictCoordinates (maskComplement D) z =
      restrictCoordinates (maskComplement D) z') : z = z' := by
  classical
  have hzF : action (pairingFourier (B.product (Fin 4)))
      (fun x => f (L.symm x)) z ≠ 0 := by
    simpa only [productPairing_fourier] using hz
  have hzF' : action (pairingFourier (B.product (Fin 4)))
      (fun x => f (L.symm x)) z' ≠ 0 := by
    simpa only [productPairing_fourier] using hz'
  have hg (t : MaskCoordinates U → V) (x : Fin 4 → V) :
      f (L.symm (x + L (extendCoordinates U t))) = f (L.symm x) := by
    rw [map_add, L.symm_apply_apply]
    exact hinv (L.symm x) t
  -- Exponent two converts agreement off D into support of the sum on D.
  have hs : maskProjection D (z + z') = z + z' := by
    funext i
    by_cases hi : maskBit D i = true
    · simp [maskProjection, hi]
    · have hc : maskBit (maskComplement D) i = true := by
        rw [maskComplement_bit]
        cases hb : maskBit D i <;> simp_all
      have he := congrFun heq (⟨i, hc⟩ : MaskCoordinates (maskComplement D))
      change z i = z' i at he
      simp [maskProjection, hi, he, hchar]
  have hpair (a : MaskCoordinates D → V) :
      (B.product (MaskCoordinates D)).value (restrictCoordinates D (z + z')) a = 1 := by
    obtain ⟨t, ht⟩ :=
      (mds_restricted_bijective L.toAddMonoidHom hL D U hsize).2 a
    change restrictCoordinates D (L (extendCoordinates U t)) = a at ht
    have hz1 := FourierGraphSupport.pairingFourier_nonzero_annihilates_translation
      (B.product (Fin 4)) (fun x => f (L.symm x))
      (L (extendCoordinates U t)) (hg t) z hzF
    have hz2 := FourierGraphSupport.pairingFourier_nonzero_annihilates_translation
      (B.product (Fin 4)) (fun x => f (L.symm x))
      (L (extendCoordinates U t)) (hg t) z' hzF'
    have hh : (B.product (Fin 4)).value (z + z') (L (extendCoordinates U t)) = 1 := by
      rw [CharacterPairing.add_left, hz1, hz2, one_mul]
    rw [product_pairing_supported_left B D (z + z') (L (extendCoordinates U t)) hs,
      ht] at hh
    exact hh
  have hzero : restrictCoordinates D (z + z') = 0 := by
    by_contra hzero
    obtain ⟨a, ha⟩ := (B.product (MaskCoordinates D)).nondegenerate
      (restrictCoordinates D (z + z')) hzero
    exact ha (hpair a)
  have hsum : z + z' = 0 := by
    funext i
    by_cases hi : maskBit D i = true
    · have he := congrFun hzero (⟨i, hi⟩ : MaskCoordinates D)
      exact he
    · have he := congrFun hs i
      simpa [maskProjection, hi] using he.symm
  have hp : z' + z' = 0 := by
    funext i
    exact hchar (z' i)
  calc
    z = z + (z' + z') := by rw [hp, add_zero]
    _ = z' := by rw [← add_assoc, hsum, zero_add]

/-- The arbitrary-mask Fourier support injection in the grouped graph API.
All dependent coordinates are one tuple, and empty fibers are permitted.
The free mask is the complement of `D`. -/
theorem uniform_pullback_fourier_fiber_unique
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (U D : Fin 16) (hsize : maskSize D = maskSize U)
    (f : (Fin 4 → V) → ℝ)
    (hinv : ∀ (x : Fin 4 → V) (t : MaskCoordinates U → V),
      f (x + extendCoordinates U t) = f x) :
    ∀ (w : MaskCoordinates (maskComplement D) → V)
      (v v' : OtherCoordinates (maskComplement D) → V),
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B))
        (fun z => f (L.symm z)) ((splitMask (maskComplement D)).symm (v, w)) ≠ 0 →
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B))
        (fun z => f (L.symm z)) ((splitMask (maskComplement D)).symm (v', w)) ≠ 0 →
      v = v' := by
  intro w v v' hv hv'
  have he : (splitMask (maskComplement D)).symm (v, w) =
      (splitMask (maskComplement D)).symm (v', w) := by
    apply uniform_pullback_fourier_support_injective B hchar L hL U D hsize f hinv
      _ _ hv hv'
    funext i
    simp [restrictCoordinates, splitMask, joinMask, i.property]
  have hp := congrArg (splitMask (maskComplement D)) he
  have hvv : (v, w) = (v', w) := by
    simpa only [Equiv.apply_symm_apply] using hp
  exact congrArg Prod.fst hvv

end Support

/-- Actual word-pairing support injection through physical outer diffusion.
The invariant source remains an arbitrary signed joint state function. -/
theorem word_uniform_pullback_fourier_support_injective
    (U D : Fin 16) (hsize : maskSize D = maskSize U)
    (f : AES.WordState → ℝ)
    (hinv : ∀ (x : AES.WordState) (t : MaskCoordinates U → AES.Word),
      f (x + extendCoordinates U t) = f x)
    (z z' : AES.WordState)
    (hz : action (coordinateKernel (fun _ : Fin 4 => WordFourierCore.wordFourier))
      (fun x => f (WordCrossZero.wordMixAddEquiv.symm x)) z ≠ 0)
    (hz' : action (coordinateKernel (fun _ : Fin 4 => WordFourierCore.wordFourier))
      (fun x => f (WordCrossZero.wordMixAddEquiv.symm x)) z' ≠ 0)
    (heq : restrictCoordinates (maskComplement D) z =
      restrictCoordinates (maskComplement D) z') : z = z' :=
  uniform_pullback_fourier_support_injective WordFourierCore.wordPairing word_add_self
    WordCrossZero.wordMixAddEquiv WordCrossZero.wordMixAddEquiv_zeroMDS
    U D hsize f hinv z z' hz hz' heq

/-- Actual word specialization of the grouped partial-graph support premise. -/
theorem word_uniform_pullback_fourier_fiber_unique
    (U D : Fin 16) (hsize : maskSize D = maskSize U)
    (f : AES.WordState → ℝ)
    (hinv : ∀ (x : AES.WordState) (t : MaskCoordinates U → AES.Word),
      f (x + extendCoordinates U t) = f x) :
    ∀ (w : MaskCoordinates (maskComplement D) → AES.Word)
      (v v' : OtherCoordinates (maskComplement D) → AES.Word),
      action (coordinateKernel (fun _ : Fin 4 => WordFourierCore.wordFourier))
        (fun z => f (WordCrossZero.wordMixAddEquiv.symm z))
        ((splitMask (maskComplement D)).symm (v, w)) ≠ 0 →
      action (coordinateKernel (fun _ : Fin 4 => WordFourierCore.wordFourier))
        (fun z => f (WordCrossZero.wordMixAddEquiv.symm z))
        ((splitMask (maskComplement D)).symm (v', w)) ≠ 0 → v = v' :=
  uniform_pullback_fourier_fiber_unique WordFourierCore.wordPairing word_add_self
    WordCrossZero.wordMixAddEquiv WordCrossZero.wordMixAddEquiv_zeroMDS
    U D hsize f hinv

end AESConcrete.GeneralFourierGraphSupport
