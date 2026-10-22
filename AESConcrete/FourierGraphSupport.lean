import AESConcrete.MDSGraphSupport
import AESConcrete.WordFourierCore

/-!
# Fourier partial-graph support from one invariant input coordinate

Candidate extension, outside the current DirectIncidence root and audit.
Finite Fourier translation covariance forces every nonzero coefficient to
annihilate every translation preserving the input. Singleton MDS coordinate
surjectivity then separates two supported frequencies agreeing off one
coordinate. The actual specialization uses the product of the actual word
pairings and the physical `wordMixAddEquiv`, without an outer dual-map premise.

The input is an arbitrary signed joint function invariant under translation
in one coordinate. Its remaining three coordinates may be correlated. No
normalization, tensor factorization, positivity, energy estimate, physical
step cap or return bound is assumed or asserted here.

Constructive mathematics only: no attacks or workloads. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct pairs,
and the 10/14/16 target remain fixed. No accepted root, manuscript, historical
source, goals or schedules are changed by this candidate module.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FourierGraphSupport
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

section Translation
variable {X : Type*} [AddCommGroup X] [Fintype X]

/-- Reindex the exact normalized finite Fourier sum by `x ↦ x + h`.
The normalization is unchanged; this identity needs no exponent-two premise. -/
theorem pairingFourier_translation_covariance
    (B : CharacterPairing X) (f : X → ℝ) (h y : X) :
    action (pairingFourier B) f y =
      B.value y h * action (pairingFourier B) (fun x => f (x + h)) y := by
  classical
  have he := Equiv.sum_comp (Equiv.addRight h)
    (fun x : X => pairingFourier B y x * f x)
  change (∑ x, pairingFourier B y (x + h) * f (x + h)) =
    ∑ x, pairingFourier B y x * f x at he
  calc
    action (pairingFourier B) f y =
        ∑ x, pairingFourier B y (x + h) * f (x + h) := he.symm
    _ = ∑ x, B.value y h * (pairingFourier B y x * f (x + h)) := by
      apply Finset.sum_congr rfl
      intro x _
      unfold pairingFourier
      rw [B.add_right]
      ring
    _ = B.value y h * action (pairingFourier B) (fun x => f (x + h)) y := by
      simp only [action, Finset.mul_sum]

/-- Every nonzero Fourier coefficient annihilates a translation fixing the
function. This applies to signed functions with arbitrary joint dependence. -/
theorem pairingFourier_nonzero_annihilates_translation
    (B : CharacterPairing X) (f : X → ℝ) (h : X)
    (hinv : ∀ x, f (x + h) = f x) (y : X)
    (hy : action (pairingFourier B) f y ≠ 0) : B.value y h = 1 := by
  have he := pairingFourier_translation_covariance B f h y
  have hf : (fun x => f (x + h)) = f := funext hinv
  rw [hf] at he
  have hp : (B.value y h - 1) * action (pairingFourier B) f y = 0 := by
    nlinarith [he]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hy)

end Translation

section SingletonMDS
variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- The actual `(1,1)` MDS restriction makes each output coordinate a
surjective function of any single input coordinate. This unwraps the existing
restricted-map bijection rather than assuming a matrix-entry inverse. -/
theorem mds_singleton_coordinate_surjective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r s : Fin 4) :
    Function.Surjective (fun t : V => L (Pi.single r t) s) := by
  classical
  have hr : maskBit (singletonMask r) r = true :=
    (singletonMask_bit r r).mpr rfl
  have hs : maskBit (singletonMask s) s = true :=
    (singletonMask_bit s s).mpr rfl
  intro a
  obtain ⟨x, hx⟩ :=
    (mds_restricted_bijective L hL (singletonMask s) (singletonMask r)
      (by rw [singletonMask_size, singletonMask_size])).2 (fun _ => a)
  have hext : extendCoordinates (singletonMask r) x =
      Pi.single r (x ⟨r, hr⟩) := by
    funext i
    by_cases hi : i = r
    · subst i
      simp [extendCoordinates, hr]
    · have hbit : maskBit (singletonMask r) i ≠ true := by
        intro hbit
        exact hi ((singletonMask_bit r i).mp hbit)
      simp [extendCoordinates, hbit, hi]
  have ha := congrFun hx (⟨s, hs⟩ : MaskCoordinates (singletonMask s))
  change L (extendCoordinates (singletonMask r) x) s = a at ha
  rw [hext] at ha
  exact ⟨x ⟨r, hr⟩, ha⟩

end SingletonMDS

section ProductSupport
variable {V : Type*} [AddCommGroup V] [Fintype V]

omit [Fintype V] in
/-- A product character evaluated on a one-coordinate frequency has exactly
one nontrivial factor. -/
theorem product_pairing_single_left
    (B : CharacterPairing V) (s : Fin 4) (v : V) (x : Fin 4 → V) :
    (B.product (Fin 4)).value (Pi.single s v) x = B.value v (x s) := by
  classical
  change (∏ i : Fin 4, B.value ((Pi.single s v : Fin 4 → V) i) (x i)) = B.value v (x s)
  rw [Finset.prod_eq_single s]
  · simp
  · intro i _ hi
    simp [hi, B.zero_left]
  · simp

/-- Translation invariance in one input coordinate becomes uniqueness of any
one output frequency coordinate after inverse pullback by an MDS map. The
other coordinates remain arbitrary and jointly distributed. -/
theorem uniform_pullback_fourier_support_coordinate_eq
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (f : (Fin 4 → V) → ℝ)
    (hinv : ∀ (x : Fin 4 → V) (t : V), f (x + Pi.single r t) = f x)
    (z z' : Fin 4 → V)
    (hz : action (pairingFourier (B.product (Fin 4))) (fun x => f (L.symm x)) z ≠ 0)
    (hz' : action (pairingFourier (B.product (Fin 4))) (fun x => f (L.symm x)) z' ≠ 0)
    (heq : ∀ i, i ≠ s → z i = z' i) : z s = z' s := by
  classical
  have hg (t : V) (x : Fin 4 → V) :
      f (L.symm (x + L (Pi.single r t))) = f (L.symm x) := by
    rw [map_add, L.symm_apply_apply]
    exact hinv (L.symm x) t
  have hsingle : z + z' = Pi.single s (z s + z' s) := by
    funext i
    by_cases hi : i = s
    · subst i
      simp
    · simp only [Pi.add_apply, heq i hi, hchar, Pi.single_eq_of_ne hi]
  have hpair (a : V) : B.value (z s + z' s) a = 1 := by
    obtain ⟨t, ht⟩ := mds_singleton_coordinate_surjective L.toAddMonoidHom hL r s a
    change L (Pi.single r t) s = a at ht
    have hz1 := pairingFourier_nonzero_annihilates_translation
      (B.product (Fin 4)) (fun x => f (L.symm x)) (L (Pi.single r t)) (hg t) z hz
    have hz2 := pairingFourier_nonzero_annihilates_translation
      (B.product (Fin 4)) (fun x => f (L.symm x)) (L (Pi.single r t)) (hg t) z' hz'
    have hh : (B.product (Fin 4)).value (z + z') (L (Pi.single r t)) = 1 := by
      rw [CharacterPairing.add_left, hz1, hz2, one_mul]
    rw [hsingle, product_pairing_single_left, ht] at hh
    exact hh
  have hzero : z s + z' s = 0 := by
    by_contra hzero
    obtain ⟨a, ha⟩ := B.nondegenerate (z s + z' s) hzero
    exact ha (hpair a)
  calc
    z s = z s + (z' s + z' s) := by rw [hchar, add_zero]
    _ = z' s := by rw [← add_assoc, hzero, zero_add]

/-- The partial graph interface for the tensor of one-coordinate Fourier
kernels. Empty fibers are permitted; no graph-surjectivity assertion occurs. -/
theorem uniform_pullback_fourier_fiber_unique
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (f : (Fin 4 → V) → ℝ)
    (hinv : ∀ (x : Fin 4 → V) (t : V), f (x + Pi.single r t) = f x) :
    ∀ (w : Fin 3 → V) (v v' : V),
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B))
        (fun z => f (L.symm z)) (Fin.insertNth s v w) ≠ 0 →
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B))
        (fun z => f (L.symm z)) (Fin.insertNth s v' w) ≠ 0 → v = v' := by
  intro w v v' hv hv'
  have hz : action (pairingFourier (B.product (Fin 4)))
      (fun z => f (L.symm z)) (Fin.insertNth s v w) ≠ 0 := by
    simpa only [productPairing_fourier] using hv
  have hz' : action (pairingFourier (B.product (Fin 4)))
      (fun z => f (L.symm z)) (Fin.insertNth s v' w) ≠ 0 := by
    simpa only [productPairing_fourier] using hv'
  have heq : ∀ i : Fin 4, i ≠ s →
      (Fin.insertNth s v w : Fin 4 → V) i = (Fin.insertNth s v' w : Fin 4 → V) i := by
    intro i hi
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
    rw [← hj]
    simp
  simpa only [Fin.insertNth_apply_same] using
    uniform_pullback_fourier_support_coordinate_eq B hchar L hL r s f hinv
      (Fin.insertNth s v w) (Fin.insertNth s v' w) hz hz' heq

end ProductSupport

/-- Actual four-word Fourier partial graph, using the physical word diffusion
and the actual word trace pairing. Translation invariance is the complete
input premise; no assumption on the other three coordinates is introduced. -/
theorem word_uniform_pullback_fourier_fiber_unique
    (r s : Fin 4) (f : AES.WordState → ℝ)
    (hinv : ∀ (x : AES.WordState) (t : AES.Word), f (x + Pi.single r t) = f x) :
    ∀ (w : Fin 3 → AES.Word) (v v' : AES.Word),
      action (coordinateKernel (fun _ : Fin 4 => WordFourierCore.wordFourier))
        (fun z => f (WordCrossZero.wordMixAddEquiv.symm z))
        (Fin.insertNth s v w) ≠ 0 →
      action (coordinateKernel (fun _ : Fin 4 => WordFourierCore.wordFourier))
        (fun z => f (WordCrossZero.wordMixAddEquiv.symm z))
        (Fin.insertNth s v' w) ≠ 0 → v = v' :=
  uniform_pullback_fourier_fiber_unique WordFourierCore.wordPairing word_add_self
    WordCrossZero.wordMixAddEquiv WordCrossZero.wordMixAddEquiv_zeroMDS r s f hinv

end AESConcrete.FourierGraphSupport
