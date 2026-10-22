import AESConcrete.GeneralFourierGraphSupport
import AESConcrete.GeneralMDSGraphEnergy
import AESConcrete.FourierGraphEnergy

/-!
# Arbitrary-mask Fourier graph energy

The grouped graph
energy applies to all dependent Fourier coordinates at once. The two existing
outer-coordinate Fourier identities transfer its estimate back to the original
kernel. Geometry, energy algebra and actual word resources remain separate.
All functions may be signed and jointly correlated.

Constructive bounds only: no attacks, workloads, accepted/manuscript/historical
edits, goals or schedules. Independent uniform retained keys, whitening,
omitted final MixColumns, ordered-distinct pairs and the 10/14/16 target remain
fixed. No source extraction, subset expansion, aggregation, new physical step
cap, return cap or complete AES theorem is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.GeneralFourierGraphEnergy
set_option maxRecDepth 100000
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates splitMask)

section GraphEnergy
variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- Every dependent Fourier coordinate receives a genuine column-energy
bound. The entire complementary free tuple receives the joint tensor operator
estimate. Both resources concern the actual two-sided conjugate kernel. -/
theorem coordinate_fourier_partial_graph_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (T : V → V → ℝ) (D : Fin 16) (ρ κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ h : V → ℝ,
      (∑ y, action (fourierConjugate B T) h y ^ 2) ≤ ρ ^ 2 * ∑ x, h x ^ 2)
    (hcolumn : ∀ v, (∑ y, fourierConjugate B T y v ^ 2) ≤ κ)
    (f : (Fin 4 → V) → ℝ)
    (hgraph : ∀ (w : MaskCoordinates (maskComplement D) → V)
      (v v' : OtherCoordinates (maskComplement D) → V),
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B)) f
        ((splitMask (maskComplement D)).symm (v, w)) ≠ 0 →
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B)) f
        ((splitMask (maskComplement D)).symm (v', w)) ≠ 0 → v = v') :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => T)) f y ^ 2) ≤
      ρ ^ (2 * (4 - maskSize D)) * κ ^ maskSize D * ∑ x, f x ^ 2 := by
  letI : Nonempty V := ⟨0⟩
  have he := GeneralMDSGraphEnergy.coordinate_partial_graph_energy
    (fun _ : Fin 4 => fourierConjugate B T) (maskComplement D) ρ κ hκ
    (fun _ => hT) (fun _ => hcolumn)
    (action (coordinateKernel (fun _ : Fin 4 => pairingFourier B)) f) hgraph
  have hdep : 4 - maskSize (maskComplement D) = maskSize D := by
    rw [← maskComplement_size, maskComplement_involutive]
  rw [hdep, maskComplement_size,
    FourierGraphEnergy.coordinate_fourier_conjugation_energy B hchar T f,
    FourierGraphEnergy.coordinate_fourier_input_energy B hchar f] at he
  exact he

/-- The arbitrary invariant input mask supplies the Fourier graph premise
after physical inverse pullback. Equal-size MDS geometry is the only diffusion
condition, and diffusion preserves the input counting energy exactly. -/
theorem coordinate_uniform_pullback_fourier_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (U D : Fin 16) (hsize : maskSize D = maskSize U)
    (T : V → V → ℝ) (ρ κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ h : V → ℝ,
      (∑ y, action (fourierConjugate B T) h y ^ 2) ≤ ρ ^ 2 * ∑ x, h x ^ 2)
    (hcolumn : ∀ v, (∑ y, fourierConjugate B T y v ^ 2) ≤ κ)
    (f : (Fin 4 → V) → ℝ)
    (hinv : ∀ (x : Fin 4 → V) (t : MaskCoordinates U → V),
      f (x + extendCoordinates U t) = f x) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => T))
      (fun z => f (L.symm z)) y ^ 2) ≤
      ρ ^ (2 * (4 - maskSize D)) * κ ^ maskSize D * ∑ x, f x ^ 2 := by
  have he := coordinate_fourier_partial_graph_energy B hchar T D ρ κ hκ hT hcolumn
    (fun z => f (L.symm z))
    (GeneralFourierGraphSupport.uniform_pullback_fourier_fiber_unique
      B hchar L hL U D hsize f hinv)
  have hn : (∑ z, f (L.symm z) ^ 2) = ∑ x, f x ^ 2 :=
    L.symm.toEquiv.sum_comp (fun x => f x ^ 2)
  rw [hn] at he
  exact he

end GraphEnergy

-- Numerical resource boundary: 4294967296 is 2^32. Both resources below
-- are for F R F on a complete word, while the support geometry uses the
-- physical diffusion of the four outer words.

/-- Actual residual tensor through physical word diffusion, for any invariant
input mask and any equally sized output dependent mask. All remaining source
coordinates may be arbitrarily correlated. -/
theorem word_residual_uniform_mask_energy
    (U D : Fin 16) (hsize : maskSize D = maskSize U)
    (f : AES.WordState → ℝ)
    (hinv : ∀ (x : AES.WordState) (t : MaskCoordinates U → AES.Word),
      f (x + extendCoordinates U t) = f x) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 =>
      residualMatrix AES.wordSuperboxKernel 0))
      (fun z => f (WordCrossZero.wordMixAddEquiv.symm z)) y ^ 2) ≤
      (21 / 131072 : ℝ) ^ (2 * (4 - maskSize D)) *
        (2 / (15 * 4294967296) : ℝ) ^ maskSize D * ∑ x, f x ^ 2 := by
  have hT : ∀ h : AES.Word → ℝ,
      (∑ y, action (WordFourierCore.wordConjugate
        (residualMatrix AES.wordSuperboxKernel 0)) h y ^ 2) ≤
        (21 / 131072 : ℝ) ^ 2 * ∑ x, h x ^ 2 :=
    WordFourierBounds.fourier_residual_energy_le .ordinary .ordinary false
  have hcolumn : ∀ v : AES.Word,
      (∑ y, WordFourierCore.wordConjugate
        (residualMatrix AES.wordSuperboxKernel 0) y v ^ 2) ≤
        (2 / (15 * 4294967296) : ℝ) := by
    intro v
    exact le_of_lt (WordFourierVariants.variant_column_energy_lt false true v)
  exact coordinate_uniform_pullback_fourier_energy WordFourierCore.wordPairing word_add_self
    WordCrossZero.wordMixAddEquiv WordCrossZero.wordMixAddEquiv_zeroMDS
    U D hsize (residualMatrix AES.wordSuperboxKernel 0)
    (21 / 131072 : ℝ) (2 / (15 * 4294967296) : ℝ) (by norm_num)
    hT hcolumn f hinv

end AESConcrete.GeneralFourierGraphEnergy
