import AESConcrete.FourierGraphSupport
import AESConcrete.MDSGraphEnergy
import AESConcrete.WordFourierVariants

/-!
# Fourier graph energy for a full-uniform input coordinate

The Fourier transform below acts on the four outer word coordinates. Its
conjugation and counting-energy identities are derived from the product
character pairing, rather than from diffusion inside one word. The generic
graph estimate and actual AES specialization are separate interfaces. All
inputs may be signed and jointly correlated.

The final estimate assumes translation invariance in one input coordinate. It
does not decompose a nonzero-uniform leg, aggregate support pieces, or assert
the physical `(13,12)` step cap. Constructive scope only. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct pairs and
the 10/14/16 target stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FourierGraphEnergy
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.WordFourierCore

section ProductFourier
variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V]

/-- Product Fourier preserves counting energy on arbitrary joint inputs.
Here `I` is the outer coordinate index; no input tensor factorization is
assumed. -/
theorem coordinate_fourier_input_energy (B : CharacterPairing V)
    (hchar : ∀ x : V, x + x = 0) (f : (I → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : I => pairingFourier B)) f y ^ 2) =
      ∑ x, f x ^ 2 := by
  have hp : ∀ x : I → V, x + x = 0 := by
    intro x
    funext i
    exact hchar (x i)
  rw [← productPairing_fourier]
  exact pairingFourier_energy (B.product I) hp f

/-- Conjugate every outer-coordinate kernel and Fourier transform its
joint input. The resulting energy is exactly the original tensor energy.
This is a two-sided conjugation identity, not a one-sided mixed matrix
estimate. -/
theorem coordinate_fourier_conjugation_energy (B : CharacterPairing V)
    (hchar : ∀ x : V, x + x = 0) (T : V → V → ℝ)
    (f : (I → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : I => fourierConjugate B T))
      (action (coordinateKernel (fun _ : I => pairingFourier B)) f) y ^ 2) =
      ∑ y, action (coordinateKernel (fun _ : I => T)) f y ^ 2 := by
  have hp : ∀ x : I → V, x + x = 0 := by
    intro x
    funext i
    exact hchar (x i)
  have he := fourierConjugate_energy (B.product I) hp
    (coordinateKernel (fun _ : I => T)) f
  rw [coordinate_fourierConjugate, productPairing_fourier] at he
  exact he

end ProductFourier

section GraphEnergy
variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- The Fourier support graph supplies one column cap, with only three
operator factors. Both caps concern the actual two-sided conjugate kernel.
The support condition is separate from the energy algebra. -/
theorem coordinate_fourier_partial_graph_energy (B : CharacterPairing V)
    (hchar : ∀ x : V, x + x = 0) (T : V → V → ℝ)
    (s : Fin 4) (ρ c : ℝ)
    (hT : ∀ h : V → ℝ,
      (∑ y, action (fourierConjugate B T) h y ^ 2) ≤
        ρ ^ 2 * ∑ x, h x ^ 2)
    (hcolumn : ∀ v, (∑ y, fourierConjugate B T y v ^ 2) ≤ c ^ 2)
    (f : (Fin 4 → V) → ℝ)
    (hgraph : ∀ (w : Fin 3 → V) (v v' : V),
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B)) f
        (Fin.insertNth s v w) ≠ 0 →
      action (coordinateKernel (fun _ : Fin 4 => pairingFourier B)) f
        (Fin.insertNth s v' w) ≠ 0 → v = v') :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => T)) f y ^ 2) ≤
      ρ ^ 6 * c ^ 2 * ∑ x, f x ^ 2 := by
  have he := MDSGraphEnergy.coordinate_partial_graph_energy
    (fun _ : Fin 4 => fourierConjugate B T) s (fun _ : Fin 3 => ρ) c
    (fun _ => hT) hcolumn
    (action (coordinateKernel (fun _ : Fin 4 => pairingFourier B)) f) hgraph
  have hp : (∏ _ : Fin 3, ρ) ^ 2 = ρ ^ 6 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hp, coordinate_fourier_conjugation_energy B hchar T f,
    coordinate_fourier_input_energy B hchar f] at he
  exact he

end GraphEnergy

-- These are four-word specializations. `wordPairing` pairs the bytes inside
-- one word; its product here pairs the four physical outer state words.

theorem wordState_fourier_energy (f : AES.WordState → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => wordFourier)) f y ^ 2) =
      ∑ x, f x ^ 2 :=
  coordinate_fourier_input_energy WordFourierCore.wordPairing word_add_self f

/-- Exact outer four-word residual-conjugation energy identity for any
word kernel and any joint state function. -/
theorem wordState_fourier_conjugation_energy
    (T : AES.Word → AES.Word → ℝ) (f : AES.WordState → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => wordConjugate T))
      (action (coordinateKernel (fun _ : Fin 4 => wordFourier)) f) y ^ 2) =
      ∑ y, action (coordinateKernel (fun _ : Fin 4 => T)) f y ^ 2 :=
  coordinate_fourier_conjugation_energy WordFourierCore.wordPairing word_add_self T f

-- Actual numerical resource boundary: the operator and all-column caps
-- are for F R F. The input support theorem uses physical outer wordMix.

/-- Actual residual tensor after inverse-pullback through physical word
diffusion, for an input invariant under every translation in coordinate
`r`. The other three input coordinates may be arbitrarily correlated. -/
theorem word_residual_uniform_coordinate_energy
    (r s : Fin 4) (f : AES.WordState → ℝ)
    (hinv : ∀ (x : AES.WordState) (t : AES.Word),
      f (x + Pi.single r t) = f x) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 =>
      residualMatrix AES.wordSuperboxKernel 0))
      (fun z => f (WordCrossZero.wordMixAddEquiv.symm z)) y ^ 2) ≤
      (21 / 131072 : ℝ) ^ 6 * (2 / (15 * 4294967296) : ℝ) * ∑ x, f x ^ 2 := by
  have hc : (Real.sqrt (2 / (15 * 4294967296) : ℝ)) ^ 2 =
      (2 / (15 * 4294967296) : ℝ) := Real.sq_sqrt (by norm_num)
  have hT : ∀ h : AES.Word → ℝ,
      (∑ y, action (wordConjugate (residualMatrix AES.wordSuperboxKernel 0)) h y ^ 2) ≤
        (21 / 131072 : ℝ) ^ 2 * ∑ x, h x ^ 2 :=
    WordFourierBounds.fourier_residual_energy_le .ordinary .ordinary false
  have hcolumn : ∀ v : AES.Word,
      (∑ y, wordConjugate (residualMatrix AES.wordSuperboxKernel 0) y v ^ 2) ≤
        (Real.sqrt (2 / (15 * 4294967296) : ℝ)) ^ 2 := by
    intro v
    rw [hc]
    exact le_of_lt (WordFourierVariants.variant_column_energy_lt false true v)
  have he := coordinate_fourier_partial_graph_energy WordFourierCore.wordPairing word_add_self
    (residualMatrix AES.wordSuperboxKernel 0) s
    (21 / 131072 : ℝ) (Real.sqrt (2 / (15 * 4294967296) : ℝ))
    hT hcolumn (fun z => f (WordCrossZero.wordMixAddEquiv.symm z))
    (FourierGraphSupport.word_uniform_pullback_fourier_fiber_unique r s f hinv)
  have hn : (∑ z, f (WordCrossZero.wordMixAddEquiv.symm z) ^ 2) = ∑ x, f x ^ 2 :=
    WordCrossZero.wordMixAddEquiv.symm.toEquiv.sum_comp (fun x => f x ^ 2)
  rw [hc, hn] at he
  exact he

end AESConcrete.FourierGraphEnergy
