import AESConcrete.GeneralMDSGraphSupport
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import AESMixing.Product

/-!
# MDS graph energy with any number of active coordinates

The dependent coordinates form one tuple-valued graph factor. Its column
energy is a product of genuine column energies; the free coordinates receive
the finite tensor operator estimate on an arbitrary joint signed function. The
graph relation never asserts independence or coordinatewise dependence.

Kernel reindexing, conditional energy, MDS geometry and actual resources
remain distinct statements. Independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct pairs stay fixed. This module does not establish the full AES 10/14/16 theorem.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.GeneralMDSGraphEnergy
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.GeneralMDSGraphSupport

variable {V : Type*}

/-- Split the entire dependent tuple from the selected information set. -/
theorem coordinateKernel_splitMask (T : Fin 4 → V → V → ℝ) (m : Fin 16) :
    coordinateKernel T = reindexKernel (splitMask m)
      (tensorKernel
        (coordinateKernel (fun i : OtherCoordinates m => T i.val))
        (coordinateKernel (fun i : MaskCoordinates m => T i.val))) := by
  funext y x
  change (∏ i : Fin 4, T i (y i) (x i)) =
    (∏ i : OtherCoordinates m, T i.val (y i.val) (x i.val)) *
      ∏ i : MaskCoordinates m, T i.val (y i.val) (x i.val)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin 4 => AES.maskBit m i = true)]
  exact mul_comm _ _

section ConditionalEnergy
variable [Fintype V] [Nonempty V]

/-- Any `b` coordinates receive operator bounds, and the remaining `4-b`
coordinates receive column bounds. All dependent coordinates are allowed
to depend jointly on the entire free tuple. -/
theorem coordinate_partial_graph_energy
    (T : Fin 4 → V → V → ℝ) (m : Fin 16) (ρ κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ i (f : V → ℝ),
      (∑ y, action (T i) f y ^ 2) ≤ ρ ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ i v, (∑ y, T i y v ^ 2) ≤ κ)
    (f : (Fin 4 → V) → ℝ)
    (hgraph : ∀ (w : MaskCoordinates m → V) (v v' : OtherCoordinates m → V),
      f ((splitMask m).symm (v, w)) ≠ 0 →
      f ((splitMask m).symm (v', w)) ≠ 0 → v = v') :
    (∑ y, action (coordinateKernel T) f y ^ 2) ≤
      ρ ^ (2 * maskSize m) * κ ^ (4 - maskSize m) * ∑ x, f x ^ 2 := by
  let e := splitMask (V := V) m
  let B := coordinateKernel (fun i : OtherCoordinates m => T i.val)
  let A := coordinateKernel (fun i : MaskCoordinates m => T i.val)
  let a : ℝ := ∏ _ : MaskCoordinates m, ρ
  let c : ℝ := Real.sqrt (κ ^ Fintype.card (OtherCoordinates m))
  have hc : c ^ 2 = κ ^ Fintype.card (OtherCoordinates m) :=
    Real.sq_sqrt (pow_nonneg hκ _)
  have hA : ∀ g : (MaskCoordinates m → V) → ℝ,
      (∑ y, action A g y ^ 2) ≤ a ^ 2 * ∑ x, g x ^ 2 :=
    FiniteTensorEnergy.coordinate_energy
      (fun i : MaskCoordinates m => T i.val) (fun _ => ρ)
      (fun i => hT i.val)
  have hB : ∀ v : OtherCoordinates m → V,
      (∑ y, B y v ^ 2) ≤ c ^ 2 := by
    intro v
    rw [hc]
    exact product_column_energy_le (fun i y => T i.val y (v i)) κ
      (fun i => hcolumn i.val (v i))
  have hfiber : ∀ (w : MaskCoordinates m → V) (v v' : OtherCoordinates m → V),
      (f ∘ e.symm) (v, w) ≠ 0 → (f ∘ e.symm) (v', w) ≠ 0 → v = v' := hgraph
  have he := GraphColumnEnergy.tensor_partial_graph_energy B A a c hA hB
    (f ∘ e.symm) hfiber
  have hn : (∑ x, (f ∘ e.symm) x ^ 2) = ∑ x, f x ^ 2 :=
    e.symm.sum_comp (fun x => f x ^ 2)
  have ha : a ^ 2 = ρ ^ (2 * maskSize m) := by
    simp only [a, Finset.prod_const, Finset.card_univ, maskCoordinates_card]
    rw [← pow_mul, Nat.mul_comm]
  rw [hn, ha, hc, otherCoordinates_card] at he
  rw [coordinateKernel_splitMask T m]
  simp_rw [reindexKernel_action]
  rw [e.sum_comp (fun y => action (tensorKernel B A) (f ∘ e.symm) y ^ 2)]
  exact he

end ConditionalEnergy

section MDSEnergy
variable [AddCommGroup V] [Fintype V]

/-- Any equal-size MDS restriction supplies the conditional graph premise.
Diffusion preserves counting energy exactly. -/
theorem coordinate_supported_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (inp out : Fin 16) (hsize : maskSize out = maskSize inp)
    (T : Fin 4 → V → V → ℝ) (ρ κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ i (f : V → ℝ),
      (∑ y, action (T i) f y ^ 2) ≤ ρ ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ i v, (∑ y, T i y v ^ 2) ≤ κ)
    (f : (Fin 4 → V) → ℝ)
    (hsupport : ∀ x, f x ≠ 0 → maskProjection inp x = x) :
    (∑ y, action (coordinateKernel T) (fun z => f (L.symm z)) y ^ 2) ≤
      ρ ^ (2 * maskSize out) * κ ^ (4 - maskSize out) * ∑ x, f x ^ 2 := by
  letI : Nonempty V := ⟨0⟩
  have he := coordinate_partial_graph_energy T out ρ κ hκ hT hcolumn
    (fun z => f (L.symm z))
    (pullback_fiber_unique L hL inp out hsize f hsupport)
  have hn : (∑ z, f (L.symm z) ^ 2) = ∑ x, f x ^ 2 :=
    L.symm.toEquiv.sum_comp (fun x => f x ^ 2)
  rw [hn] at he
  exact he

end MDSEnergy

section ExactSupport
variable [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- One selected source piece with active count `b`. Selecting the same
coordinate labels on output gives an equal-size MDS information set. -/
theorem coordinate_support_piece_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (T : Fin 4 → V → V → ℝ) (ρ κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ i (f : V → ℝ),
      (∑ y, action (T i) f y ^ 2) ≤ ρ ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ i v, (∑ y, T i y v ^ 2) ≤ κ)
    {d : ℕ} (p : SupportIndex d) (b : Fin 5)
    (hb : maskSize p.val.2 + b.val = 4) (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (coordinateKernel T)
      (fun z => supportIndexComponent (0 : V) p f (L.symm z)) y ^ 2) ≤
      ρ ^ (2 * b.val) * κ ^ (4 - b.val) *
        ∑ x, supportIndexComponent (0 : V) p f x ^ 2 := by
  have hs : maskSize (maskComplement p.val.2) = b.val := by
    rw [maskComplement_size]
    omega
  have he := coordinate_supported_energy L hL
    (maskComplement p.val.2) (maskComplement p.val.2) rfl T ρ κ hκ hT hcolumn
    (supportIndexComponent (0 : V) p f) (supportIndexComponent_supported p f)
  rw [hs] at he
  exact he

end ExactSupport

/-- Actual ordinary word residual resources, with arbitrary active count.
The coefficient is kept in energy form, with natural exponents throughout. -/
theorem word_residual_support_piece_energy {d : ℕ}
    (p : SupportIndex d) (b : Fin 5)
    (hb : AES.maskSize p.val.2 + b.val = 4) (f : AES.WordState → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 =>
      residualMatrix AES.wordSuperboxKernel 0))
      (fun z => supportIndexComponent (0 : AES.Word) p f
        (WordCrossZero.wordMixAddEquiv.symm z)) y ^ 2) ≤
      (21 / 131072 : ℝ) ^ (2 * b.val) *
        (2 / (15 * 4294967296) : ℝ) ^ (4 - b.val) *
        ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 :=
  coordinate_support_piece_energy WordCrossZero.wordMixAddEquiv
    WordCrossZero.wordMixAddEquiv_zeroMDS
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    (21 / 131072 : ℝ) (2 / (15 * 4294967296) : ℝ) (by norm_num)
    (fun _ => SharpDampedWordNorm.word_superbox_residual_energy)
    (fun _ v => le_of_lt (AllColumnBound.actual_word_residual_column_energy_lt v))
    p b hb f

end AESConcrete.GeneralMDSGraphEnergy
