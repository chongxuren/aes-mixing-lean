import AESConcrete.MDSGraphSupport
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import Mathlib.Algebra.BigOperators.Fin

/-!
# Three operator factors and one column factor after MDS diffusion

The kernel reindexing, conditional graph-energy estimate, MDS support premise,
and actual numerical specialization are separate statements below. An input
function supported on one zero coordinate is arbitrary and may be signed or
correlated on all remaining coordinates.

The actual specialization bounds one exact inactive-support source piece. It
does not aggregate pieces or assert a physical step cap or return bound.
Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and the 10/14/16 target stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MDSGraphEnergy
open AESMixing
open AESConcrete.MDSGraphSupport (splitAt)

variable {V : Type*}

/-- Kernel identity only: split off the distinguished coordinate, retaining
the physical order of the other three coordinates through `succAbove`. -/
theorem coordinateKernel_splitAt (T : Fin 4 → V → V → ℝ) (s : Fin 4) :
    coordinateKernel T = reindexKernel (splitAt s)
      (tensorKernel (T s) (coordinateKernel (fun i : Fin 3 => T (s.succAbove i)))) := by
  funext y x
  change (∏ i : Fin 4, T i (y i) (x i)) =
    T s (y s) (x s) *
      ∏ i : Fin 3, T (s.succAbove i) (y (s.succAbove i)) (x (s.succAbove i))
  exact Fin.prod_univ_succAbove (fun i => T i (y i) (x i)) s

section ConditionalEnergy
variable [Fintype V] [Nonempty V]

/-- A conditional energy estimate for a coordinate tensor whose input is a
partial graph over the three coordinates other than `s`. The three free legs
need operator caps; the distinguished leg needs only its column cap. -/
theorem coordinate_partial_graph_energy
    (T : Fin 4 → V → V → ℝ) (s : Fin 4) (a : Fin 3 → ℝ) (c : ℝ)
    (hT : ∀ i (f : V → ℝ),
      (∑ y, action (T (s.succAbove i)) f y ^ 2) ≤
        (a i) ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ v, (∑ y, T s y v ^ 2) ≤ c ^ 2)
    (f : (Fin 4 → V) → ℝ)
    (hgraph : ∀ (w : Fin 3 → V) (v v' : V),
      f (Fin.insertNth s v w) ≠ 0 → f (Fin.insertNth s v' w) ≠ 0 → v = v') :
    (∑ y, action (coordinateKernel T) f y ^ 2) ≤
      (∏ i, a i) ^ 2 * c ^ 2 * ∑ x, f x ^ 2 := by
  let e := splitAt (V := V) s
  let K := tensorKernel (T s)
    (coordinateKernel (fun i : Fin 3 => T (s.succAbove i)))
  have hk : coordinateKernel T = reindexKernel e K := coordinateKernel_splitAt T s
  have hfiber : ∀ (w : Fin 3 → V) (v v' : V),
      (f ∘ e.symm) (v, w) ≠ 0 → (f ∘ e.symm) (v', w) ≠ 0 → v = v' := by
    exact hgraph
  have he := GraphColumnEnergy.tensor_partial_graph_energy (T s)
    (coordinateKernel (fun i : Fin 3 => T (s.succAbove i)))
    (∏ i, a i) c
    (FiniteTensorEnergy.coordinate_energy (fun i : Fin 3 => T (s.succAbove i)) a hT)
    hcolumn (f ∘ e.symm) hfiber
  have hn : (∑ x, (f ∘ e.symm) x ^ 2) = ∑ x, f x ^ 2 :=
    e.symm.sum_comp (fun x => f x ^ 2)
  rw [hn] at he
  rw [hk]
  simp_rw [reindexKernel_action]
  rw [e.sum_comp (fun y => action K (f ∘ e.symm) y ^ 2)]
  exact he

end ConditionalEnergy

section MDSEnergy
variable [AddCommGroup V] [Fintype V]

/-- Apply the generic conditional graph estimate to the MDS pullback of an
input supported on a zero slab. The diffusion permutation preserves input
counting energy exactly. -/
theorem coordinate_zero_slab_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (T : Fin 4 → V → V → ℝ) (r s : Fin 4) (a : Fin 3 → ℝ) (c : ℝ)
    (hT : ∀ i (f : V → ℝ),
      (∑ y, action (T (s.succAbove i)) f y ^ 2) ≤
        (a i) ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ v, (∑ y, T s y v ^ 2) ≤ c ^ 2)
    (f : (Fin 4 → V) → ℝ) (hzero : ∀ x, f x ≠ 0 → x r = 0) :
    (∑ y, action (coordinateKernel T) (fun z => f (L.symm z)) y ^ 2) ≤
      (∏ i, a i) ^ 2 * c ^ 2 * ∑ x, f x ^ 2 := by
  letI : Nonempty V := ⟨0⟩
  have he := coordinate_partial_graph_energy T s a c hT hcolumn
    (fun z => f (L.symm z))
    (MDSGraphSupport.zero_slab_pullback_fiber_unique L hL r s f hzero)
  have hn : (∑ z, f (L.symm z) ^ 2) = ∑ x, f x ^ 2 :=
    L.symm.toEquiv.sum_comp (fun x => f x ^ 2)
  rw [hn] at he
  exact he

/-- Uniform three-free-leg version: three operator caps `ρ` and one column
cap `c` give the energy coefficient `ρ^6 c^2`. -/
theorem uniform_zero_slab_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (T : V → V → ℝ) (r s : Fin 4) (ρ c : ℝ)
    (hT : ∀ f : V → ℝ,
      (∑ y, action T f y ^ 2) ≤ ρ ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ v, (∑ y, T y v ^ 2) ≤ c ^ 2)
    (f : (Fin 4 → V) → ℝ) (hzero : ∀ x, f x ≠ 0 → x r = 0) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 => T))
      (fun z => f (L.symm z)) y ^ 2) ≤
      ρ ^ 6 * c ^ 2 * ∑ x, f x ^ 2 := by
  have he := coordinate_zero_slab_energy L hL (fun _ : Fin 4 => T)
    r s (fun _ : Fin 3 => ρ) c (fun _ => hT) hcolumn f hzero
  have hp : (∏ _ : Fin 3, ρ) ^ 2 = ρ ^ 6 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  rw [hp] at he
  exact he

end MDSEnergy

-- Numerical specialization boundary: these constants come only from the
-- ordinary actual word residual operator and all-column theorems. The square
-- root supplies the generic column-cap parameter and is eliminated exactly.

/-- Ordinary actual word residual tensor after physical word diffusion of
one zero-slab input. This is an energy estimate for that input class only. -/
theorem word_residual_zero_slab_energy
    (r s : Fin 4) (f : AES.WordState → ℝ)
    (hzero : ∀ x, f x ≠ 0 → x r = 0) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 =>
      residualMatrix AES.wordSuperboxKernel 0))
      (fun z => f (WordCrossZero.wordMixAddEquiv.symm z)) y ^ 2) ≤
      (21 / 131072 : ℝ) ^ 6 * (2 / (15 * 4294967296) : ℝ) * ∑ x, f x ^ 2 := by
  have hc : (Real.sqrt (2 / (15 * 4294967296) : ℝ)) ^ 2 =
      (2 / (15 * 4294967296) : ℝ) := Real.sq_sqrt (by norm_num)
  have hcolumn : ∀ v : AES.Word,
      (∑ y, residualMatrix AES.wordSuperboxKernel 0 y v ^ 2) ≤
        (Real.sqrt (2 / (15 * 4294967296) : ℝ)) ^ 2 := by
    intro v
    rw [hc]
    exact le_of_lt (AllColumnBound.actual_word_residual_column_energy_lt v)
  have he := uniform_zero_slab_energy WordCrossZero.wordMixAddEquiv
    WordCrossZero.wordMixAddEquiv_zeroMDS (residualMatrix AES.wordSuperboxKernel 0)
    r s (21 / 131072 : ℝ) (Real.sqrt (2 / (15 * 4294967296) : ℝ))
    SharpDampedWordNorm.word_superbox_residual_energy hcolumn f hzero
  rw [hc] at he
  exact he

/-- One actual exact-support source piece with an inactive input coordinate.
This includes each selected `(3,3)` piece but performs no summation over
pieces and introduces no output-orthogonality premise. -/
theorem word_residual_support_piece_energy {d : ℕ}
    (p : SupportIndex d) (r s : Fin 4) (hr : AES.maskBit p.val.2 r = true)
    (f : AES.WordState → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 4 =>
      residualMatrix AES.wordSuperboxKernel 0))
      (fun z => supportIndexComponent (0 : AES.Word) p f
        (WordCrossZero.wordMixAddEquiv.symm z)) y ^ 2) ≤
      (21 / 131072 : ℝ) ^ 6 * (2 / (15 * 4294967296) : ℝ) *
        ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 :=
  word_residual_zero_slab_energy r s (supportIndexComponent (0 : AES.Word) p f)
    (MDSGraphSupport.supportIndexComponent_inactive_zero p r hr f)

end AESConcrete.MDSGraphEnergy
