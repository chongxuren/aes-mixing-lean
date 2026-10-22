import AES8.Estimates.Word.PaperSharpEntriesSelection
import AES8.Estimates.Word.PaperSharpEntriesProfileReparam
import AESConcrete.WordEntryGraph

/-!
# Physical graph entry reduction to explicit byte pair predicates

The combinatorial selection, affine section geometry, pair reparametrization
and mass-one averaging are joined here. The finite predicates are explicit
byte-level premises; no full-entry cap is assumed. Numerical certification and
the ordinary/full-Fourier endpoint wrappers remain separate responsibilities.
Draft only until the coordinator records diagnostic and integrated receipts.
Constructive mathematics only; no attacks or local application execution.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperSharpEntriesGraphReduction
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.MDSFiveFactorEntry
open AESConcrete.ShortenedLineResponse
  (Byte byteDiffusionHom byteDiffusionHom_zeroMDS)
open AES8.PaperSharpEntriesSelection
open AES8.PaperSharpEntriesAffineSections
open AES8.PaperSharpEntriesProfileReparam
attribute [local instance] Classical.propDecidable

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Mass-one averaging consumes a proved bound for each actual fixed section.
This is the lower-level version of the inherited fifth-moment theorem. -/
theorem graphResponse_le_sections
    {V I : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4)
    (T : RemainingPosition r z → V → ℝ) (hnonneg : ∀ p v, 0 ≤ T p v)
    (hmass : ∀ p, (∑ v : V, T p v) = 1) (H : ℝ)
    (hsection : ∀ a : I → V,
      (∑ v : V, ∏ k : Fin 5, T (idx (Sum.inr k))
        (graphCoordinate L (sectionSource L hL r z idx hsize a v).val
          (idx (Sum.inr k)).val)) ≤ H) :
    graphResponse L r z T ≤ H := by
  let weight (a : I → V) : ℝ := ∏ i : I, T (idx (Sum.inl i)) (a i)
  let remainder (a : I → V) (v : V) : ℝ := ∏ k : Fin 5,
    T (idx (Sum.inr k))
      (graphCoordinate L (sectionSource L hL r z idx hsize a v).val
        (idx (Sum.inr k)).val)
  have hweight (a : I → V) : 0 ≤ weight a :=
    Finset.prod_nonneg (fun i _ => hnonneg _ _)
  have hmassfixed : (∑ a : I → V, weight a) = 1 := by
    dsimp only [weight]
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  have hprod (a : I → V) (v : V) :
      (∏ p : RemainingPosition r z,
        T p (graphCoordinate L (sectionSource L hL r z idx hsize a v).val p.val)) =
        weight a * remainder a v := by
    rw [← idx.prod_comp (fun p : RemainingPosition r z =>
      T p (graphCoordinate L (sectionSource L hL r z idx hsize a v).val p.val))]
    rw [Fintype.prod_sum_type]
    dsimp only [weight, remainder]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [section_fixed]
  have hsum : graphResponse L r z T =
      ∑ a : I → V, weight a * ∑ v : V, remainder a v := by
    calc
      _ = ∑ av : (I → V) × V, ∏ p : RemainingPosition r z,
          T p (graphCoordinate L (sectionSource L hL r z idx hsize av.1 av.2).val p.val) :=
        ((projectionEquiv L hL r z idx hsize 0).symm.sum_comp
          (fun c : ShortenedGraph L r z =>
            ∏ p : RemainingPosition r z, T p (graphCoordinate L c.val p.val))).symm
      _ = ∑ a : I → V, ∑ v : V, weight a * remainder a v := by
        rw [Fintype.sum_prod_type]
        simp only [hprod]
      _ = _ := by simp only [Finset.mul_sum]
  rw [hsum]
  calc
    _ ≤ ∑ a : I → V, weight a * H :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hsection a) (hweight a))
    _ = H := by rw [← Finset.sum_mul, hmassfixed, one_mul]

/-- The only four numerical predicate families needed after selection. -/
structure RequiredPairCaps (rho : Byte → ℝ) (B : Byte ≃+ Byte) (H : ℝ) : Prop where
  balanced23 : PairCap rho B 2 3 H
  balanced32 : PairCap rho B 3 2 H
  homogeneous14 : HomogeneousPairCap rho B 1 4 H
  homogeneous41 : HomogeneousPairCap rho B 4 1 H

theorem selected_pair_cap {rho : Byte → ℝ} {B : Byte ≃+ Byte} {H : ℝ}
    (caps : RequiredPairCaps rho B H) {r z s t : Fin 16} (h : Shape r z s t) :
    PairCap rho B (maskSize s) (maskSize t) H ∨
      (maskSize r + maskSize z = 3 ∧
        HomogeneousPairCap rho B (maskSize s) (maskSize t) H) := by
  rcases h.branch with h | h | ⟨hz, h | h⟩
  · exact Or.inl (by simpa only [h.1, h.2] using caps.balanced23)
  · exact Or.inl (by simpa only [h.1, h.2] using caps.balanced32)
  · exact Or.inr ⟨hz, by simpa only [h.1, h.2] using caps.homogeneous14⟩
  · exact Or.inr ⟨hz, by simpa only [h.1, h.2] using caps.homogeneous41⟩

def physicalLeg (C : Byte → Byte → ℝ) (a b : Fin 4 → Byte) :
    GraphPosition → Byte → ℝ
  | Sum.inl i, v => C (b i) v
  | Sum.inr i, v => C v (a i)

/-- Reduce each selected physical section to an affine or homogeneous mixed
pair predicate. Labels are required nonzero only on the actual active legs. -/
theorem selected_section_le
    (inverse : Bool) (C : Byte → Byte → ℝ) (rho : Byte → ℝ) (B : Byte ≃+ Byte)
    (hrow : ∀ b v, b ≠ 0 → C b v = rho (B b * v))
    (hcol : ∀ a v, a ≠ 0 → C v a = rho (a * B v))
    (hnonneg : ∀ b a, 0 ≤ C b a)
    (a b : Fin 4 → Byte) {r z s t : Fin 16} (h : Shape r z s t)
    (ha : ∀ i : MaskCoordinates t, a i.val ≠ 0)
    (hb : ∀ i : MaskCoordinates s, b i.val ≠ 0)
    (H : ℝ) (caps : RequiredPairCaps rho B H)
    (fixed : Fixed r z s t → Byte) :
    (∑ v : Byte, ∏ k : Fin 5,
      physicalLeg C a b (sectionIndex h (Sum.inr k)).val
        (graphCoordinate (byteDiffusionHom inverse)
          (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
            r z (sectionIndex h) (fixed_card_size h) fixed v).val
          (sectionIndex h (Sum.inr k)).val)) ≤ H := by
  let idx := sectionIndex h
  let hs := fixed_card_size h
  let coord (k : Fin 5) (v : Byte) : Byte :=
    graphCoordinate (byteDiffusionHom inverse)
      (sectionSource (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
        r z idx hs fixed v).val (idx (Sum.inr k)).val
  let T : MaskCoordinates s ⊕ MaskCoordinates t → Byte → ℝ := fun p v =>
    physicalLeg C a b (idx (Sum.inr (sideIndex h p))).val (coord (sideIndex h p) v)
  have hprod (v : Byte) :
      (∏ k : Fin 5, physicalLeg C a b (idx (Sum.inr k)).val (coord k v)) =
        ∏ p : MaskCoordinates s ⊕ MaskCoordinates t, T p v := by
    exact ((sideIndex h).prod_comp
      (fun k => physicalLeg C a b (idx (Sum.inr k)).val (coord k v))).symm
  have hnn : ∀ p v, 0 ≤ T p v := by
    intro p v
    dsimp [T, physicalLeg]
    cases (idx (Sum.inr (sideIndex h p))).val <;> exact hnonneg _ _
  have hpair (i : MaskCoordinates s) (j : MaskCoordinates t) :
      (∑ v : Byte, T (Sum.inl i) v ^ Fintype.card (MaskCoordinates s) *
        T (Sum.inr j) v ^ Fintype.card (MaskCoordinates t)) ≤ H := by
    let ki := sideIndex h (Sum.inl i)
    let kj := sideIndex h (Sum.inr j)
    have htout (v : Byte) : T (Sum.inl i) v =
        C (b i.val) (sectionSlope inverse r z idx hs ki * v +
          sectionOffset inverse r z idx hs fixed ki) := by
      dsimp only [T]
      rw [show (idx (Sum.inr ki)).val = Sum.inl i.val from sectionIndex_output h i]
      change C (b i.val) (coord ki v) = _
      rw [show coord ki v = _ from
        section_coordinate_affine inverse r z idx hs fixed ki v]
    have htin (v : Byte) : T (Sum.inr j) v =
        C (sectionSlope inverse r z idx hs kj * v +
          sectionOffset inverse r z idx hs fixed kj) (a j.val) := by
      dsimp only [T]
      rw [show (idx (Sum.inr kj)).val = Sum.inr j.val from sectionIndex_input h j]
      change C (coord kj v) (a j.val) = _
      rw [show coord kj v = _ from
        section_coordinate_affine inverse r z idx hs fixed kj v]
    simp_rw [htout, htin, maskCoordinates_card]
    rcases selected_pair_cap caps h with hcap | ⟨hz, hcap⟩
    · exact affine_pair_sum_le B rho C hrow hcol (a j.val) (b i.val)
        (sectionSlope inverse r z idx hs ki) (sectionSlope inverse r z idx hs kj)
        (sectionOffset inverse r z idx hs fixed ki)
        (sectionOffset inverse r z idx hs fixed kj) (ha j) (hb i)
        (sectionSlope_ne_zero inverse r z idx hs ki)
        (sectionSlope_ne_zero inverse r z idx hs kj) _ _ H hcap
    · rw [sectionOffset_eq_zero_of_three_zeros inverse h hz fixed ki,
        sectionOffset_eq_zero_of_three_zeros inverse h hz fixed kj]
      simp only [add_zero]
      exact homogeneous_pair_sum_le B rho C hrow hcol (a j.val) (b i.val)
        (sectionSlope inverse r z idx hs ki) (sectionSlope inverse r z idx hs kj)
        (ha j) (hb i) (sectionSlope_ne_zero inverse r z idx hs ki)
        (sectionSlope_ne_zero inverse r z idx hs kj) _ _ H hcap
  change (∑ v : Byte, ∏ k : Fin 5,
    physicalLeg C a b (idx (Sum.inr k)).val (coord k v)) ≤ H
  simp_rw [hprod]
  apply AES8.PaperSharpEntriesReduction.sum_prod_sum_type_le_pair_moment T hnn
    (by rw [maskCoordinates_card]; exact (side_sizes_pos h).1)
    (by rw [maskCoordinates_card]; exact (side_sizes_pos h).2) H hpair

/-- Actual same-orientation word entries in both diffusion directions reduce
to the four explicit byte pair predicates. All zero masks and active labels
are those of the external words; no arbitrary entry resource is a premise. -/
theorem word_entry_le_of_pairCaps
    (o : AESConcrete.ByteOrientations.Orientation) (inverse : Bool)
    (rho : Byte → ℝ) (B : Byte ≃+ Byte)
    (hrow : ∀ b v, b ≠ 0 → AESConcrete.ByteOrientations.channel o b v = rho (B b * v))
    (hcol : ∀ a v, a ≠ 0 → AESConcrete.ByteOrientations.channel o v a = rho (a * B v))
    (H : ℝ) (hH : 0 ≤ H) (caps : RequiredPairCaps rho B H)
    (a b : AESConcrete.WordColumnGram.Word) (ha : a ≠ 0) :
    AESConcrete.WordOrientationClosure.wordKernel o o inverse b a ≤ H := by
  let r := AESConcrete.AllColumnBound.inputZeroMask b
  let z := AESConcrete.AllColumnBound.inputZeroMask a
  rw [AESConcrete.WordEntryGraph.actual_shortened_formula]
  change graphResponse (byteDiffusionHom inverse) r z
    (fun p => AESConcrete.WordEntryGraph.leg o o a b p.val) ≤ H
  by_cases hz : maskSize r + maskSize z ≤ 3
  · obtain ⟨s, t, h⟩ := balanced_or_homogeneous_masks r z hz
    apply graphResponse_le_sections (byteDiffusionHom inverse)
      (byteDiffusionHom_zeroMDS inverse) r z (sectionIndex h) (fixed_card_size h)
      (fun p => AESConcrete.WordEntryGraph.leg o o a b p.val)
      (fun p v => AESConcrete.WordEntryGraph.leg_nonneg o o a b p.val v)
      (fun p => AESConcrete.WordEntryGraph.leg_mass o o a b p.val) H
    intro fixed
    have hai (i : MaskCoordinates t) : a i.val ≠ 0 := by
      intro hi
      exact h.input_available i.val
        ((AESConcrete.AllColumnBound.inputZeroMask_bit a i.val).mpr hi) i.property
    have hbi (i : MaskCoordinates s) : b i.val ≠ 0 := by
      intro hi
      exact h.output_available i.val
        ((AESConcrete.AllColumnBound.inputZeroMask_bit b i.val).mpr hi) i.property
    exact selected_section_le inverse (AESConcrete.ByteOrientations.channel o)
      rho B hrow hcol (AESConcrete.ByteOrientations.channel_resources o).nonnegative
      a b h hai hbi H caps fixed
  · obtain ⟨p⟩ := AESConcrete.WordEntryGraph.active_nonempty_of_input_ne_zero a b ha
    rw [graphResponse_zero_of_high_zeros (byteDiffusionHom inverse)
      (byteDiffusionHom_zeroMDS inverse) r z (by omega)
      (fun p => AESConcrete.WordEntryGraph.leg o o a b p.val) p
      (AESConcrete.WordEntryGraph.active_leg_zero o o a b p)]
    exact hH

end AES8.PaperSharpEntriesGraphReduction
