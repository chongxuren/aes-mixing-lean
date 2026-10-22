import AESConcrete.RefinedProjectionCompleteness
import AESConcrete.WordCrossZero
import AESRound.CertificateData

/-!
# Activity branch zeros of the actual centered refined step

The raw step vanishes when the two active counts sum to at most four and the
input active count is positive. Exact inactive masks give at least four zero
graph coordinates; the actual ZeroMDS theorem forces the input state to zero,
contradicting its positive active support. Pointed parallel channels transfer
the required output zeros to the diffusion output. If either residual degree
is positive, the global uniform centering term also vanishes.

The numerical table screen is not an operator premise. This module first
proves the generic kernel identity, then specializes the actual word map, and
only afterwards checks the frozen certificate entries.

Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct reference pairs are fixed for the AES10/14/16 target.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityBranchZeros
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.RefinedStepZeros (physicalBlock blockType crossPair)
open AESConcrete.CenteredWordStepZeros (compose_assoc compose_sub_left compose_sub_right)
open AESConcrete.DegreeCentering (globalUniformKernel degreeKernel_compose_globalUniformKernel
  globalUniformKernel_compose_degreeKernel)

set_option maxRecDepth 100000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

private theorem inactive_piece_row_zero (marked : Bool) (y x : V) (hy : y ≠ 0) :
    supportPiece (0 : V) marked true y x = 0 := by
  cases marked <;> simp [supportPiece, zeroMatrix, identityKernel, hy]

theorem supportIndexKernel_inactive_row {d : ℕ} (p : SupportIndex d)
    (y x : Fin 4 → V) (h : supportIndexKernel (0 : V) p y x ≠ 0) :
    ∀ i, AES.maskBit p.val.2 i = true → y i = 0 := by
  intro i hi
  by_contra hy
  apply h
  unfold supportIndexKernel supportProduct
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [hi]
  exact inactive_piece_row_zero _ _ _ hy

theorem supportIndexKernel_inactive_column {d : ℕ} (p : SupportIndex d)
    (y x : Fin 4 → V) (h : supportIndexKernel (0 : V) p y x ≠ 0) :
    ∀ i, AES.maskBit p.val.2 i = true → x i = 0 := by
  have hs : supportIndexKernel (0 : V) p x y ≠ 0 := by
    rw [supportIndexKernel_symmetric]
    exact h
  exact supportIndexKernel_inactive_row p x y hs

/-- Extract a genuine selected support summand; no positivity of the
refined kernel is assumed. -/
theorem refined_nonzero_witness (d a : Fin 5) (y x : Fin 4 → V)
    (h : refinedKernel (0 : V) d a y x ≠ 0) :
    ∃ p : SupportIndex d.val, AES.maskSize p.val.2 + a.val = 4 ∧
      supportIndexKernel (0 : V) p y x ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  unfold refinedKernel
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · rw [if_pos hp, hn p hp]
  · rw [if_neg hp]

theorem parallel_zero_row_transfer (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (y x : Fin 4 → V) (h : coordinateKernel (fun _ : Fin 4 => D) y x ≠ 0)
    (i : Fin 4) (hy : y i = 0) : x i = 0 := by
  by_contra hx
  apply h
  unfold coordinateKernel
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change D (y i) (x i) = 0
  rw [hy, hD.zero_row]
  simp [hx]

/-- Raw physical branch zero. Only the inactive portions of the two
exact supports are needed for the ZeroMDS implication. -/
theorem raw_refined_branch_zero (D : V → V → ℝ) (hD : PointedBistochastic D 0)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (d a j b : Fin 5) (hab : a.val + b.val ≤ 4) (hb : b ≠ 0) :
    kernelCompose (refinedKernel (0 : V) d a)
      (kernelCompose (fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x))
        (refinedKernel (0 : V) j b)) = 0 := by
  have hterm (y x v w : Fin 4 → V) :
      refinedKernel (0 : V) d a y v *
        (coordinateKernel (fun _ : Fin 4 => D) v (L w) *
          refinedKernel (0 : V) j b w x) = 0 := by
    by_cases hp : refinedKernel (0 : V) d a y v = 0
    · simp [hp]
    by_cases hH : coordinateKernel (fun _ : Fin 4 => D) v (L w) = 0
    · simp [hH]
    by_cases hq : refinedKernel (0 : V) j b w x = 0
    · simp [hq]
    obtain ⟨p, hpa, hpk⟩ := refined_nonzero_witness d a y v hp
    obtain ⟨q, hqb, hqk⟩ := refined_nonzero_witness j b w x hq
    have hsize : 4 ≤ AES.maskSize p.val.2 + AES.maskSize q.val.2 := by omega
    have hgraph : graphZeroConditions L p.val.2 q.val.2 w := by
      constructor
      · intro i hi
        exact parallel_zero_row_transfer D hD v (L w) hH i
          (supportIndexKernel_inactive_column p y v hpk i hi)
      · exact supportIndexKernel_inactive_row q w x hqk
    have hw : w = 0 := mds_graph_zero_high L hL p.val.2 q.val.2 hsize w hgraph
    have hz : refinedKernel (0 : V) j b w x = 0 := by
      rw [hw]
      exact RefinedProjectionCompleteness.refined_at_zero (0 : V) j b hb x
    exact (hq hz).elim
  funext y x
  unfold kernelCompose
  simp only [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w _
  exact hterm y x v w

theorem refined_uniform_zero_of_positive (hn : 1 < Fintype.card V)
    (d a : Fin 5) (hd : d ≠ 0) :
    kernelCompose (refinedKernel (0 : V) d a) (globalUniformKernel 0) = 0 := by
  have hp := refinedKernel_compose_degreeKernel (0 : V) hn d a
  calc
    _ = kernelCompose (kernelCompose (refinedKernel (0 : V) d a) (degreeKernel (0 : V) d))
        (globalUniformKernel (0 : V)) := by rw [hp]
    _ = kernelCompose (refinedKernel (0 : V) d a)
        (kernelCompose (degreeKernel (0 : V) d) (globalUniformKernel (0 : V))) :=
      (compose_assoc _ _ _).symm
    _ = 0 := by
      rw [degreeKernel_compose_globalUniformKernel (0 : V) hn d hd]
      funext y x
      simp [kernelCompose]

theorem uniform_refined_zero_of_positive (hn : 1 < Fintype.card V)
    (j b : Fin 5) (hj : j ≠ 0) :
    kernelCompose (globalUniformKernel (0 : V)) (refinedKernel 0 j b) = 0 := by
  have hp := degreeKernel_compose_refinedKernel (0 : V) hn j b
  calc
    _ = kernelCompose (globalUniformKernel (0 : V))
        (kernelCompose (degreeKernel (0 : V) j) (refinedKernel (0 : V) j b)) := by rw [hp]
    _ = kernelCompose (kernelCompose (globalUniformKernel (0 : V)) (degreeKernel (0 : V) j))
        (refinedKernel (0 : V) j b) := compose_assoc _ _ _
    _ = 0 := by
      rw [globalUniformKernel_compose_degreeKernel (0 : V) hn j hj]
      funext y x
      simp [kernelCompose]

/-- Positivity of either residual degree is used only to remove centering.
The raw branch zero above is independent of residual degree. -/
theorem centered_refined_branch_zero (D : V → V → ℝ) (hn : 1 < Fintype.card V)
    (hD : PointedBistochastic D 0) (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (d a j b : Fin 5) (hab : a.val + b.val ≤ 4) (hb : b ≠ 0)
    (hpositive : d ≠ 0 ∨ j ≠ 0) :
    kernelCompose (refinedKernel (0 : V) d a)
      (kernelCompose
        ((fun y x => coordinateKernel (fun _ : Fin 4 => D) y (L x)) - globalUniformKernel 0)
        (refinedKernel (0 : V) j b)) = 0 := by
  rw [compose_sub_left, compose_sub_right, raw_refined_branch_zero D hD L hL d a j b hab hb]
  rcases hpositive with hd | hj
  · rw [compose_assoc, refined_uniform_zero_of_positive hn d a hd]
    funext y x
    simp [kernelCompose]
  · rw [uniform_refined_zero_of_positive hn j b hj]
    funext y x
    simp [kernelCompose]

def branchPair (i j : Fin 14) : Prop :=
  (blockType i).2.val + (blockType j).2.val ≤ 4 ∧
    ((blockType i).1 ≠ 0 ∨ (blockType j).1 ≠ 0)

instance (i j : Fin 14) : Decidable (branchPair i j) := by
  unfold branchPair
  infer_instance

private theorem blockType_active : ∀ i : Fin 14, (blockType i).2 ≠ 0 := by decide

theorem physical_branch_zero (i j : Fin 14) (h : branchPair i j) :
    physicalBlock i j = 0 := by
  exact centered_refined_branch_zero AES.wordSuperboxKernel
    (by rw [AES.word_card]; norm_num) AES.word_superbox_pointed
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
    (blockType i).1 (blockType i).2 (blockType j).1 (blockType j).2
    h.1 (blockType_active j) h.2

theorem physical_branch_norm (i j : Fin 14) (h : branchPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply kernelOperator_norm_le _ (le_refl 0)
  intro f
  rw [physical_branch_zero i j h]
  simp [action]

/-- This finite table check follows the operator proof; it is not a premise. -/
theorem certificate_branch_entries (i j : Fin 14) (h : branchPair i j) :
    AESRound.Certificate.L i j = 0 ∧ AESRound.Certificate.H i j = 0 := by
  fin_cases i <;> fin_cases j
  all_goals first | exact ⟨rfl, rfl⟩ | (exfalso; revert h; decide)

theorem physical_branch_step_cap (i j : Fin 14) (h : branchPair i j) :
    ‖kernelOperator (physicalBlock i j)‖ ≤
      ((101 : ℝ) / 2 ^ (48 : ℕ)) * AESRound.Certificate.L i j := by
  rw [physical_branch_norm i j h, (certificate_branch_entries i j h).1]
  simp

theorem branchPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => branchPair ij.1 ij.2)).card = 35 := by decide

theorem additional_branchPair_count :
    ((Finset.univ.product Finset.univ).filter
      (fun ij : Fin 14 × Fin 14 => branchPair ij.1 ij.2 ∧ ¬crossPair ij.1 ij.2)).card = 23 := by decide

end AESConcrete.ActivityBranchZeros
