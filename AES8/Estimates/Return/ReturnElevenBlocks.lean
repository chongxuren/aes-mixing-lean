/- Module role: Selected concrete high-return estimates.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.ZeroOutsideProjection
import AES8.Reductions.Return.ReturnCentering
import AESMixing.L2Sums

/-!
# Four orthogonal outside patterns for return eleven

A uniform norm cap on each literal Q_r T Q_z block gives a factor four
on the component-eleven operator. The two factors of two come from the
input and output orthogonal families. Signed inputs remain arbitrary.
The block bounds are explicit premises; this does not prove a return cell.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AES8.ReturnElevenBlocks
open AESMixing AESMixing.AES
open AES8.ZeroOutsideProjection
open AES8.SupportProfile (component profile)

theorem Q_sum {J : Type*} [Fintype J] (r : Fin 4) (f : J → WordState → ℝ) :
    Q r (fun x => ∑ j, f j x) = fun x => ∑ j, Q r (f j) x := by
  simp only [Q_eq_support_action, action_sum_family]

theorem sum_pattern_lengths_le (f : WordState → ℝ) :
    (∑ r : Fin 4, l2 (Q r f)) ≤ 2 * l2 (component f 11) := by
  have hn : l2 (fun r : Fin 4 => l2 (Q r f)) = l2 (component f 11) := by
    apply (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
    simp only [l2_sq, component_eleven_energy]
  have hone : l2 (fun _ : Fin 4 => (1 : ℝ)) = 2 := by
    apply (sq_eq_sq₀ (l2_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mp
    norm_num [l2_sq]
  have h := abs_inner_le_l2 (fun r : Fin 4 => l2 (Q r f)) (fun _ => (1 : ℝ))
  have hpos : 0 ≤ ∑ r : Fin 4, l2 (Q r f) :=
    Finset.sum_nonneg (fun r _ => l2_nonneg _)
  simp only [_root_.mul_one, abs_of_nonneg hpos, hn, hone] at h
  exact h.trans_eq (_root_.mul_comm _ _)

/-- A four-by-four block estimate on exact orthogonal outside projections. -/
theorem component_action_l2_le (D : WordState → WordState → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hblock : ∀ (f : WordState → ℝ) (r z : Fin 4),
      l2 (Q r (action D (Q z f))) ≤ K * l2 (Q z f))
    (f : WordState → ℝ) :
    l2 (component (action D (component f 11)) 11) ≤ (4 * K) * l2 (component f 11) := by
  have hrow (r : Fin 4) :
      l2 (Q r (action D (component f 11))) ≤ (2 * K) * l2 (component f 11) := by
    have he : Q r (action D (component f 11)) =
        fun x => ∑ z : Fin 4, Q r (action D (Q z f)) x := by
      rw [component_eleven_eq_sum_Q, action_sum_family, Q_sum]
    rw [he]
    calc
      _ ≤ ∑ z : Fin 4, l2 (Q r (action D (Q z f))) :=
        l2_finset_sum_le Finset.univ (fun z => Q r (action D (Q z f)))
      _ ≤ ∑ z : Fin 4, K * l2 (Q z f) := Finset.sum_le_sum (fun z _ => hblock f r z)
      _ = K * ∑ z : Fin 4, l2 (Q z f) := (Finset.mul_sum _ _ _).symm
      _ ≤ K * (2 * l2 (component f 11)) :=
        mul_le_mul_of_nonneg_left (sum_pattern_lengths_le f) hK
      _ = _ := by ring
  apply l2_le_of_energy _ (component f 11) (4 * K) (by positivity)
  calc
    _ = ∑ r : Fin 4, l2 (Q r (action D (component f 11))) ^ 2 := by
      rw [component_eleven_energy]
      simp only [l2_sq]
    _ ≤ ∑ _r : Fin 4, ((2 * K) * l2 (component f 11)) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      exact (sq_le_sq₀ (l2_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) hK) (l2_nonneg _))).mpr (hrow r)
    _ = (4 * K) ^ 2 * ∑ x, component f 11 x ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat, mul_pow, l2_sq]
      ring

/-- The actual middle-high return uses the exact physical kernel identity. -/
theorem highReturn_profile_le_of_blocks (K : ℝ) (hK : 0 ≤ K)
    (hblock : ∀ (f : WordState → ℝ) (r z : Fin 4),
      l2 (Q r (action ReturnCentering.physicalReturnKernel (Q z f))) ≤ K * l2 (Q z f))
    (f : WordState → ℝ) :
    profile (TransferAssembly.highReturn (component f 11)) 11 ≤ (4 * K) * profile f 11 := by
  rw [ReturnCentering.highReturn_eq_physical_action]
  exact component_action_l2_le ReturnCentering.physicalReturnKernel K hK hblock f

end AES8.ReturnElevenBlocks
