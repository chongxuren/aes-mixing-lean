import AESMixing.IncidenceCounting
import AESMixing.IncidenceComparison

/-! Exact byte-size specialization of the incidence sum. Only the fixed
four-coordinate subset arithmetic is finite; all vector functions remain
arbitrary in the analytic theorem. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskSize)

theorem incidenceNormCoefficient_square (p : ℝ) (hp : 0 ≤ p) (n i j : ℕ) :
    incidenceNormCoefficient (p^2) n i j =
      if 4 ≤ n ∨ n+i+j ≤ 4 then 0 else p^((4-(n+i))+(4-(n+j))) := by
  unfold incidenceNormCoefficient
  split_ifs
  · rfl
  · rw [← pow_add]
    have he : (p^2)^((4-(n+i))+(4-(n+j))) =
        (p^((4-(n+i))+(4-(n+j))))^2 := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

def byteIncidenceTerm (n i j : ℕ) : ℕ :=
  if 4 ≤ n ∨ n+i+j ≤ 4 then 0 else 16^((4-(n+i))+(4-(n+j)))

theorem byte_incidence_term (n i j : ℕ) :
    incidenceNormCoefficient 256 n i j = (byteIncidenceTerm n i j : ℝ) := by
  rw [show (256 : ℝ) = 16^2 by norm_num, incidenceNormCoefficient_square 16 (by norm_num)]
  unfold byteIncidenceTerm
  split_ifs <;> norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem byte_incidence_reindex : ∀ r z i j : Fin 5,
    r.val+i.val ≤ 4 → z.val+j.val ≤ 4 →
    ((∑ t ∈ Finset.range ((4-(r.val+i.val))+(4-(z.val+j.val))+1),
      ((4-(r.val+i.val))+(4-(z.val+j.val))).choose t *
        byteIncidenceTerm (r.val+z.val+t) i.val j.val : ℕ) : ℚ) =
      incidenceSupportRaw i.val j.val (4-r.val) (4-z.val) := by
  intro r z i j
  fin_cases r <;> fin_cases z <;> fin_cases i <;> fin_cases j <;>
    norm_num [byteIncidenceTerm, incidenceSupportRaw, Finset.sum_range_succ, Nat.choose]

theorem byte_shorteningNormSum (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp) :
    shorteningNormSum 256 r z (unmarkedGraphPositions r z out inp) out inp =
      (incidenceSupportRaw (maskSize out) (maskSize inp) (4-maskSize r) (4-maskSize z) : ℝ) := by
  rw [shorteningNormSum_by_size 256 r z out inp hr hz]
  simp_rw [byte_incidence_term]
  have h := byte_incidence_reindex
    ⟨maskSize r,Nat.lt_succ_of_le (maskSize_le_four r)⟩
    ⟨maskSize z,Nat.lt_succ_of_le (maskSize_le_four z)⟩
    ⟨maskSize out,Nat.lt_succ_of_le (maskSize_le_four out)⟩
    ⟨maskSize inp,Nat.lt_succ_of_le (maskSize_le_four inp)⟩
    (disjoint_mask_size_le_four r out hr) (disjoint_mask_size_le_four z inp hz)
  have hh := congrArg (fun q : ℚ => (q : ℝ)) h
  rw [Rat.cast_natCast] at hh
  simpa only [Nat.cast_sum, Nat.cast_mul, Fin.val_mk] using hh

end AESMixing
