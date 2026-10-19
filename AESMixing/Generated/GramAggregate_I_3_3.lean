import AESMixing.GramCertificates.I_3_3_s0
import AESMixing.GramCertificates.I_3_3_s1
import AESMixing.GramCertificates.I_3_3_s2
import AESMixing.GramCertificates.I_3_3_s3
import AESMixing.GramCertificates.I_3_3_s4
import AESMixing.GramCertificates.I_3_3_s5
import AESMixing.GramCertificates.I_3_3_s6
import AESMixing.GramCertificates.I_3_3_s7
import AESMixing.GramCertificates.I_3_3_s8
import AESMixing.GramCertificates.I_3_3_s9
import AESMixing.GramCertificates.I_3_3_s10
import AESMixing.GramCertificates.I_3_3_s11
import AESMixing.GramCertificates.I_3_3_s12
import AESMixing.GramCertificates.I_3_3_s13
import AESMixing.GramCertificates.I_3_3_s14
import AESMixing.GramCertificates.I_3_3_s15
import AESMixing.GramCertificates.I_3_3_s16
import AESMixing.GramCertificates.I_3_3_s17
import AESMixing.GramCertificates.I_3_3_s18
import AESMixing.GramCertificates.I_3_3_s19
import AESMixing.GramCertificates.I_3_3_s20
import AESMixing.GramCertificates.I_3_3_s21
import AESMixing.GramCertificates.I_3_3_s22
import AESMixing.GramCertificates.I_3_3_s23
import AESMixing.GramCertificates.I_3_3_s24
import AESMixing.AESGramOrientation
open scoped BigOperators
set_option maxRecDepth 1000000
namespace AESMixing.GramPair.I_3_3
-- Exhaustive aggregation: every mode has a unique block and within-block index.
def blockRanks : Fin 25 → Fin 25 → ℕ := ![AESMixing.GramCertificates.I_3_3_s0.ranks, AESMixing.GramCertificates.I_3_3_s1.ranks, AESMixing.GramCertificates.I_3_3_s2.ranks, AESMixing.GramCertificates.I_3_3_s3.ranks, AESMixing.GramCertificates.I_3_3_s4.ranks, AESMixing.GramCertificates.I_3_3_s5.ranks, AESMixing.GramCertificates.I_3_3_s6.ranks, AESMixing.GramCertificates.I_3_3_s7.ranks, AESMixing.GramCertificates.I_3_3_s8.ranks, AESMixing.GramCertificates.I_3_3_s9.ranks, AESMixing.GramCertificates.I_3_3_s10.ranks, AESMixing.GramCertificates.I_3_3_s11.ranks, AESMixing.GramCertificates.I_3_3_s12.ranks, AESMixing.GramCertificates.I_3_3_s13.ranks, AESMixing.GramCertificates.I_3_3_s14.ranks, AESMixing.GramCertificates.I_3_3_s15.ranks, AESMixing.GramCertificates.I_3_3_s16.ranks, AESMixing.GramCertificates.I_3_3_s17.ranks, AESMixing.GramCertificates.I_3_3_s18.ranks, AESMixing.GramCertificates.I_3_3_s19.ranks, AESMixing.GramCertificates.I_3_3_s20.ranks, AESMixing.GramCertificates.I_3_3_s21.ranks, AESMixing.GramCertificates.I_3_3_s22.ranks, AESMixing.GramCertificates.I_3_3_s23.ranks, AESMixing.GramCertificates.I_3_3_s24.ranks]
-- Each hexadecimal digit stores one rank; the least significant digit is mode zero.
def ranks (i : Fin 625) : ℕ :=
  (0x6777678887788877888767776788878888888888888887888778887888888878788887787767888788888888878887778776677767888778776787766766578887888888888888888788878888888888888888888888888888888888888787888888878788888888888888888877888777888788888887878887778776788878888888787888877877688888888888878788888887878878788787776768878777676888878888888787888777877678776887877767678776676657888788888888878887778776888888888888888888778887788887888888878788877787768887788877888777776677766787768887778776777666766567776788877877678776676657888788888887878887778776787768878777676787766766578776888777877677766676656766578776676656766556554 >>> (4*i.val)) % 16
theorem block_counts (b t : Fin 25) : gramCaseCount true 3 3 (gramSubModeIndex b t) =
    256^(8-blockRanks b t) := by
  fin_cases b
  · exact AESMixing.GramCertificates.I_3_3_s0.counts t
  · exact AESMixing.GramCertificates.I_3_3_s1.counts t
  · exact AESMixing.GramCertificates.I_3_3_s2.counts t
  · exact AESMixing.GramCertificates.I_3_3_s3.counts t
  · exact AESMixing.GramCertificates.I_3_3_s4.counts t
  · exact AESMixing.GramCertificates.I_3_3_s5.counts t
  · exact AESMixing.GramCertificates.I_3_3_s6.counts t
  · exact AESMixing.GramCertificates.I_3_3_s7.counts t
  · exact AESMixing.GramCertificates.I_3_3_s8.counts t
  · exact AESMixing.GramCertificates.I_3_3_s9.counts t
  · exact AESMixing.GramCertificates.I_3_3_s10.counts t
  · exact AESMixing.GramCertificates.I_3_3_s11.counts t
  · exact AESMixing.GramCertificates.I_3_3_s12.counts t
  · exact AESMixing.GramCertificates.I_3_3_s13.counts t
  · exact AESMixing.GramCertificates.I_3_3_s14.counts t
  · exact AESMixing.GramCertificates.I_3_3_s15.counts t
  · exact AESMixing.GramCertificates.I_3_3_s16.counts t
  · exact AESMixing.GramCertificates.I_3_3_s17.counts t
  · exact AESMixing.GramCertificates.I_3_3_s18.counts t
  · exact AESMixing.GramCertificates.I_3_3_s19.counts t
  · exact AESMixing.GramCertificates.I_3_3_s20.counts t
  · exact AESMixing.GramCertificates.I_3_3_s21.counts t
  · exact AESMixing.GramCertificates.I_3_3_s22.counts t
  · exact AESMixing.GramCertificates.I_3_3_s23.counts t
  · exact AESMixing.GramCertificates.I_3_3_s24.counts t
set_option maxHeartbeats 0 in
theorem blockRanks_eq (b t : Fin 25) : blockRanks b t = ranks (gramSubModeIndex b t) := by
  revert b t; decide
theorem counts (i : Fin 625) : gramCaseCount true 3 3 i = 256^(8-ranks i) := by
  have h := block_counts (gramSubBlock i) (gramSubWithin i)
  rw [blockRanks_eq, gramSubModeIndex_split] at h
  exact h
def values : Fin 5 → ℤ := ![8456761350, 0, 50737446900, 8524155340800, 268519283410950]
set_option maxHeartbeats 0 in
theorem numerator_values (j : Fin 5) :
    rankGramNumerator (fun m => ranks (finFunctionFinEquiv m)) j = values j := by
  fin_cases j <;> decide
theorem gram_entries (j : Fin 5) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 3) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 3) y) =
        (values j : ℝ)/255^4 := by
  rw [oriented_activity_gram_from_ranks true j 3 3 ranks counts, numerator_values]
#print axioms counts
#print axioms numerator_values
#print axioms gram_entries
end AESMixing.GramPair.I_3_3
