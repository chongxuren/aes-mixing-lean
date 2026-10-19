import AESMixing.GramCertificates.I_4_8_s0
import AESMixing.GramCertificates.I_4_8_s1
import AESMixing.GramCertificates.I_4_8_s2
import AESMixing.GramCertificates.I_4_8_s3
import AESMixing.GramCertificates.I_4_8_s4
import AESMixing.GramCertificates.I_4_8_s5
import AESMixing.GramCertificates.I_4_8_s6
import AESMixing.GramCertificates.I_4_8_s7
import AESMixing.GramCertificates.I_4_8_s8
import AESMixing.GramCertificates.I_4_8_s9
import AESMixing.GramCertificates.I_4_8_s10
import AESMixing.GramCertificates.I_4_8_s11
import AESMixing.GramCertificates.I_4_8_s12
import AESMixing.GramCertificates.I_4_8_s13
import AESMixing.GramCertificates.I_4_8_s14
import AESMixing.GramCertificates.I_4_8_s15
import AESMixing.GramCertificates.I_4_8_s16
import AESMixing.GramCertificates.I_4_8_s17
import AESMixing.GramCertificates.I_4_8_s18
import AESMixing.GramCertificates.I_4_8_s19
import AESMixing.GramCertificates.I_4_8_s20
import AESMixing.GramCertificates.I_4_8_s21
import AESMixing.GramCertificates.I_4_8_s22
import AESMixing.GramCertificates.I_4_8_s23
import AESMixing.GramCertificates.I_4_8_s24
import AESMixing.AESGramOrientation
open scoped BigOperators
set_option maxRecDepth 1000000
namespace AESMixing.GramPair.I_4_8
-- Exhaustive aggregation: every mode has a unique block and within-block index.
def blockRanks : Fin 25 → Fin 25 → ℕ := ![AESMixing.GramCertificates.I_4_8_s0.ranks, AESMixing.GramCertificates.I_4_8_s1.ranks, AESMixing.GramCertificates.I_4_8_s2.ranks, AESMixing.GramCertificates.I_4_8_s3.ranks, AESMixing.GramCertificates.I_4_8_s4.ranks, AESMixing.GramCertificates.I_4_8_s5.ranks, AESMixing.GramCertificates.I_4_8_s6.ranks, AESMixing.GramCertificates.I_4_8_s7.ranks, AESMixing.GramCertificates.I_4_8_s8.ranks, AESMixing.GramCertificates.I_4_8_s9.ranks, AESMixing.GramCertificates.I_4_8_s10.ranks, AESMixing.GramCertificates.I_4_8_s11.ranks, AESMixing.GramCertificates.I_4_8_s12.ranks, AESMixing.GramCertificates.I_4_8_s13.ranks, AESMixing.GramCertificates.I_4_8_s14.ranks, AESMixing.GramCertificates.I_4_8_s15.ranks, AESMixing.GramCertificates.I_4_8_s16.ranks, AESMixing.GramCertificates.I_4_8_s17.ranks, AESMixing.GramCertificates.I_4_8_s18.ranks, AESMixing.GramCertificates.I_4_8_s19.ranks, AESMixing.GramCertificates.I_4_8_s20.ranks, AESMixing.GramCertificates.I_4_8_s21.ranks, AESMixing.GramCertificates.I_4_8_s22.ranks, AESMixing.GramCertificates.I_4_8_s23.ranks, AESMixing.GramCertificates.I_4_8_s24.ranks]
-- Each hexadecimal digit stores one rank; the least significant digit is mode zero.
def ranks (i : Fin 625) : ℕ :=
  (0x8888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888788888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888887878888888787888888888888888888888888888888888888878788888887878888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888887788877888888888888888888778887788888888888888888888888878888888888888888888888888888888888888787888888878788888888888888888877888778888788888887878887778776 >>> (4*i.val)) % 16
theorem block_counts (b t : Fin 25) : gramCaseCount true 4 8 (gramSubModeIndex b t) =
    256^(8-blockRanks b t) := by
  fin_cases b
  · exact AESMixing.GramCertificates.I_4_8_s0.counts t
  · exact AESMixing.GramCertificates.I_4_8_s1.counts t
  · exact AESMixing.GramCertificates.I_4_8_s2.counts t
  · exact AESMixing.GramCertificates.I_4_8_s3.counts t
  · exact AESMixing.GramCertificates.I_4_8_s4.counts t
  · exact AESMixing.GramCertificates.I_4_8_s5.counts t
  · exact AESMixing.GramCertificates.I_4_8_s6.counts t
  · exact AESMixing.GramCertificates.I_4_8_s7.counts t
  · exact AESMixing.GramCertificates.I_4_8_s8.counts t
  · exact AESMixing.GramCertificates.I_4_8_s9.counts t
  · exact AESMixing.GramCertificates.I_4_8_s10.counts t
  · exact AESMixing.GramCertificates.I_4_8_s11.counts t
  · exact AESMixing.GramCertificates.I_4_8_s12.counts t
  · exact AESMixing.GramCertificates.I_4_8_s13.counts t
  · exact AESMixing.GramCertificates.I_4_8_s14.counts t
  · exact AESMixing.GramCertificates.I_4_8_s15.counts t
  · exact AESMixing.GramCertificates.I_4_8_s16.counts t
  · exact AESMixing.GramCertificates.I_4_8_s17.counts t
  · exact AESMixing.GramCertificates.I_4_8_s18.counts t
  · exact AESMixing.GramCertificates.I_4_8_s19.counts t
  · exact AESMixing.GramCertificates.I_4_8_s20.counts t
  · exact AESMixing.GramCertificates.I_4_8_s21.counts t
  · exact AESMixing.GramCertificates.I_4_8_s22.counts t
  · exact AESMixing.GramCertificates.I_4_8_s23.counts t
  · exact AESMixing.GramCertificates.I_4_8_s24.counts t
set_option maxHeartbeats 0 in
theorem blockRanks_eq (b t : Fin 25) : blockRanks b t = ranks (gramSubModeIndex b t) := by
  revert b t; decide
theorem counts (i : Fin 625) : gramCaseCount true 4 8 i = 256^(8-ranks i) := by
  have h := block_counts (gramSubBlock i) (gramSubWithin i)
  rw [blockRanks_eq, gramSubModeIndex_split] at h
  exact h
def values : Fin 5 → ℤ := ![4228315650, 0, -390150, 520200, -195075]
set_option maxHeartbeats 0 in
theorem numerator_values (j : Fin 5) :
    rankGramNumerator (fun m => ranks (finFunctionFinEquiv m)) j = values j := by
  fin_cases j <;> decide
theorem gram_entries (j : Fin 5) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 4) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 8) y) =
        (values j : ℝ)/255^4 := by
  rw [oriented_activity_gram_from_ranks true j 4 8 ranks counts, numerator_values]
#print axioms counts
#print axioms numerator_values
#print axioms gram_entries
end AESMixing.GramPair.I_4_8
