import AESMixing.GramCertificates.I_5_15_s0
import AESMixing.GramCertificates.I_5_15_s1
import AESMixing.GramCertificates.I_5_15_s2
import AESMixing.GramCertificates.I_5_15_s3
import AESMixing.GramCertificates.I_5_15_s4
import AESMixing.GramCertificates.I_5_15_s5
import AESMixing.GramCertificates.I_5_15_s6
import AESMixing.GramCertificates.I_5_15_s7
import AESMixing.GramCertificates.I_5_15_s8
import AESMixing.GramCertificates.I_5_15_s9
import AESMixing.GramCertificates.I_5_15_s10
import AESMixing.GramCertificates.I_5_15_s11
import AESMixing.GramCertificates.I_5_15_s12
import AESMixing.GramCertificates.I_5_15_s13
import AESMixing.GramCertificates.I_5_15_s14
import AESMixing.GramCertificates.I_5_15_s15
import AESMixing.GramCertificates.I_5_15_s16
import AESMixing.GramCertificates.I_5_15_s17
import AESMixing.GramCertificates.I_5_15_s18
import AESMixing.GramCertificates.I_5_15_s19
import AESMixing.GramCertificates.I_5_15_s20
import AESMixing.GramCertificates.I_5_15_s21
import AESMixing.GramCertificates.I_5_15_s22
import AESMixing.GramCertificates.I_5_15_s23
import AESMixing.GramCertificates.I_5_15_s24
import AESMixing.AESGramOrientation
open scoped BigOperators
set_option maxRecDepth 1000000
namespace AESMixing.GramPair.I_5_15
-- Exhaustive aggregation: every mode has a unique block and within-block index.
def blockRanks : Fin 25 → Fin 25 → ℕ := ![AESMixing.GramCertificates.I_5_15_s0.ranks, AESMixing.GramCertificates.I_5_15_s1.ranks, AESMixing.GramCertificates.I_5_15_s2.ranks, AESMixing.GramCertificates.I_5_15_s3.ranks, AESMixing.GramCertificates.I_5_15_s4.ranks, AESMixing.GramCertificates.I_5_15_s5.ranks, AESMixing.GramCertificates.I_5_15_s6.ranks, AESMixing.GramCertificates.I_5_15_s7.ranks, AESMixing.GramCertificates.I_5_15_s8.ranks, AESMixing.GramCertificates.I_5_15_s9.ranks, AESMixing.GramCertificates.I_5_15_s10.ranks, AESMixing.GramCertificates.I_5_15_s11.ranks, AESMixing.GramCertificates.I_5_15_s12.ranks, AESMixing.GramCertificates.I_5_15_s13.ranks, AESMixing.GramCertificates.I_5_15_s14.ranks, AESMixing.GramCertificates.I_5_15_s15.ranks, AESMixing.GramCertificates.I_5_15_s16.ranks, AESMixing.GramCertificates.I_5_15_s17.ranks, AESMixing.GramCertificates.I_5_15_s18.ranks, AESMixing.GramCertificates.I_5_15_s19.ranks, AESMixing.GramCertificates.I_5_15_s20.ranks, AESMixing.GramCertificates.I_5_15_s21.ranks, AESMixing.GramCertificates.I_5_15_s22.ranks, AESMixing.GramCertificates.I_5_15_s23.ranks, AESMixing.GramCertificates.I_5_15_s24.ranks]
-- Each hexadecimal digit stores one rank; the least significant digit is mode zero.
def ranks (i : Fin 625) : ℕ :=
  (0x6766578776676656766556554787768887778776777666766567665787766766567665565546766577766676656665556554565546766556554565544544378776888777877677766676658887788877888777776677766787768887778776777666766577766777667776666655666556766577766676656665556554676657877667665676655655478776888777877677766676656766578776676656766556554676657776667665666555655456554676655655456554454436766577766676656665556554777667776677766666556665567665777666766566655565546665566655666555554455544565546665556554555444544356554676655655456554454436766577766676656665556554565546766556554565544544356554666555655455544454434544356554454434544334332 >>> (4*i.val)) % 16
theorem block_counts (b t : Fin 25) : gramCaseCount true 5 15 (gramSubModeIndex b t) =
    256^(8-blockRanks b t) := by
  fin_cases b
  · exact AESMixing.GramCertificates.I_5_15_s0.counts t
  · exact AESMixing.GramCertificates.I_5_15_s1.counts t
  · exact AESMixing.GramCertificates.I_5_15_s2.counts t
  · exact AESMixing.GramCertificates.I_5_15_s3.counts t
  · exact AESMixing.GramCertificates.I_5_15_s4.counts t
  · exact AESMixing.GramCertificates.I_5_15_s5.counts t
  · exact AESMixing.GramCertificates.I_5_15_s6.counts t
  · exact AESMixing.GramCertificates.I_5_15_s7.counts t
  · exact AESMixing.GramCertificates.I_5_15_s8.counts t
  · exact AESMixing.GramCertificates.I_5_15_s9.counts t
  · exact AESMixing.GramCertificates.I_5_15_s10.counts t
  · exact AESMixing.GramCertificates.I_5_15_s11.counts t
  · exact AESMixing.GramCertificates.I_5_15_s12.counts t
  · exact AESMixing.GramCertificates.I_5_15_s13.counts t
  · exact AESMixing.GramCertificates.I_5_15_s14.counts t
  · exact AESMixing.GramCertificates.I_5_15_s15.counts t
  · exact AESMixing.GramCertificates.I_5_15_s16.counts t
  · exact AESMixing.GramCertificates.I_5_15_s17.counts t
  · exact AESMixing.GramCertificates.I_5_15_s18.counts t
  · exact AESMixing.GramCertificates.I_5_15_s19.counts t
  · exact AESMixing.GramCertificates.I_5_15_s20.counts t
  · exact AESMixing.GramCertificates.I_5_15_s21.counts t
  · exact AESMixing.GramCertificates.I_5_15_s22.counts t
  · exact AESMixing.GramCertificates.I_5_15_s23.counts t
  · exact AESMixing.GramCertificates.I_5_15_s24.counts t
set_option maxHeartbeats 0 in
theorem blockRanks_eq (b t : Fin 25) : blockRanks b t = ranks (gramSubModeIndex b t) := by
  revert b t; decide
theorem counts (i : Fin 625) : gramCaseCount true 5 15 i = 256^(8-ranks i) := by
  have h := block_counts (gramSubBlock i) (gramSubWithin i)
  rw [blockRanks_eq, gramSubModeIndex_split] at h
  exact h
def values : Fin 5 → ℤ := ![277102632960000, 0, 0, 0, 0]
set_option maxHeartbeats 0 in
theorem numerator_values (j : Fin 5) :
    rankGramNumerator (fun m => ranks (finFunctionFinEquiv m)) j = values j := by
  fin_cases j <;> decide
theorem gram_entries (j : Fin 5) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 5) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 15) y) =
        (values j : ℝ)/255^4 := by
  rw [oriented_activity_gram_from_ranks true j 5 15 ranks counts, numerator_values]
#print axioms counts
#print axioms numerator_values
#print axioms gram_entries
end AESMixing.GramPair.I_5_15
