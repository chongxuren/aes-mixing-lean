import AESMixing.Generated.GramRow_I_0
import AESMixing.Generated.GramRow_I_1
import AESMixing.Generated.GramRow_I_2
import AESMixing.Generated.GramRow_I_3
import AESMixing.Generated.GramRow_I_4
import AESMixing.Generated.GramRow_I_5
import AESMixing.Generated.GramRow_I_6
import AESMixing.Generated.GramRow_I_7
import AESMixing.Generated.GramRow_I_8
import AESMixing.Generated.GramRow_I_9
import AESMixing.Generated.GramRow_I_10
import AESMixing.Generated.GramRow_I_11
import AESMixing.Generated.GramRow_I_12
import AESMixing.Generated.GramRow_I_13
import AESMixing.Generated.GramRow_I_14
import AESMixing.Generated.GramRow_I_15
import AESMixing.Generated.GramLDL_I0
import AESMixing.Generated.GramLDL_I2
import AESMixing.Generated.GramLDL_I3
open scoped BigOperators
namespace AESMixing.GramTable.I
def values : Fin 16 → Fin 16 → Fin 5 → ℤ := ![AESMixing.GramRow.I_0.values, AESMixing.GramRow.I_1.values, AESMixing.GramRow.I_2.values, AESMixing.GramRow.I_3.values, AESMixing.GramRow.I_4.values, AESMixing.GramRow.I_5.values, AESMixing.GramRow.I_6.values, AESMixing.GramRow.I_7.values, AESMixing.GramRow.I_8.values, AESMixing.GramRow.I_9.values, AESMixing.GramRow.I_10.values, AESMixing.GramRow.I_11.values, AESMixing.GramRow.I_12.values, AESMixing.GramRow.I_13.values, AESMixing.GramRow.I_14.values, AESMixing.GramRow.I_15.values]
theorem gram_entries (j : Fin 5) (a b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) a) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values a b j : ℝ) / 255^4 := by
  fin_cases a
  · exact AESMixing.GramRow.I_0.gram_entries j b
  · exact AESMixing.GramRow.I_1.gram_entries j b
  · exact AESMixing.GramRow.I_2.gram_entries j b
  · exact AESMixing.GramRow.I_3.gram_entries j b
  · exact AESMixing.GramRow.I_4.gram_entries j b
  · exact AESMixing.GramRow.I_5.gram_entries j b
  · exact AESMixing.GramRow.I_6.gram_entries j b
  · exact AESMixing.GramRow.I_7.gram_entries j b
  · exact AESMixing.GramRow.I_8.gram_entries j b
  · exact AESMixing.GramRow.I_9.gram_entries j b
  · exact AESMixing.GramRow.I_10.gram_entries j b
  · exact AESMixing.GramRow.I_11.gram_entries j b
  · exact AESMixing.GramRow.I_12.gram_entries j b
  · exact AESMixing.GramRow.I_13.gram_entries j b
  · exact AESMixing.GramRow.I_14.gram_entries j b
  · exact AESMixing.GramRow.I_15.gram_entries j b
theorem values_0 (a b : Fin 16) :
    values a b 0 = AESMixing.GramNumeric.I0.numerator a b := by
  fin_cases a <;> fin_cases b <;> rfl
theorem numeric_entries_0 (a b : Fin 16) :
    gram (fun y a => degreeComponent 0 0 (diffusedActivityColumn (byteDiffusionOrientation true) a) y) a b =
      (AESMixing.GramNumeric.I0.numerator a b : ℝ) / 255^4 := by
  have h := gram_entries 0 a b
  rw [values_0] at h
  exact h
#print axioms numeric_entries_0
theorem values_2 (a b : Fin 16) :
    values a b 2 = AESMixing.GramNumeric.I2.numerator a b := by
  fin_cases a <;> fin_cases b <;> rfl
theorem numeric_entries_2 (a b : Fin 16) :
    gram (fun y a => degreeComponent 0 2 (diffusedActivityColumn (byteDiffusionOrientation true) a) y) a b =
      (AESMixing.GramNumeric.I2.numerator a b : ℝ) / 255^4 := by
  have h := gram_entries 2 a b
  rw [values_2] at h
  exact h
#print axioms numeric_entries_2
theorem values_3 (a b : Fin 16) :
    values a b 3 = AESMixing.GramNumeric.I3.numerator a b := by
  fin_cases a <;> fin_cases b <;> rfl
theorem numeric_entries_3 (a b : Fin 16) :
    gram (fun y a => degreeComponent 0 3 (diffusedActivityColumn (byteDiffusionOrientation true) a) y) a b =
      (AESMixing.GramNumeric.I3.numerator a b : ℝ) / 255^4 := by
  have h := gram_entries 3 a b
  rw [values_3] at h
  exact h
#print axioms numeric_entries_3
theorem degree_one_zero (a b : Fin 16) : values a b 1 = 0 := by
  fin_cases a <;> fin_cases b <;> rfl
#print axioms gram_entries
#print axioms degree_one_zero
end AESMixing.GramTable.I
