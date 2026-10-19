import AESMixing.Generated.GramRow_F_0
import AESMixing.Generated.GramRow_F_1
import AESMixing.Generated.GramRow_F_2
import AESMixing.Generated.GramRow_F_3
import AESMixing.Generated.GramRow_F_4
import AESMixing.Generated.GramRow_F_5
import AESMixing.Generated.GramRow_F_6
import AESMixing.Generated.GramRow_F_7
import AESMixing.Generated.GramRow_F_8
import AESMixing.Generated.GramRow_F_9
import AESMixing.Generated.GramRow_F_10
import AESMixing.Generated.GramRow_F_11
import AESMixing.Generated.GramRow_F_12
import AESMixing.Generated.GramRow_F_13
import AESMixing.Generated.GramRow_F_14
import AESMixing.Generated.GramRow_F_15
import AESMixing.Generated.GramLDL_F0
import AESMixing.Generated.GramLDL_F2
import AESMixing.Generated.GramLDL_F3
open scoped BigOperators
namespace AESMixing.GramTable.F
def values : Fin 16 → Fin 16 → Fin 5 → ℤ := ![AESMixing.GramRow.F_0.values, AESMixing.GramRow.F_1.values, AESMixing.GramRow.F_2.values, AESMixing.GramRow.F_3.values, AESMixing.GramRow.F_4.values, AESMixing.GramRow.F_5.values, AESMixing.GramRow.F_6.values, AESMixing.GramRow.F_7.values, AESMixing.GramRow.F_8.values, AESMixing.GramRow.F_9.values, AESMixing.GramRow.F_10.values, AESMixing.GramRow.F_11.values, AESMixing.GramRow.F_12.values, AESMixing.GramRow.F_13.values, AESMixing.GramRow.F_14.values, AESMixing.GramRow.F_15.values]
theorem gram_entries (j : Fin 5) (a b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) a) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) b) y) =
        (values a b j : ℝ) / 255^4 := by
  fin_cases a
  · exact AESMixing.GramRow.F_0.gram_entries j b
  · exact AESMixing.GramRow.F_1.gram_entries j b
  · exact AESMixing.GramRow.F_2.gram_entries j b
  · exact AESMixing.GramRow.F_3.gram_entries j b
  · exact AESMixing.GramRow.F_4.gram_entries j b
  · exact AESMixing.GramRow.F_5.gram_entries j b
  · exact AESMixing.GramRow.F_6.gram_entries j b
  · exact AESMixing.GramRow.F_7.gram_entries j b
  · exact AESMixing.GramRow.F_8.gram_entries j b
  · exact AESMixing.GramRow.F_9.gram_entries j b
  · exact AESMixing.GramRow.F_10.gram_entries j b
  · exact AESMixing.GramRow.F_11.gram_entries j b
  · exact AESMixing.GramRow.F_12.gram_entries j b
  · exact AESMixing.GramRow.F_13.gram_entries j b
  · exact AESMixing.GramRow.F_14.gram_entries j b
  · exact AESMixing.GramRow.F_15.gram_entries j b
theorem values_0 (a b : Fin 16) :
    values a b 0 = AESMixing.GramNumeric.F0.numerator a b := by
  fin_cases a <;> fin_cases b <;> rfl
theorem numeric_entries_0 (a b : Fin 16) :
    gram (fun y a => degreeComponent 0 0 (diffusedActivityColumn (byteDiffusionOrientation false) a) y) a b =
      (AESMixing.GramNumeric.F0.numerator a b : ℝ) / 255^4 := by
  have h := gram_entries 0 a b
  rw [values_0] at h
  exact h
#print axioms numeric_entries_0
theorem values_2 (a b : Fin 16) :
    values a b 2 = AESMixing.GramNumeric.F2.numerator a b := by
  fin_cases a <;> fin_cases b <;> rfl
theorem numeric_entries_2 (a b : Fin 16) :
    gram (fun y a => degreeComponent 0 2 (diffusedActivityColumn (byteDiffusionOrientation false) a) y) a b =
      (AESMixing.GramNumeric.F2.numerator a b : ℝ) / 255^4 := by
  have h := gram_entries 2 a b
  rw [values_2] at h
  exact h
#print axioms numeric_entries_2
theorem values_3 (a b : Fin 16) :
    values a b 3 = AESMixing.GramNumeric.F3.numerator a b := by
  fin_cases a <;> fin_cases b <;> rfl
theorem numeric_entries_3 (a b : Fin 16) :
    gram (fun y a => degreeComponent 0 3 (diffusedActivityColumn (byteDiffusionOrientation false) a) y) a b =
      (AESMixing.GramNumeric.F3.numerator a b : ℝ) / 255^4 := by
  have h := gram_entries 3 a b
  rw [values_3] at h
  exact h
#print axioms numeric_entries_3
theorem degree_one_zero (a b : Fin 16) : values a b 1 = 0 := by
  fin_cases a <;> fin_cases b <;> rfl
#print axioms gram_entries
#print axioms degree_one_zero
end AESMixing.GramTable.F
