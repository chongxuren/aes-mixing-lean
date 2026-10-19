import AESMixing.Generated.GramAggregate_I_1_0
import AESMixing.Generated.GramAggregate_I_1_1
import AESMixing.Generated.GramAggregate_I_1_2
import AESMixing.Generated.GramAggregate_I_1_3
import AESMixing.Generated.GramAggregate_I_1_4
import AESMixing.Generated.GramAggregate_I_1_5
import AESMixing.Generated.GramAggregate_I_1_6
import AESMixing.Generated.GramAggregate_I_1_7
import AESMixing.Generated.GramAggregate_I_1_8
import AESMixing.Generated.GramAggregate_I_1_9
import AESMixing.Generated.GramAggregate_I_1_10
import AESMixing.Generated.GramAggregate_I_1_11
import AESMixing.Generated.GramAggregate_I_1_12
import AESMixing.Generated.GramAggregate_I_1_13
import AESMixing.Generated.GramAggregate_I_1_14
import AESMixing.Generated.GramAggregate_I_1_15
open scoped BigOperators
namespace AESMixing.GramRow.I_1
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_1_0.values, AESMixing.GramPair.I_1_1.values, AESMixing.GramPair.I_1_2.values, AESMixing.GramPair.I_1_3.values, AESMixing.GramPair.I_1_4.values, AESMixing.GramPair.I_1_5.values, AESMixing.GramPair.I_1_6.values, AESMixing.GramPair.I_1_7.values, AESMixing.GramPair.I_1_8.values, AESMixing.GramPair.I_1_9.values, AESMixing.GramPair.I_1_10.values, AESMixing.GramPair.I_1_11.values, AESMixing.GramPair.I_1_12.values, AESMixing.GramPair.I_1_13.values, AESMixing.GramPair.I_1_14.values, AESMixing.GramPair.I_1_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 1) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_1_0.gram_entries j
  · exact AESMixing.GramPair.I_1_1.gram_entries j
  · exact AESMixing.GramPair.I_1_2.gram_entries j
  · exact AESMixing.GramPair.I_1_3.gram_entries j
  · exact AESMixing.GramPair.I_1_4.gram_entries j
  · exact AESMixing.GramPair.I_1_5.gram_entries j
  · exact AESMixing.GramPair.I_1_6.gram_entries j
  · exact AESMixing.GramPair.I_1_7.gram_entries j
  · exact AESMixing.GramPair.I_1_8.gram_entries j
  · exact AESMixing.GramPair.I_1_9.gram_entries j
  · exact AESMixing.GramPair.I_1_10.gram_entries j
  · exact AESMixing.GramPair.I_1_11.gram_entries j
  · exact AESMixing.GramPair.I_1_12.gram_entries j
  · exact AESMixing.GramPair.I_1_13.gram_entries j
  · exact AESMixing.GramPair.I_1_14.gram_entries j
  · exact AESMixing.GramPair.I_1_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_1
