import AESMixing.Generated.GramAggregate_I_7_0
import AESMixing.Generated.GramAggregate_I_7_1
import AESMixing.Generated.GramAggregate_I_7_2
import AESMixing.Generated.GramAggregate_I_7_3
import AESMixing.Generated.GramAggregate_I_7_4
import AESMixing.Generated.GramAggregate_I_7_5
import AESMixing.Generated.GramAggregate_I_7_6
import AESMixing.Generated.GramAggregate_I_7_7
import AESMixing.Generated.GramAggregate_I_7_8
import AESMixing.Generated.GramAggregate_I_7_9
import AESMixing.Generated.GramAggregate_I_7_10
import AESMixing.Generated.GramAggregate_I_7_11
import AESMixing.Generated.GramAggregate_I_7_12
import AESMixing.Generated.GramAggregate_I_7_13
import AESMixing.Generated.GramAggregate_I_7_14
import AESMixing.Generated.GramAggregate_I_7_15
open scoped BigOperators
namespace AESMixing.GramRow.I_7
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_7_0.values, AESMixing.GramPair.I_7_1.values, AESMixing.GramPair.I_7_2.values, AESMixing.GramPair.I_7_3.values, AESMixing.GramPair.I_7_4.values, AESMixing.GramPair.I_7_5.values, AESMixing.GramPair.I_7_6.values, AESMixing.GramPair.I_7_7.values, AESMixing.GramPair.I_7_8.values, AESMixing.GramPair.I_7_9.values, AESMixing.GramPair.I_7_10.values, AESMixing.GramPair.I_7_11.values, AESMixing.GramPair.I_7_12.values, AESMixing.GramPair.I_7_13.values, AESMixing.GramPair.I_7_14.values, AESMixing.GramPair.I_7_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 7) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_7_0.gram_entries j
  · exact AESMixing.GramPair.I_7_1.gram_entries j
  · exact AESMixing.GramPair.I_7_2.gram_entries j
  · exact AESMixing.GramPair.I_7_3.gram_entries j
  · exact AESMixing.GramPair.I_7_4.gram_entries j
  · exact AESMixing.GramPair.I_7_5.gram_entries j
  · exact AESMixing.GramPair.I_7_6.gram_entries j
  · exact AESMixing.GramPair.I_7_7.gram_entries j
  · exact AESMixing.GramPair.I_7_8.gram_entries j
  · exact AESMixing.GramPair.I_7_9.gram_entries j
  · exact AESMixing.GramPair.I_7_10.gram_entries j
  · exact AESMixing.GramPair.I_7_11.gram_entries j
  · exact AESMixing.GramPair.I_7_12.gram_entries j
  · exact AESMixing.GramPair.I_7_13.gram_entries j
  · exact AESMixing.GramPair.I_7_14.gram_entries j
  · exact AESMixing.GramPair.I_7_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_7
