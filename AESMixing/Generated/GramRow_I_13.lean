import AESMixing.Generated.GramAggregate_I_13_0
import AESMixing.Generated.GramAggregate_I_13_1
import AESMixing.Generated.GramAggregate_I_13_2
import AESMixing.Generated.GramAggregate_I_13_3
import AESMixing.Generated.GramAggregate_I_13_4
import AESMixing.Generated.GramAggregate_I_13_5
import AESMixing.Generated.GramAggregate_I_13_6
import AESMixing.Generated.GramAggregate_I_13_7
import AESMixing.Generated.GramAggregate_I_13_8
import AESMixing.Generated.GramAggregate_I_13_9
import AESMixing.Generated.GramAggregate_I_13_10
import AESMixing.Generated.GramAggregate_I_13_11
import AESMixing.Generated.GramAggregate_I_13_12
import AESMixing.Generated.GramAggregate_I_13_13
import AESMixing.Generated.GramAggregate_I_13_14
import AESMixing.Generated.GramAggregate_I_13_15
open scoped BigOperators
namespace AESMixing.GramRow.I_13
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_13_0.values, AESMixing.GramPair.I_13_1.values, AESMixing.GramPair.I_13_2.values, AESMixing.GramPair.I_13_3.values, AESMixing.GramPair.I_13_4.values, AESMixing.GramPair.I_13_5.values, AESMixing.GramPair.I_13_6.values, AESMixing.GramPair.I_13_7.values, AESMixing.GramPair.I_13_8.values, AESMixing.GramPair.I_13_9.values, AESMixing.GramPair.I_13_10.values, AESMixing.GramPair.I_13_11.values, AESMixing.GramPair.I_13_12.values, AESMixing.GramPair.I_13_13.values, AESMixing.GramPair.I_13_14.values, AESMixing.GramPair.I_13_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 13) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_13_0.gram_entries j
  · exact AESMixing.GramPair.I_13_1.gram_entries j
  · exact AESMixing.GramPair.I_13_2.gram_entries j
  · exact AESMixing.GramPair.I_13_3.gram_entries j
  · exact AESMixing.GramPair.I_13_4.gram_entries j
  · exact AESMixing.GramPair.I_13_5.gram_entries j
  · exact AESMixing.GramPair.I_13_6.gram_entries j
  · exact AESMixing.GramPair.I_13_7.gram_entries j
  · exact AESMixing.GramPair.I_13_8.gram_entries j
  · exact AESMixing.GramPair.I_13_9.gram_entries j
  · exact AESMixing.GramPair.I_13_10.gram_entries j
  · exact AESMixing.GramPair.I_13_11.gram_entries j
  · exact AESMixing.GramPair.I_13_12.gram_entries j
  · exact AESMixing.GramPair.I_13_13.gram_entries j
  · exact AESMixing.GramPair.I_13_14.gram_entries j
  · exact AESMixing.GramPair.I_13_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_13
