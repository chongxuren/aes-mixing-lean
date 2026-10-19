import AESMixing.Generated.GramAggregate_I_14_0
import AESMixing.Generated.GramAggregate_I_14_1
import AESMixing.Generated.GramAggregate_I_14_2
import AESMixing.Generated.GramAggregate_I_14_3
import AESMixing.Generated.GramAggregate_I_14_4
import AESMixing.Generated.GramAggregate_I_14_5
import AESMixing.Generated.GramAggregate_I_14_6
import AESMixing.Generated.GramAggregate_I_14_7
import AESMixing.Generated.GramAggregate_I_14_8
import AESMixing.Generated.GramAggregate_I_14_9
import AESMixing.Generated.GramAggregate_I_14_10
import AESMixing.Generated.GramAggregate_I_14_11
import AESMixing.Generated.GramAggregate_I_14_12
import AESMixing.Generated.GramAggregate_I_14_13
import AESMixing.Generated.GramAggregate_I_14_14
import AESMixing.Generated.GramAggregate_I_14_15
open scoped BigOperators
namespace AESMixing.GramRow.I_14
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_14_0.values, AESMixing.GramPair.I_14_1.values, AESMixing.GramPair.I_14_2.values, AESMixing.GramPair.I_14_3.values, AESMixing.GramPair.I_14_4.values, AESMixing.GramPair.I_14_5.values, AESMixing.GramPair.I_14_6.values, AESMixing.GramPair.I_14_7.values, AESMixing.GramPair.I_14_8.values, AESMixing.GramPair.I_14_9.values, AESMixing.GramPair.I_14_10.values, AESMixing.GramPair.I_14_11.values, AESMixing.GramPair.I_14_12.values, AESMixing.GramPair.I_14_13.values, AESMixing.GramPair.I_14_14.values, AESMixing.GramPair.I_14_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 14) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_14_0.gram_entries j
  · exact AESMixing.GramPair.I_14_1.gram_entries j
  · exact AESMixing.GramPair.I_14_2.gram_entries j
  · exact AESMixing.GramPair.I_14_3.gram_entries j
  · exact AESMixing.GramPair.I_14_4.gram_entries j
  · exact AESMixing.GramPair.I_14_5.gram_entries j
  · exact AESMixing.GramPair.I_14_6.gram_entries j
  · exact AESMixing.GramPair.I_14_7.gram_entries j
  · exact AESMixing.GramPair.I_14_8.gram_entries j
  · exact AESMixing.GramPair.I_14_9.gram_entries j
  · exact AESMixing.GramPair.I_14_10.gram_entries j
  · exact AESMixing.GramPair.I_14_11.gram_entries j
  · exact AESMixing.GramPair.I_14_12.gram_entries j
  · exact AESMixing.GramPair.I_14_13.gram_entries j
  · exact AESMixing.GramPair.I_14_14.gram_entries j
  · exact AESMixing.GramPair.I_14_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_14
