import AESMixing.Generated.GramAggregate_I_10_0
import AESMixing.Generated.GramAggregate_I_10_1
import AESMixing.Generated.GramAggregate_I_10_2
import AESMixing.Generated.GramAggregate_I_10_3
import AESMixing.Generated.GramAggregate_I_10_4
import AESMixing.Generated.GramAggregate_I_10_5
import AESMixing.Generated.GramAggregate_I_10_6
import AESMixing.Generated.GramAggregate_I_10_7
import AESMixing.Generated.GramAggregate_I_10_8
import AESMixing.Generated.GramAggregate_I_10_9
import AESMixing.Generated.GramAggregate_I_10_10
import AESMixing.Generated.GramAggregate_I_10_11
import AESMixing.Generated.GramAggregate_I_10_12
import AESMixing.Generated.GramAggregate_I_10_13
import AESMixing.Generated.GramAggregate_I_10_14
import AESMixing.Generated.GramAggregate_I_10_15
open scoped BigOperators
namespace AESMixing.GramRow.I_10
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_10_0.values, AESMixing.GramPair.I_10_1.values, AESMixing.GramPair.I_10_2.values, AESMixing.GramPair.I_10_3.values, AESMixing.GramPair.I_10_4.values, AESMixing.GramPair.I_10_5.values, AESMixing.GramPair.I_10_6.values, AESMixing.GramPair.I_10_7.values, AESMixing.GramPair.I_10_8.values, AESMixing.GramPair.I_10_9.values, AESMixing.GramPair.I_10_10.values, AESMixing.GramPair.I_10_11.values, AESMixing.GramPair.I_10_12.values, AESMixing.GramPair.I_10_13.values, AESMixing.GramPair.I_10_14.values, AESMixing.GramPair.I_10_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 10) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_10_0.gram_entries j
  · exact AESMixing.GramPair.I_10_1.gram_entries j
  · exact AESMixing.GramPair.I_10_2.gram_entries j
  · exact AESMixing.GramPair.I_10_3.gram_entries j
  · exact AESMixing.GramPair.I_10_4.gram_entries j
  · exact AESMixing.GramPair.I_10_5.gram_entries j
  · exact AESMixing.GramPair.I_10_6.gram_entries j
  · exact AESMixing.GramPair.I_10_7.gram_entries j
  · exact AESMixing.GramPair.I_10_8.gram_entries j
  · exact AESMixing.GramPair.I_10_9.gram_entries j
  · exact AESMixing.GramPair.I_10_10.gram_entries j
  · exact AESMixing.GramPair.I_10_11.gram_entries j
  · exact AESMixing.GramPair.I_10_12.gram_entries j
  · exact AESMixing.GramPair.I_10_13.gram_entries j
  · exact AESMixing.GramPair.I_10_14.gram_entries j
  · exact AESMixing.GramPair.I_10_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_10
