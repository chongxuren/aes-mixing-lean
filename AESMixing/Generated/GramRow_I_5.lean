import AESMixing.Generated.GramAggregate_I_5_0
import AESMixing.Generated.GramAggregate_I_5_1
import AESMixing.Generated.GramAggregate_I_5_2
import AESMixing.Generated.GramAggregate_I_5_3
import AESMixing.Generated.GramAggregate_I_5_4
import AESMixing.Generated.GramAggregate_I_5_5
import AESMixing.Generated.GramAggregate_I_5_6
import AESMixing.Generated.GramAggregate_I_5_7
import AESMixing.Generated.GramAggregate_I_5_8
import AESMixing.Generated.GramAggregate_I_5_9
import AESMixing.Generated.GramAggregate_I_5_10
import AESMixing.Generated.GramAggregate_I_5_11
import AESMixing.Generated.GramAggregate_I_5_12
import AESMixing.Generated.GramAggregate_I_5_13
import AESMixing.Generated.GramAggregate_I_5_14
import AESMixing.Generated.GramAggregate_I_5_15
open scoped BigOperators
namespace AESMixing.GramRow.I_5
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_5_0.values, AESMixing.GramPair.I_5_1.values, AESMixing.GramPair.I_5_2.values, AESMixing.GramPair.I_5_3.values, AESMixing.GramPair.I_5_4.values, AESMixing.GramPair.I_5_5.values, AESMixing.GramPair.I_5_6.values, AESMixing.GramPair.I_5_7.values, AESMixing.GramPair.I_5_8.values, AESMixing.GramPair.I_5_9.values, AESMixing.GramPair.I_5_10.values, AESMixing.GramPair.I_5_11.values, AESMixing.GramPair.I_5_12.values, AESMixing.GramPair.I_5_13.values, AESMixing.GramPair.I_5_14.values, AESMixing.GramPair.I_5_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 5) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_5_0.gram_entries j
  · exact AESMixing.GramPair.I_5_1.gram_entries j
  · exact AESMixing.GramPair.I_5_2.gram_entries j
  · exact AESMixing.GramPair.I_5_3.gram_entries j
  · exact AESMixing.GramPair.I_5_4.gram_entries j
  · exact AESMixing.GramPair.I_5_5.gram_entries j
  · exact AESMixing.GramPair.I_5_6.gram_entries j
  · exact AESMixing.GramPair.I_5_7.gram_entries j
  · exact AESMixing.GramPair.I_5_8.gram_entries j
  · exact AESMixing.GramPair.I_5_9.gram_entries j
  · exact AESMixing.GramPair.I_5_10.gram_entries j
  · exact AESMixing.GramPair.I_5_11.gram_entries j
  · exact AESMixing.GramPair.I_5_12.gram_entries j
  · exact AESMixing.GramPair.I_5_13.gram_entries j
  · exact AESMixing.GramPair.I_5_14.gram_entries j
  · exact AESMixing.GramPair.I_5_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_5
