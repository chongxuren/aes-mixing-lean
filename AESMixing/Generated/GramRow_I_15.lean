import AESMixing.Generated.GramAggregate_I_15_0
import AESMixing.Generated.GramAggregate_I_15_1
import AESMixing.Generated.GramAggregate_I_15_2
import AESMixing.Generated.GramAggregate_I_15_3
import AESMixing.Generated.GramAggregate_I_15_4
import AESMixing.Generated.GramAggregate_I_15_5
import AESMixing.Generated.GramAggregate_I_15_6
import AESMixing.Generated.GramAggregate_I_15_7
import AESMixing.Generated.GramAggregate_I_15_8
import AESMixing.Generated.GramAggregate_I_15_9
import AESMixing.Generated.GramAggregate_I_15_10
import AESMixing.Generated.GramAggregate_I_15_11
import AESMixing.Generated.GramAggregate_I_15_12
import AESMixing.Generated.GramAggregate_I_15_13
import AESMixing.Generated.GramAggregate_I_15_14
import AESMixing.Generated.GramAggregate_I_15_15
open scoped BigOperators
namespace AESMixing.GramRow.I_15
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_15_0.values, AESMixing.GramPair.I_15_1.values, AESMixing.GramPair.I_15_2.values, AESMixing.GramPair.I_15_3.values, AESMixing.GramPair.I_15_4.values, AESMixing.GramPair.I_15_5.values, AESMixing.GramPair.I_15_6.values, AESMixing.GramPair.I_15_7.values, AESMixing.GramPair.I_15_8.values, AESMixing.GramPair.I_15_9.values, AESMixing.GramPair.I_15_10.values, AESMixing.GramPair.I_15_11.values, AESMixing.GramPair.I_15_12.values, AESMixing.GramPair.I_15_13.values, AESMixing.GramPair.I_15_14.values, AESMixing.GramPair.I_15_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 15) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_15_0.gram_entries j
  · exact AESMixing.GramPair.I_15_1.gram_entries j
  · exact AESMixing.GramPair.I_15_2.gram_entries j
  · exact AESMixing.GramPair.I_15_3.gram_entries j
  · exact AESMixing.GramPair.I_15_4.gram_entries j
  · exact AESMixing.GramPair.I_15_5.gram_entries j
  · exact AESMixing.GramPair.I_15_6.gram_entries j
  · exact AESMixing.GramPair.I_15_7.gram_entries j
  · exact AESMixing.GramPair.I_15_8.gram_entries j
  · exact AESMixing.GramPair.I_15_9.gram_entries j
  · exact AESMixing.GramPair.I_15_10.gram_entries j
  · exact AESMixing.GramPair.I_15_11.gram_entries j
  · exact AESMixing.GramPair.I_15_12.gram_entries j
  · exact AESMixing.GramPair.I_15_13.gram_entries j
  · exact AESMixing.GramPair.I_15_14.gram_entries j
  · exact AESMixing.GramPair.I_15_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_15
