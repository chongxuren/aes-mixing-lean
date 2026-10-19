import AESMixing.Generated.GramAggregate_I_9_0
import AESMixing.Generated.GramAggregate_I_9_1
import AESMixing.Generated.GramAggregate_I_9_2
import AESMixing.Generated.GramAggregate_I_9_3
import AESMixing.Generated.GramAggregate_I_9_4
import AESMixing.Generated.GramAggregate_I_9_5
import AESMixing.Generated.GramAggregate_I_9_6
import AESMixing.Generated.GramAggregate_I_9_7
import AESMixing.Generated.GramAggregate_I_9_8
import AESMixing.Generated.GramAggregate_I_9_9
import AESMixing.Generated.GramAggregate_I_9_10
import AESMixing.Generated.GramAggregate_I_9_11
import AESMixing.Generated.GramAggregate_I_9_12
import AESMixing.Generated.GramAggregate_I_9_13
import AESMixing.Generated.GramAggregate_I_9_14
import AESMixing.Generated.GramAggregate_I_9_15
open scoped BigOperators
namespace AESMixing.GramRow.I_9
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_9_0.values, AESMixing.GramPair.I_9_1.values, AESMixing.GramPair.I_9_2.values, AESMixing.GramPair.I_9_3.values, AESMixing.GramPair.I_9_4.values, AESMixing.GramPair.I_9_5.values, AESMixing.GramPair.I_9_6.values, AESMixing.GramPair.I_9_7.values, AESMixing.GramPair.I_9_8.values, AESMixing.GramPair.I_9_9.values, AESMixing.GramPair.I_9_10.values, AESMixing.GramPair.I_9_11.values, AESMixing.GramPair.I_9_12.values, AESMixing.GramPair.I_9_13.values, AESMixing.GramPair.I_9_14.values, AESMixing.GramPair.I_9_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 9) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_9_0.gram_entries j
  · exact AESMixing.GramPair.I_9_1.gram_entries j
  · exact AESMixing.GramPair.I_9_2.gram_entries j
  · exact AESMixing.GramPair.I_9_3.gram_entries j
  · exact AESMixing.GramPair.I_9_4.gram_entries j
  · exact AESMixing.GramPair.I_9_5.gram_entries j
  · exact AESMixing.GramPair.I_9_6.gram_entries j
  · exact AESMixing.GramPair.I_9_7.gram_entries j
  · exact AESMixing.GramPair.I_9_8.gram_entries j
  · exact AESMixing.GramPair.I_9_9.gram_entries j
  · exact AESMixing.GramPair.I_9_10.gram_entries j
  · exact AESMixing.GramPair.I_9_11.gram_entries j
  · exact AESMixing.GramPair.I_9_12.gram_entries j
  · exact AESMixing.GramPair.I_9_13.gram_entries j
  · exact AESMixing.GramPair.I_9_14.gram_entries j
  · exact AESMixing.GramPair.I_9_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_9
