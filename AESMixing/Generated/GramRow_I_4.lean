import AESMixing.Generated.GramAggregate_I_4_0
import AESMixing.Generated.GramAggregate_I_4_1
import AESMixing.Generated.GramAggregate_I_4_2
import AESMixing.Generated.GramAggregate_I_4_3
import AESMixing.Generated.GramAggregate_I_4_4
import AESMixing.Generated.GramAggregate_I_4_5
import AESMixing.Generated.GramAggregate_I_4_6
import AESMixing.Generated.GramAggregate_I_4_7
import AESMixing.Generated.GramAggregate_I_4_8
import AESMixing.Generated.GramAggregate_I_4_9
import AESMixing.Generated.GramAggregate_I_4_10
import AESMixing.Generated.GramAggregate_I_4_11
import AESMixing.Generated.GramAggregate_I_4_12
import AESMixing.Generated.GramAggregate_I_4_13
import AESMixing.Generated.GramAggregate_I_4_14
import AESMixing.Generated.GramAggregate_I_4_15
open scoped BigOperators
namespace AESMixing.GramRow.I_4
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.I_4_0.values, AESMixing.GramPair.I_4_1.values, AESMixing.GramPair.I_4_2.values, AESMixing.GramPair.I_4_3.values, AESMixing.GramPair.I_4_4.values, AESMixing.GramPair.I_4_5.values, AESMixing.GramPair.I_4_6.values, AESMixing.GramPair.I_4_7.values, AESMixing.GramPair.I_4_8.values, AESMixing.GramPair.I_4_9.values, AESMixing.GramPair.I_4_10.values, AESMixing.GramPair.I_4_11.values, AESMixing.GramPair.I_4_12.values, AESMixing.GramPair.I_4_13.values, AESMixing.GramPair.I_4_14.values, AESMixing.GramPair.I_4_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) 4) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation true) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.I_4_0.gram_entries j
  · exact AESMixing.GramPair.I_4_1.gram_entries j
  · exact AESMixing.GramPair.I_4_2.gram_entries j
  · exact AESMixing.GramPair.I_4_3.gram_entries j
  · exact AESMixing.GramPair.I_4_4.gram_entries j
  · exact AESMixing.GramPair.I_4_5.gram_entries j
  · exact AESMixing.GramPair.I_4_6.gram_entries j
  · exact AESMixing.GramPair.I_4_7.gram_entries j
  · exact AESMixing.GramPair.I_4_8.gram_entries j
  · exact AESMixing.GramPair.I_4_9.gram_entries j
  · exact AESMixing.GramPair.I_4_10.gram_entries j
  · exact AESMixing.GramPair.I_4_11.gram_entries j
  · exact AESMixing.GramPair.I_4_12.gram_entries j
  · exact AESMixing.GramPair.I_4_13.gram_entries j
  · exact AESMixing.GramPair.I_4_14.gram_entries j
  · exact AESMixing.GramPair.I_4_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.I_4
