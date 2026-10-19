import AESMixing.Generated.GramAggregate_F_3_0
import AESMixing.Generated.GramAggregate_F_3_1
import AESMixing.Generated.GramAggregate_F_3_2
import AESMixing.Generated.GramAggregate_F_3_3
import AESMixing.Generated.GramAggregate_F_3_4
import AESMixing.Generated.GramAggregate_F_3_5
import AESMixing.Generated.GramAggregate_F_3_6
import AESMixing.Generated.GramAggregate_F_3_7
import AESMixing.Generated.GramAggregate_F_3_8
import AESMixing.Generated.GramAggregate_F_3_9
import AESMixing.Generated.GramAggregate_F_3_10
import AESMixing.Generated.GramAggregate_F_3_11
import AESMixing.Generated.GramAggregate_F_3_12
import AESMixing.Generated.GramAggregate_F_3_13
import AESMixing.Generated.GramAggregate_F_3_14
import AESMixing.Generated.GramAggregate_F_3_15
open scoped BigOperators
namespace AESMixing.GramRow.F_3
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.F_3_0.values, AESMixing.GramPair.F_3_1.values, AESMixing.GramPair.F_3_2.values, AESMixing.GramPair.F_3_3.values, AESMixing.GramPair.F_3_4.values, AESMixing.GramPair.F_3_5.values, AESMixing.GramPair.F_3_6.values, AESMixing.GramPair.F_3_7.values, AESMixing.GramPair.F_3_8.values, AESMixing.GramPair.F_3_9.values, AESMixing.GramPair.F_3_10.values, AESMixing.GramPair.F_3_11.values, AESMixing.GramPair.F_3_12.values, AESMixing.GramPair.F_3_13.values, AESMixing.GramPair.F_3_14.values, AESMixing.GramPair.F_3_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) 3) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.F_3_0.gram_entries j
  · exact AESMixing.GramPair.F_3_1.gram_entries j
  · exact AESMixing.GramPair.F_3_2.gram_entries j
  · exact AESMixing.GramPair.F_3_3.gram_entries j
  · exact AESMixing.GramPair.F_3_4.gram_entries j
  · exact AESMixing.GramPair.F_3_5.gram_entries j
  · exact AESMixing.GramPair.F_3_6.gram_entries j
  · exact AESMixing.GramPair.F_3_7.gram_entries j
  · exact AESMixing.GramPair.F_3_8.gram_entries j
  · exact AESMixing.GramPair.F_3_9.gram_entries j
  · exact AESMixing.GramPair.F_3_10.gram_entries j
  · exact AESMixing.GramPair.F_3_11.gram_entries j
  · exact AESMixing.GramPair.F_3_12.gram_entries j
  · exact AESMixing.GramPair.F_3_13.gram_entries j
  · exact AESMixing.GramPair.F_3_14.gram_entries j
  · exact AESMixing.GramPair.F_3_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.F_3
