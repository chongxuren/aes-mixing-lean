import AESMixing.Generated.GramAggregate_F_2_0
import AESMixing.Generated.GramAggregate_F_2_1
import AESMixing.Generated.GramAggregate_F_2_2
import AESMixing.Generated.GramAggregate_F_2_3
import AESMixing.Generated.GramAggregate_F_2_4
import AESMixing.Generated.GramAggregate_F_2_5
import AESMixing.Generated.GramAggregate_F_2_6
import AESMixing.Generated.GramAggregate_F_2_7
import AESMixing.Generated.GramAggregate_F_2_8
import AESMixing.Generated.GramAggregate_F_2_9
import AESMixing.Generated.GramAggregate_F_2_10
import AESMixing.Generated.GramAggregate_F_2_11
import AESMixing.Generated.GramAggregate_F_2_12
import AESMixing.Generated.GramAggregate_F_2_13
import AESMixing.Generated.GramAggregate_F_2_14
import AESMixing.Generated.GramAggregate_F_2_15
open scoped BigOperators
namespace AESMixing.GramRow.F_2
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.F_2_0.values, AESMixing.GramPair.F_2_1.values, AESMixing.GramPair.F_2_2.values, AESMixing.GramPair.F_2_3.values, AESMixing.GramPair.F_2_4.values, AESMixing.GramPair.F_2_5.values, AESMixing.GramPair.F_2_6.values, AESMixing.GramPair.F_2_7.values, AESMixing.GramPair.F_2_8.values, AESMixing.GramPair.F_2_9.values, AESMixing.GramPair.F_2_10.values, AESMixing.GramPair.F_2_11.values, AESMixing.GramPair.F_2_12.values, AESMixing.GramPair.F_2_13.values, AESMixing.GramPair.F_2_14.values, AESMixing.GramPair.F_2_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) 2) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.F_2_0.gram_entries j
  · exact AESMixing.GramPair.F_2_1.gram_entries j
  · exact AESMixing.GramPair.F_2_2.gram_entries j
  · exact AESMixing.GramPair.F_2_3.gram_entries j
  · exact AESMixing.GramPair.F_2_4.gram_entries j
  · exact AESMixing.GramPair.F_2_5.gram_entries j
  · exact AESMixing.GramPair.F_2_6.gram_entries j
  · exact AESMixing.GramPair.F_2_7.gram_entries j
  · exact AESMixing.GramPair.F_2_8.gram_entries j
  · exact AESMixing.GramPair.F_2_9.gram_entries j
  · exact AESMixing.GramPair.F_2_10.gram_entries j
  · exact AESMixing.GramPair.F_2_11.gram_entries j
  · exact AESMixing.GramPair.F_2_12.gram_entries j
  · exact AESMixing.GramPair.F_2_13.gram_entries j
  · exact AESMixing.GramPair.F_2_14.gram_entries j
  · exact AESMixing.GramPair.F_2_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.F_2
