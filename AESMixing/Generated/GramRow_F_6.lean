import AESMixing.Generated.GramAggregate_F_6_0
import AESMixing.Generated.GramAggregate_F_6_1
import AESMixing.Generated.GramAggregate_F_6_2
import AESMixing.Generated.GramAggregate_F_6_3
import AESMixing.Generated.GramAggregate_F_6_4
import AESMixing.Generated.GramAggregate_F_6_5
import AESMixing.Generated.GramAggregate_F_6_6
import AESMixing.Generated.GramAggregate_F_6_7
import AESMixing.Generated.GramAggregate_F_6_8
import AESMixing.Generated.GramAggregate_F_6_9
import AESMixing.Generated.GramAggregate_F_6_10
import AESMixing.Generated.GramAggregate_F_6_11
import AESMixing.Generated.GramAggregate_F_6_12
import AESMixing.Generated.GramAggregate_F_6_13
import AESMixing.Generated.GramAggregate_F_6_14
import AESMixing.Generated.GramAggregate_F_6_15
open scoped BigOperators
namespace AESMixing.GramRow.F_6
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.F_6_0.values, AESMixing.GramPair.F_6_1.values, AESMixing.GramPair.F_6_2.values, AESMixing.GramPair.F_6_3.values, AESMixing.GramPair.F_6_4.values, AESMixing.GramPair.F_6_5.values, AESMixing.GramPair.F_6_6.values, AESMixing.GramPair.F_6_7.values, AESMixing.GramPair.F_6_8.values, AESMixing.GramPair.F_6_9.values, AESMixing.GramPair.F_6_10.values, AESMixing.GramPair.F_6_11.values, AESMixing.GramPair.F_6_12.values, AESMixing.GramPair.F_6_13.values, AESMixing.GramPair.F_6_14.values, AESMixing.GramPair.F_6_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) 6) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.F_6_0.gram_entries j
  · exact AESMixing.GramPair.F_6_1.gram_entries j
  · exact AESMixing.GramPair.F_6_2.gram_entries j
  · exact AESMixing.GramPair.F_6_3.gram_entries j
  · exact AESMixing.GramPair.F_6_4.gram_entries j
  · exact AESMixing.GramPair.F_6_5.gram_entries j
  · exact AESMixing.GramPair.F_6_6.gram_entries j
  · exact AESMixing.GramPair.F_6_7.gram_entries j
  · exact AESMixing.GramPair.F_6_8.gram_entries j
  · exact AESMixing.GramPair.F_6_9.gram_entries j
  · exact AESMixing.GramPair.F_6_10.gram_entries j
  · exact AESMixing.GramPair.F_6_11.gram_entries j
  · exact AESMixing.GramPair.F_6_12.gram_entries j
  · exact AESMixing.GramPair.F_6_13.gram_entries j
  · exact AESMixing.GramPair.F_6_14.gram_entries j
  · exact AESMixing.GramPair.F_6_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.F_6
