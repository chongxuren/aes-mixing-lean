import AESMixing.Generated.GramAggregate_F_0_0
import AESMixing.Generated.GramAggregate_F_0_1
import AESMixing.Generated.GramAggregate_F_0_2
import AESMixing.Generated.GramAggregate_F_0_3
import AESMixing.Generated.GramAggregate_F_0_4
import AESMixing.Generated.GramAggregate_F_0_5
import AESMixing.Generated.GramAggregate_F_0_6
import AESMixing.Generated.GramAggregate_F_0_7
import AESMixing.Generated.GramAggregate_F_0_8
import AESMixing.Generated.GramAggregate_F_0_9
import AESMixing.Generated.GramAggregate_F_0_10
import AESMixing.Generated.GramAggregate_F_0_11
import AESMixing.Generated.GramAggregate_F_0_12
import AESMixing.Generated.GramAggregate_F_0_13
import AESMixing.Generated.GramAggregate_F_0_14
import AESMixing.Generated.GramAggregate_F_0_15
open scoped BigOperators
namespace AESMixing.GramRow.F_0
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.F_0_0.values, AESMixing.GramPair.F_0_1.values, AESMixing.GramPair.F_0_2.values, AESMixing.GramPair.F_0_3.values, AESMixing.GramPair.F_0_4.values, AESMixing.GramPair.F_0_5.values, AESMixing.GramPair.F_0_6.values, AESMixing.GramPair.F_0_7.values, AESMixing.GramPair.F_0_8.values, AESMixing.GramPair.F_0_9.values, AESMixing.GramPair.F_0_10.values, AESMixing.GramPair.F_0_11.values, AESMixing.GramPair.F_0_12.values, AESMixing.GramPair.F_0_13.values, AESMixing.GramPair.F_0_14.values, AESMixing.GramPair.F_0_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) 0) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.F_0_0.gram_entries j
  · exact AESMixing.GramPair.F_0_1.gram_entries j
  · exact AESMixing.GramPair.F_0_2.gram_entries j
  · exact AESMixing.GramPair.F_0_3.gram_entries j
  · exact AESMixing.GramPair.F_0_4.gram_entries j
  · exact AESMixing.GramPair.F_0_5.gram_entries j
  · exact AESMixing.GramPair.F_0_6.gram_entries j
  · exact AESMixing.GramPair.F_0_7.gram_entries j
  · exact AESMixing.GramPair.F_0_8.gram_entries j
  · exact AESMixing.GramPair.F_0_9.gram_entries j
  · exact AESMixing.GramPair.F_0_10.gram_entries j
  · exact AESMixing.GramPair.F_0_11.gram_entries j
  · exact AESMixing.GramPair.F_0_12.gram_entries j
  · exact AESMixing.GramPair.F_0_13.gram_entries j
  · exact AESMixing.GramPair.F_0_14.gram_entries j
  · exact AESMixing.GramPair.F_0_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.F_0
