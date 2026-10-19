import AESMixing.Generated.GramAggregate_F_11_0
import AESMixing.Generated.GramAggregate_F_11_1
import AESMixing.Generated.GramAggregate_F_11_2
import AESMixing.Generated.GramAggregate_F_11_3
import AESMixing.Generated.GramAggregate_F_11_4
import AESMixing.Generated.GramAggregate_F_11_5
import AESMixing.Generated.GramAggregate_F_11_6
import AESMixing.Generated.GramAggregate_F_11_7
import AESMixing.Generated.GramAggregate_F_11_8
import AESMixing.Generated.GramAggregate_F_11_9
import AESMixing.Generated.GramAggregate_F_11_10
import AESMixing.Generated.GramAggregate_F_11_11
import AESMixing.Generated.GramAggregate_F_11_12
import AESMixing.Generated.GramAggregate_F_11_13
import AESMixing.Generated.GramAggregate_F_11_14
import AESMixing.Generated.GramAggregate_F_11_15
open scoped BigOperators
namespace AESMixing.GramRow.F_11
def values : Fin 16 → Fin 5 → ℤ := ![AESMixing.GramPair.F_11_0.values, AESMixing.GramPair.F_11_1.values, AESMixing.GramPair.F_11_2.values, AESMixing.GramPair.F_11_3.values, AESMixing.GramPair.F_11_4.values, AESMixing.GramPair.F_11_5.values, AESMixing.GramPair.F_11_6.values, AESMixing.GramPair.F_11_7.values, AESMixing.GramPair.F_11_8.values, AESMixing.GramPair.F_11_9.values, AESMixing.GramPair.F_11_10.values, AESMixing.GramPair.F_11_11.values, AESMixing.GramPair.F_11_12.values, AESMixing.GramPair.F_11_13.values, AESMixing.GramPair.F_11_14.values, AESMixing.GramPair.F_11_15.values]
theorem gram_entries (j : Fin 5) (b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) 11) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation false) b) y) =
        (values b j : ℝ) / 255^4 := by
  fin_cases b
  · exact AESMixing.GramPair.F_11_0.gram_entries j
  · exact AESMixing.GramPair.F_11_1.gram_entries j
  · exact AESMixing.GramPair.F_11_2.gram_entries j
  · exact AESMixing.GramPair.F_11_3.gram_entries j
  · exact AESMixing.GramPair.F_11_4.gram_entries j
  · exact AESMixing.GramPair.F_11_5.gram_entries j
  · exact AESMixing.GramPair.F_11_6.gram_entries j
  · exact AESMixing.GramPair.F_11_7.gram_entries j
  · exact AESMixing.GramPair.F_11_8.gram_entries j
  · exact AESMixing.GramPair.F_11_9.gram_entries j
  · exact AESMixing.GramPair.F_11_10.gram_entries j
  · exact AESMixing.GramPair.F_11_11.gram_entries j
  · exact AESMixing.GramPair.F_11_12.gram_entries j
  · exact AESMixing.GramPair.F_11_13.gram_entries j
  · exact AESMixing.GramPair.F_11_14.gram_entries j
  · exact AESMixing.GramPair.F_11_15.gram_entries j
#print axioms gram_entries
end AESMixing.GramRow.F_11
