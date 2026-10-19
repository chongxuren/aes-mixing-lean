import AESMixing.MDSGraphCount
import AESMixing.WordMDS

/-! Concrete AES specializations of the graph-shortening count. -/
namespace AESMixing.AES

theorem byte_mds_graph_zero_count (r z : Fin 16) :
    Fintype.card {x : Fin 4 → BinaryWord 8 //
      graphZeroConditions (columnMatrix mixEntry) r z x} =
      256 ^ (4 - (maskSize r + maskSize z)) := by
  have h := mds_graph_zero_count (columnMatrix mixEntry) byteMixColumns_zeroMDS r z
  norm_num only [BinaryWord.card, Nat.reducePow] at h
  exact h

theorem word_mds_graph_zero_count (r z : Fin 16) :
    Fintype.card {x : WordState // graphZeroConditions wordMix r z x} =
      (2^32) ^ (4 - (maskSize r + maskSize z)) := by
  simpa only [word_card] using mds_graph_zero_count wordMix wordMix_zeroMDS r z

end AESMixing.AES
