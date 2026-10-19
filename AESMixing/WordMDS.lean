import AESMixing.MDSProjection

/-! Word-coordinate additive map and its full interpolation property. -/
namespace AESMixing.AES

def shiftRowsHom : State →+ State where
  toFun := shiftRows
  map_zero' := rfl
  map_add' _ _ := rfl

def mixColumnsHom : State →+ State where
  toFun := mixColumns
  map_zero' := by
    funext row col
    have h := congrFun (mixColumns_column 0 col) row
    rw [show (fun r => (0 : State) r col) = 0 by rfl, map_zero] at h
    exact h
  map_add' x y := by
    funext row col
    have hx := congrFun (mixColumns_column x col) row
    have hy := congrFun (mixColumns_column y col) row
    have hxy := congrFun (mixColumns_column (x+y) col) row
    rw [show (fun r => (x+y) r col) = (fun r => x r col) + (fun r => y r col) by rfl,
      map_add] at hxy
    change mixColumns (x+y) row col = mixColumns x row col + mixColumns y row col
    rw [hxy, hx, hy]
    rfl

def wordDiffusionHom : State →+ State := shiftRowsHom.comp (mixColumnsHom.comp shiftRowsHom)

abbrev Word := Fin 4 → BinaryWord 8
abbrev WordState := Fin 4 → Word

def transposeState : WordState ≃+ State where
  toFun x row col := x col row
  invFun x col row := x row col
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def wordMix : WordState →+ WordState :=
  transposeState.symm.toAddMonoidHom.comp (wordDiffusionHom.comp transposeState.toAddMonoidHom)

theorem wordMix_apply (x : WordState) (col row : Fin 4) :
    wordMix x col row = wordDiffusion (transposeState x) row col := rfl

theorem wordMix_zeroMDS : ZeroMDS wordMix := by
  intro r c h x hs hz
  have hphysical : transposeState x = 0 := by
    apply wordDiffusion_mds_zero r c h
    · funext row col
      have he := congrFun (congrFun hs col) row
      change (if maskBit c col then x col else 0) row = x col row at he
      change (if maskBit c col then x col row else 0) = x col row
      cases hc : maskBit c col
      · simpa only [hc, Bool.false_eq_true, if_false, Pi.zero_apply] using he
      · simp only [if_true]
    · funext row col
      have he := congrFun (congrFun hz col) row
      change (if maskBit r col then wordMix x col else 0) row = 0 at he
      change (if maskBit r col then wordDiffusion (transposeState x) row col else 0) = 0
      cases hc : maskBit r col
      · simp only [Bool.false_eq_true, if_false]
      · simpa only [hc, if_true, wordMix_apply] using he
  exact transposeState.injective (hphysical.trans (map_zero transposeState).symm)

theorem wordMix_restricted_bijective (r c : Fin 16) (h : maskSize r = maskSize c) :
    Function.Bijective (restrictedMap wordMix r c) :=
  mds_restricted_bijective wordMix wordMix_zeroMDS r c h

theorem word_card : Fintype.card Word = 2^32 := by
  norm_num [Word, Fintype.card_fun, BinaryWord.card]

end AESMixing.AES
