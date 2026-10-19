import AESConcrete.FrameHamming

/-!
# Actual physical mask counts for three-mark survivor pairs

Common zero constraints are intersections of the original output masks
and of the original input masks. Union constraints retain that same split.
Boolean activity choices realize these operations without relabeling any
physical graph position. Count identities then give the exact Hamming
cases used by the separate signed overlap argument.

Constructive mathematics only; no attacks, numerical cube enumeration,
manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MarkedTripleMasks
open AESMixing
open AESMixing.AES (maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (zeroPositions outputZeros inputZeros)
open AESConcrete.SurvivorRelabel (falseCount cubeSurvives)
open AESConcrete.FrameHamming (distance bothFalseCount)
open AESConcrete.ActualMarkedFrameBound (survives)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

section Boolean
variable {I : Type*} [Fintype I]

def commonChoice (s t : I → Bool) : I → Bool := fun i => s i || t i
def unionChoice (s t : I → Bool) : I → Bool := fun i => s i && t i

theorem commonChoice_false (s t : I → Bool) (i : I) :
    commonChoice s t i = false ↔ s i = false ∧ t i = false := by
  cases hs : s i <;> cases ht : t i <;> simp [commonChoice, hs, ht]

theorem unionChoice_false (s t : I → Bool) (i : I) :
    unionChoice s t i = false ↔ s i = false ∨ t i = false := by
  cases hs : s i <;> cases ht : t i <;> simp [unionChoice, hs, ht]

theorem falseCount_commonChoice (s t : I → Bool) :
    falseCount (commonChoice s t) = bothFalseCount s t := by
  exact Fintype.card_congr (Equiv.subtypeEquivRight (commonChoice_false s t))

theorem union_false_count_add_common (s t : I → Bool) :
    falseCount (unionChoice s t) + bothFalseCount s t = falseCount s + falseCount t := by
  calc
    _ = (∑ i : I, if unionChoice s t i = false then 1 else 0) +
        (∑ i : I, if s i = false ∧ t i = false then 1 else 0) := by
      rw [FrameHamming.falseCount_eq_sum, FrameHamming.bothFalseCount_eq_sum]
    _ = ∑ i : I, ((if s i = false then 1 else 0) +
        (if t i = false then 1 else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      cases hs : s i <;> cases ht : t i <;> simp [unionChoice, hs, ht]
    _ = _ := by
      rw [Finset.sum_add_distrib, FrameHamming.falseCount_eq_sum, FrameHamming.falseCount_eq_sum]

end Boolean

private theorem bool_eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem output_mask_inter (A B : Finset GraphPosition) :
    outputPositionMask (A ∩ B) = maskIntersection (outputPositionMask A) (outputPositionMask B) := by
  apply maskBits_injective
  funext i
  apply bool_eq_of_true_iff
  simp only [outputPositionMask_bit, maskIntersection_bit, Bool.and_eq_true, Finset.mem_inter]

private theorem input_mask_inter (A B : Finset GraphPosition) :
    inputPositionMask (A ∩ B) = maskIntersection (inputPositionMask A) (inputPositionMask B) := by
  apply maskBits_injective
  funext i
  apply bool_eq_of_true_iff
  simp only [inputPositionMask_bit, maskIntersection_bit, Bool.and_eq_true, Finset.mem_inter]

private theorem output_mask_union (A B : Finset GraphPosition) :
    outputPositionMask (A ∪ B) = maskUnion (outputPositionMask A) (outputPositionMask B) := by
  apply maskBits_injective
  funext i
  apply bool_eq_of_true_iff
  simp only [outputPositionMask_bit, maskUnion_bit, Bool.or_eq_true, Finset.mem_union]

private theorem input_mask_union (A B : Finset GraphPosition) :
    inputPositionMask (A ∪ B) = maskUnion (inputPositionMask A) (inputPositionMask B) := by
  apply maskBits_injective
  funext i
  apply bool_eq_of_true_iff
  simp only [inputPositionMask_bit, maskUnion_bit, Bool.or_eq_true, Finset.mem_union]

theorem zeroPositions_commonChoice (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    zeroPositions m (commonChoice s t) = zeroPositions m s ∩ zeroPositions m t := by
  ext p
  simp only [MarkedBlockShortening.mem_zeroPositions, Finset.mem_inter, commonChoice_false]
  constructor
  · rintro ⟨h,hs,ht⟩
    exact ⟨⟨h,hs⟩,⟨h,ht⟩⟩
  · rintro ⟨⟨h,hs⟩,⟨h',ht⟩⟩
    exact ⟨h,hs,ht⟩

theorem zeroPositions_unionChoice (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    zeroPositions m (unionChoice s t) = zeroPositions m s ∪ zeroPositions m t := by
  ext p
  simp only [MarkedBlockShortening.mem_zeroPositions, Finset.mem_union, unionChoice_false]
  constructor
  · rintro ⟨h,hs | ht⟩
    · exact Or.inl ⟨h,hs⟩
    · exact Or.inr ⟨h,ht⟩
  · rintro (⟨h,hs⟩ | ⟨h,ht⟩)
    · exact ⟨h,Or.inl hs⟩
    · exact ⟨h,Or.inr ht⟩

theorem outputZeros_commonChoice (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    outputZeros m (commonChoice s t) = maskIntersection (outputZeros m s) (outputZeros m t) := by
  unfold outputZeros
  rw [zeroPositions_commonChoice, output_mask_inter]

theorem inputZeros_commonChoice (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    inputZeros m (commonChoice s t) = maskIntersection (inputZeros m s) (inputZeros m t) := by
  unfold inputZeros
  rw [zeroPositions_commonChoice, input_mask_inter]

theorem outputZeros_unionChoice (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    outputZeros m (unionChoice s t) = maskUnion (outputZeros m s) (outputZeros m t) := by
  unfold outputZeros
  rw [zeroPositions_unionChoice, output_mask_union]

theorem inputZeros_unionChoice (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    inputZeros m (unionChoice s t) = maskUnion (inputZeros m s) (inputZeros m t) := by
  unfold inputZeros
  rw [zeroPositions_unionChoice, input_mask_union]

def commonCount (m : GraphPosition → Bool) (s t : Activity m → Bool) : ℕ :=
  maskSize (maskIntersection (outputZeros m s) (outputZeros m t)) +
    maskSize (maskIntersection (inputZeros m s) (inputZeros m t))

def unionCount (m : GraphPosition → Bool) (s t : Activity m → Bool) : ℕ :=
  maskSize (maskUnion (outputZeros m s) (outputZeros m t)) +
    maskSize (maskUnion (inputZeros m s) (inputZeros m t))

theorem common_zero_count (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    commonCount m s t = bothFalseCount s t := by
  unfold commonCount
  rw [← outputZeros_commonChoice, ← inputZeros_commonChoice]
  exact (MarkedBlockScale.zero_count m (commonChoice s t)).symm.trans (falseCount_commonChoice s t)

theorem union_add_common (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    unionCount m s t + commonCount m s t = falseCount s + falseCount t := by
  have hu : unionCount m s t = falseCount (unionChoice s t) := by
    unfold unionCount
    rw [← outputZeros_unionChoice, ← inputZeros_unionChoice]
    exact (MarkedBlockScale.zero_count m (unionChoice s t)).symm
  rw [hu, common_zero_count]
  exact union_false_count_add_common s t

theorem union_zero_count (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    unionCount m s t = falseCount s + falseCount t - bothFalseCount s t := by
  have h := union_add_common m s t
  rw [common_zero_count] at h
  omega

theorem distance_add_twice_common (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    distance s t + 2 * commonCount m s t = falseCount s + falseCount t := by
  simpa only [common_zero_count] using FrameHamming.distance_add_twice_bothFalse s t

theorem union_eq_distance_add_common (m : GraphPosition → Bool) (s t : Activity m → Bool) :
    unionCount m s t = distance s t + commonCount m s t := by
  have h1 := union_add_common m s t
  have h2 := distance_add_twice_common m s t
  omega

theorem triple_survivor_falseCount (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) (s : Activity m → Bool) (hs : survives m s) :
    falseCount s = 2 ∨ falseCount s = 3 := by
  have h := (SurvivorRelabel.survives_iff_cube m s).mp hs
  rw [hlen] at h
  unfold cubeSurvives at h
  omega

theorem triple_pair22_geometry (m : GraphPosition → Bool) (s t : Activity m → Bool)
    (hs : falseCount s = 2) (ht : falseCount t = 2) :
    (distance s t = 0 ∧ commonCount m s t = 2 ∧ unionCount m s t = 2) ∨
    (distance s t = 2 ∧ commonCount m s t = 1 ∧ unionCount m s t = 3) ∨
    (distance s t = 4 ∧ commonCount m s t = 0 ∧ unionCount m s t = 4) := by
  have h1 := distance_add_twice_common m s t
  have h2 := union_add_common m s t
  omega

theorem triple_pair33_geometry (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 3) (s t : Activity m → Bool)
    (hs : falseCount s = 3) (ht : falseCount t = 3) :
    (distance s t = 0 ∧ commonCount m s t = 3 ∧ unionCount m s t = 3) ∨
    (distance s t = 2 ∧ commonCount m s t = 2 ∧ unionCount m s t = 4) ∨
    (distance s t = 4 ∧ commonCount m s t = 1 ∧ unionCount m s t = 5) := by
  have h1 := distance_add_twice_common m s t
  have h2 := union_add_common m s t
  have hd := FrameHamming.distance_le_card s t
  rw [SurvivorRelabel.activity_card m 3 hlen] at hd
  norm_num at hd
  omega

theorem triple_mixed_geometry (m : GraphPosition → Bool) (s t : Activity m → Bool)
    (hst : (falseCount s = 2 ∧ falseCount t = 3) ∨ (falseCount s = 3 ∧ falseCount t = 2)) :
    (distance s t = 1 ∧ commonCount m s t = 2 ∧ unionCount m s t = 3) ∨
    (distance s t = 3 ∧ commonCount m s t = 1 ∧ unionCount m s t = 4) ∨
    (distance s t = 5 ∧ commonCount m s t = 0 ∧ unionCount m s t = 5) := by
  have h1 := distance_add_twice_common m s t
  have h2 := union_add_common m s t
  omega

end AESConcrete.MarkedTripleMasks
