import AES8.Math.PaperSymbolicShortening

/-! Cyclic transport from the two representative output pairs to all six
unordered pairs, with the adjacent pair 74 oriented cyclically. Reversing an
ordered pair inverts its nonzero slope and preserves equality classes. -/
noncomputable section
namespace AES8.PaperSymbolicRotation
open Polynomial PaperSymbolicSlopeTable PaperSymbolicMDS PaperSymbolicShortening
open scoped Matrix BigOperators
set_option autoImplicit false

def rotation (r : Fin 4) (p : Fin 8) : Fin 8 :=
  if p.val < 4 then ⟨(p.val+r.val)%4, by omega⟩
  else ⟨4+(p.val-4+r.val)%4, by omega⟩

def inputShift {F : Type*} (r : Fin 4) (x : Fin 4 → F) : Fin 4 → F :=
  fun i => x (i+r)

theorem inputShift_bijective {F : Type*} (r : Fin 4) :
    Function.Bijective (inputShift (F := F) r) := by
  constructor
  · intro x y h
    funext i
    have hi := congrFun h (i-r)
    simpa [inputShift] using hi
  · intro y
    refine ⟨fun i => y (i-r), ?_⟩
    funext i
    simp [inputShift]

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

theorem rotated_word (a : F) (r : Fin 4) (x : Fin 4 → F) (p : Fin 8) :
    graphWord a (inputShift r x) p = graphWord a x (rotation r p) := by
  fin_cases r <;> fin_cases p <;>
    simp [graphWord, graphMatrix, rotation, inputShift, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Fin.add_def] <;> ring

def RotatedShortened (a : F) (pair : Bool) (r : Fin 4) (k : Fin 20)
    (x : Fin 4 → F) : Prop :=
  ∀ i ∈ zeros pair k, graphWord a x (rotation r i) = 0

theorem rotated_marked_image (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (r : Fin 4) (k : Fin 20) (z w : F) :
    (∃ x, RotatedShortened a pair r k x ∧ graphWord a x (rotation r 4) = z ∧
      graphWord a x (rotation r (secondMark pair)) = w) ↔
        w = slope a pair k * z := by
  rw [← shortened_marked_image a ha pair k z w]
  constructor
  · rintro ⟨x,hx,hz,hw⟩
    refine ⟨inputShift r x, ?_, ?_, ?_⟩
    · simpa only [Shortened, RotatedShortened, rotated_word] using hx
    · simpa only [rotated_word] using hz
    · simpa only [rotated_word] using hw
  · rintro ⟨x,hx,hz,hw⟩
    obtain ⟨y,hy⟩ := (inputShift_bijective (F := F) r).surjective x
    subst x
    refine ⟨y, ?_, ?_, ?_⟩
    · simpa only [Shortened, RotatedShortened, rotated_word] using hx
    · simpa only [rotated_word] using hz
    · simpa only [rotated_word] using hw

/-- Four adjacent rotations, then two opposite rotations. -/
def pairKind (p : Fin 6) : Bool := decide (4 ≤ p.val)
def pairRotation (p : Fin 6) : Fin 4 := if h : p.val < 4 then ⟨p.val,h⟩ else ⟨p.val-4,by omega⟩
def pairMarks (p : Fin 6) : Finset (Fin 8) :=
  {rotation (pairRotation p) 4, rotation (pairRotation p) (secondMark (pairKind p))}

set_option maxRecDepth 8192 in
theorem all_six_pairs (s : Finset (Fin 8)) :
    s.card = 2 ∧ (∀ i ∈ s, 4 ≤ i.val) ↔ ∃ p, pairMarks p = s := by
  revert s
  decide

theorem slope_nonzero (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (k : Fin 20) : slope a pair k ≠ 0 := by
  apply div_ne_zero
  · exact PaperAlgebraicSpecialization.eval_ne_zero a _ (raw_bounds pair k).1
      (by have := (raw_bounds pair k).2.2.1; omega)
  · exact denominator_ne_zero a ha pair k

theorem reversed_marked_image (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (r : Fin 4) (k : Fin 20) (z w : F) :
    (∃ x, RotatedShortened a pair r k x ∧
      graphWord a x (rotation r (secondMark pair)) = z ∧
      graphWord a x (rotation r 4) = w) ↔ w = (slope a pair k)⁻¹ * z := by
  have h := rotated_marked_image a ha pair r k w z
  have hn := slope_nonzero a ha pair k
  constructor
  · rintro ⟨x,hx,hz,hw⟩
    have he := h.mp ⟨x,hx,hw,hz⟩
    rw [he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · intro hw
    have he : z = slope a pair k * w := by
      rw [hw, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    obtain ⟨x,hx,hfirst,hsecond⟩ := h.mpr he
    exact ⟨x,hx,hsecond,hfirst⟩

theorem reversed_slope_classes (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (pair : Bool) (i j : Fin 20) :
    (slope a pair i)⁻¹ = (slope a pair j)⁻¹ ↔ slopeClass pair i = slopeClass pair j := by
  rw [inv_inj]
  exact slope_eq_iff a ha pair i j

end AES8.PaperSymbolicRotation
