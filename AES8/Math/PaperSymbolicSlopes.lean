import AES8.Math.PaperSymbolicRotation

/-! Source-bound endpoint for the frozen paper's symbolic-slopes lemma.
The field-generic theorem supplies MDS, actual shortened marked lines, printed
fractions and exact equality classes. The concrete AES specialization lives in
Model/Word/PaperAESSymbolicSlopes. -/
noncomputable section
namespace AES8.PaperSymbolicSlopes
open Polynomial PaperSymbolicSlopeTable PaperSymbolicMDS PaperSymbolicShortening
open PaperSymbolicRotation
set_option autoImplicit false
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

structure Certificate (a : F) : Prop where
  mds : ∀ (s : Finset (Fin 8)) (_ : s.card = 4),
    Function.Bijective (fun x : Fin 4 → F => fun i : s => graphWord a x i.val)
  printed : ∀ pair k,
    slope a pair k = aeval a (PaperSymbolicSlopeTable.printed pair k).1 /
      aeval a (PaperSymbolicSlopeTable.printed pair k).2
  classes : ∀ pair i j,
    slope a pair i = slope a pair j ↔ slopeClass pair i = slopeClass pair j
  actual : ∀ pair r k z w,
    (∃ x, RotatedShortened a pair r k x ∧ graphWord a x (rotation r 4) = z ∧
      graphWord a x (rotation r (secondMark pair)) = w) ↔ w = slope a pair k * z

theorem symbolic_slopes (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    Certificate a where
  mds := graph_mds a ha
  printed := slope_eq_printed a ha
  classes := slope_eq_iff a ha
  actual := rotated_marked_image a ha

end AES8.PaperSymbolicSlopes
