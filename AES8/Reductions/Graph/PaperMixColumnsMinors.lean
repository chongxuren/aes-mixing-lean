import AESMixing.MDSProjection
import AESMixing.FieldMatrixCertificate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Nonzero determinants for every square AES MixColumns minor

Module role: bridge the existing concrete reconstruction/MDS certificate to
an actual determinant statement over the already defined AES byte field
`BinaryWord 8`. No new field instance or numerical certificate is introduced.
Constructive proofs only; no attacks or manuscript/predecessor edits.

Rows and columns are arbitrary embeddings of `Fin k` into `Fin 4`: their
order is retained, and each selected coordinate occurs exactly once. Such
embeddings imply `k <= 4`. The empty minor is included. The only finite
Boolean check below encodes subsets of four positions as existing masks;
the AES value arithmetic remains the prior reconstruction certificate.
The paper endpoint is `lem:mixcolumns-minors` in `08-aes-diffusion.tex`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 150000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators Matrix

namespace AES8.PaperMixColumnsMinors
open AESMixing AESMixing.AES

/-- The sixteen existing masks represent every subset of four positions. -/
private theorem masks_complete :
    ∀ p : Fin 4 → Bool, ∃ m : Fin 16, ∀ i : Fin 4, maskBit m i = p i := by
  decide

/-- Enumerating selected coordinates by an embedding agrees with an existing mask. -/
private theorem embedding_mask {k : ℕ} (e : Fin k ↪ Fin 4) :
    ∃ m : Fin 16, ∃ E : Fin k ≃ MaskCoordinates m,
      ∀ j, (E j).val = e j := by
  classical
  obtain ⟨m, hm⟩ := masks_complete (fun i => decide (∃ j, e j = i))
  have hb (i : Fin 4) : maskBit m i = true ↔ ∃ j, e j = i := by
    rw [hm]
    simp only [decide_eq_true_eq]
  let f : Fin k → MaskCoordinates m := fun j => ⟨e j, (hb (e j)).2 ⟨j, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact e.injective (congrArg Subtype.val h)
    · intro i
      obtain ⟨j, hj⟩ := (hb i.val).1 i.property
      exact ⟨j, Subtype.ext hj⟩
  exact ⟨m, Equiv.ofBijective f hf, fun _ => rfl⟩

/-- Extension by zero converts the full coordinate sum to the selected sum. -/
private theorem sum_extend {F : Type*} [Ring F] (c : Fin 16)
    (a : Fin 4 → F) (x : MaskCoordinates c → F) :
    (∑ j : Fin 4, a j * extendCoordinates c x j) =
      ∑ j : MaskCoordinates c, a j.val * x j := by
  classical
  let f : Fin 4 → F := fun j => a j * extendCoordinates c x j
  calc
    (∑ j : Fin 4, f j) =
        ∑ j ∈ Finset.univ.filter (fun j => maskBit c j = true), f j := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hn : maskBit c j ≠ true := by simpa only [Finset.mem_filter,
        Finset.mem_univ, true_and] using hj
      simp only [f, extendCoordinates, dif_neg hn, mul_zero]
    _ = ∑ j : MaskCoordinates c, f j.val :=
      Finset.sum_subtype _ (by simp) f
    _ = ∑ j : MaskCoordinates c, a j.val * x j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [f, extendCoordinates, dif_pos j.property]

/-- Explicit row/column enumeration converts a restricted field map to `mulVec`. -/
private theorem restricted_fieldMatrix_eq_mulVec {F : Type*} [Ring F] {k : ℕ}
    (A : Matrix (Fin 4) (Fin 4) F) (r c : Fin 16)
    (rows : Fin k ≃ MaskCoordinates r) (cols : Fin k ≃ MaskCoordinates c)
    (x : Fin k → F) :
    (fun i => restrictedMap (fieldMatrix A) r c
      (fun j => x (cols.symm j)) (rows i)) =
      (fun i j => A (rows i).val (cols j).val) *ᵥ x := by
  funext i
  change (∑ j : Fin 4, A (rows i).val j *
    extendCoordinates c (fun j => x (cols.symm j)) j) = _
  rw [sum_extend]
  exact (cols.sum_comp (fun j => A (rows i).val j.val * x (cols.symm j))).symm.trans
    (by simp only [Equiv.symm_apply_apply, Matrix.mulVec, dotProduct])

/-- Every ordered square submatrix acts injectively on its selected byte values. -/
theorem minor_mulVec_injective {k : ℕ} (rows cols : Fin k ↪ Fin 4) :
    Function.Injective
      (Matrix.mulVec (fun i j => (⟨mixEntry (rows i) (cols j)⟩ : BinaryWord 8))) := by
  classical
  obtain ⟨r, er, hr⟩ := embedding_mask rows
  obtain ⟨c, ec, hc⟩ := embedding_mask cols
  have hsize : maskSize r = maskSize c := by
    rw [← maskCoordinates_card r, ← maskCoordinates_card c,
      ← Fintype.card_congr er, ← Fintype.card_congr ec]
  have hbase := (byteMixColumns_restricted_bijective r c hsize).injective
  have haction (x : Fin k → BinaryWord 8) :
      (fun i => restrictedMap (columnMatrix mixEntry) r c
        (fun j => x (ec.symm j)) (er i)) =
        (fun i j => (⟨mixEntry (rows i) (cols j)⟩ : BinaryWord 8)) *ᵥ x := by
    rw [columnMatrix_eq_fieldMatrix]
    simpa only [hr, hc] using restricted_fieldMatrix_eq_mulVec
      (fun i j => (⟨mixEntry i j⟩ : BinaryWord 8)) r c er ec x
  intro x y hxy
  have hrestricted : restrictedMap (columnMatrix mixEntry) r c
      (fun j => x (ec.symm j)) =
      restrictedMap (columnMatrix mixEntry) r c (fun j => y (ec.symm j)) := by
    funext i
    have h := congrFun hxy (er.symm i)
    rw [← haction x, ← haction y] at h
    simpa only [Equiv.apply_symm_apply] using h
  have hcoords := hbase hrestricted
  funext j
  simpa only [Equiv.symm_apply_apply] using congrFun hcoords (ec j)

/-- Every square MixColumns minor has a nonzero determinant in the actual AES field. -/
theorem determinant_nonzero {k : ℕ} (rows cols : Fin k ↪ Fin 4) :
    Matrix.det (fun i j => (⟨mixEntry (rows i) (cols j)⟩ : BinaryWord 8)) ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_injective_iff_isUnit.1 (minor_mulVec_injective rows cols))).ne_zero

end AES8.PaperMixColumnsMinors
