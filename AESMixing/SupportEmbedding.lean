import AESMixing.CoordinateEmbedding
import AESMixing.ShortenedIncidence

/-! A support component keeps an arbitrary joint function on marked
positions, fixes inactive positions to zero, and is constant on the other
nonzero positions. We first use unnormalized constants; their exact energy
supplies the paper's normalization factor. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit maskSize)

set_option maxRecDepth 100000 in
theorem unmarked_coordinate_count : ∀ r out : Fin 16, MaskDisjoint r out →
    (Finset.univ.filter (fun i : {i : Fin 4 // maskBit out i ≠ true} =>
      ¬maskBit r i.val = true)).card = 4-(maskSize r+maskSize out) := by decide

variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

def supportConstant (zeroPosition : Bool) (x : V) : ℝ :=
  if zeroPosition then identityKernel x 0 else 1-identityKernel x 0

theorem supportConstant_energy (b : Bool) :
    (∑ x : V, supportConstant b x^2) =
      if b then 1 else (Fintype.card V : ℝ)-1 := by
  cases b
  · have hp (x : V) : supportConstant false x^2 = 1-identityKernel x 0 := by
      by_cases h : x = 0 <;> simp [supportConstant, identityKernel, h]
    simp_rw [hp]
    rw [Finset.sum_sub_distrib]
    simp [identityKernel]
  · have hp (x : V) : supportConstant true x^2 = identityKernel x 0 := by
      by_cases h : x = 0 <;> simp [supportConstant, identityKernel, h]
    simp_rw [hp]
    simp [identityKernel]

def supportEmbedding (r out : Fin 16) (f : (MaskCoordinates out → V) → ℝ) :
    (Fin 4 → V) → ℝ :=
  coordinateEmbedding (fun i => maskBit out i = true)
    (fun i => supportConstant (maskBit r i.val)) f

theorem supportEmbedding_energy (r out : Fin 16) (hr : MaskDisjoint r out)
    (f : (MaskCoordinates out → V) → ℝ) :
    (∑ x, supportEmbedding r out f x^2) =
      ((Fintype.card V : ℝ)-1)^(4-(maskSize r+maskSize out)) * ∑ u, f u^2 := by
  unfold supportEmbedding
  rw [coordinateEmbedding_energy]
  simp_rw [supportConstant_energy]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
  rw [unmarked_coordinate_count r out hr]
  ring

end AESMixing
