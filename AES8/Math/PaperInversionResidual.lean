import AES8.Math.PaperInversionCounts
import AES8.Math.PaperInversionSignNorm
import AESMixing.ChannelProjection
import AESMixing.AffineChannel

/-! Residual contraction of inversion on every finite characteristic-two field.
The counting and sign-Gram leaves are kept separate; this module closes their
interfaces and transfers the full residual bound through affine output maps. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperInversionResidual
open AESMixing PaperFieldTrace
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

def bound (F : Type*) [Fintype F] : ℝ :=
  (Real.sqrt (Fintype.card F)+2)/(Fintype.card F : ℝ)

omit [DecidableEq F] [CharP F 2] [Algebra (ZMod 2) F] in
theorem bound_nonneg : 0 ≤ bound F := by unfold bound; positivity

theorem nonzero_l2 (x : {x : F // x ≠ 0} → ℝ) (hx : ∑ i, x i=0) :
    l2 (fun b : {x : F // x ≠ 0} =>
      ∑ a : {x : F // x ≠ 0}, differenceChannel invPermutation b.val a.val*x a) ≤
      bound F*l2 x := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  apply PaperInversionSignNorm.residual_l2 (Fintype.card F) hq _
    (inversionSignMatrix character) nonzeroInvPermutation _ _ x hx
  · intro i j
    exact inversion_sign_gram character character_zero character_add character_sum
      CharTwo.add_self_eq_zero i j
  · intro b a
    rw [PaperInversionCounts.channel a.val b.val a.property b.property]
    have he : a.val*b.val=1 ↔ nonzeroInvPermutation b=a := by
      rw [mul_eq_one_iff_eq_inv₀ b.property]
      change a.val=b.val⁻¹ ↔ _
      exact ⟨fun h => Subtype.ext h.symm, fun h => (congrArg Subtype.val h).symm⟩
    have ht : (a.val*b.val)⁻¹=b.val⁻¹*a.val⁻¹ := by simp [mul_inv_rev]
    simp only [inversionSignMatrix, character, ht, he]
    split_ifs <;> ring

theorem nonzero_energy (x : {x : F // x ≠ 0} → ℝ) (hx : ∑ i, x i=0) :
    (∑ b : {x : F // x ≠ 0},
      (∑ a : {x : F // x ≠ 0}, differenceChannel invPermutation b.val a.val*x a)^2) ≤
      bound F^2*∑ i, x i^2 := by
  have h := (sq_le_sq₀ (l2_nonneg _)
    (mul_nonneg (bound_nonneg (F := F)) (l2_nonneg x))).mpr (nonzero_l2 x hx)
  simpa only [mul_pow, l2_sq] using h

theorem full_energy (x : F → ℝ) (hx0 : x 0=0) (hx : ∑ i, x i=0) :
    (∑ b, action (differenceChannel invPermutation) x b^2) ≤
      bound F^2*∑ i, x i^2 := by
  have hs : (∑ i : {x : F // x ≠ 0}, x i.val)=0 := by
    have h := Fintype.sum_eq_add_sum_subtype_ne x 0
    rw [hx0, hx, zero_add] at h
    exact h.symm
  have he (b : F) : action (differenceChannel invPermutation) x b =
      ∑ a : {x : F // x ≠ 0}, differenceChannel invPermutation b a.val*x a.val := by
    rw [action, Fintype.sum_eq_add_sum_subtype_ne
      (fun a => differenceChannel invPermutation b a*x a) 0,
      hx0, mul_zero, zero_add]
  have hz : action (differenceChannel invPermutation) x 0=0 := by
    simp only [action, differenceChannel_zero_row, ite_mul, one_mul, zero_mul]
    simpa using hx0
  rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun b => action (differenceChannel invPermutation) x b^2) 0,
    hz, zero_pow (by decide), zero_add,
    Fintype.sum_eq_add_sum_subtype_ne (fun a => x a^2) 0,
    hx0, zero_pow (by decide), zero_add]
  simp_rw [he]
  exact nonzero_energy (fun i => x i.val) hs

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem pointed : PointedBistochastic (differenceChannel (invPermutation (F := F))) 0 :=
  ⟨differenceChannel_nonneg _, differenceChannel_zero_row _,
   differenceChannel_zero_column _, differenceChannel_column _, differenceChannel_row _⟩

/-- The literal channel minus the zero/uniform-nonzero orthogonal projection. -/
theorem residual_l2 (f : F → ℝ) :
    l2 (action (residualMatrix (differenceChannel invPermutation) 0) f) ≤
      bound F*l2 f := by
  apply l2_le_of_energy _ _ _ (bound_nonneg (F := F))
  exact residualMatrix_energy pointed Fintype.one_lt_card (bound F) full_energy f

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem affine_residual (A : F ≃+ F) (c b a : F) :
    residualMatrix (differenceChannel (affineOutput invPermutation A c)) 0 b a =
      residualMatrix (differenceChannel invPermutation) 0 (A.symm b) a := by
  unfold residualMatrix
  rw [affineOutput_channel]
  congr 1
  have hb : A.symm b=0 ↔ b=0 := by
    constructor
    · intro h
      have h' := congrArg A h
      simpa using h'
    · intro h; simp [h]
  simp [activityMatrix, hb]

theorem affine_residual_l2 (A : F ≃+ F) (c : F) (f : F → ℝ) :
    l2 (action (residualMatrix (differenceChannel (affineOutput invPermutation A c)) 0) f) ≤
      bound F*l2 f := by
  have he : l2 (action (residualMatrix
      (differenceChannel (affineOutput invPermutation A c)) 0) f) =
      l2 (action (residualMatrix (differenceChannel invPermutation) 0) f) := by
    unfold l2 action
    simp_rw [affine_residual]
    congr 1
    exact Equiv.sum_comp A.symm.toEquiv (fun y : F =>
      (∑ x, residualMatrix (differenceChannel invPermutation) 0 y x*f x)^2)
  rw [he]
  exact residual_l2 f

end AES8.PaperInversionResidual
