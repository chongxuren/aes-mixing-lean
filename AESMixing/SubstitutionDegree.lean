import AESMixing.CoordinateTensor

/-! Substitution preserves residual-coordinate components and contracts degree j
by (9/128)^j. This statement concerns the actual AES byte resources and every
joint input vector, and is separate from the subsequent diffusion estimate. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem byte_degree_right {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (b : Bool) :
    kernelCompose D (degreePiece 0 b) = bytePiece D b := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action]
  cases b
  · change action D (action (activityMatrix 0) f) = action (activityMatrix 0) f
    rw [activityMatrix_action, h.pointed.action_average]
  · change action D (action (residualProjection 0) f) = action (residualMatrix D 0) f
    rw [residualProjection_action, residualMatrix_action h.pointed]

theorem byte_degree_left {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (b : Bool) :
    kernelCompose (degreePiece 0 b) D = bytePiece D b := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action]
  cases b
  · change action (activityMatrix 0) (action D f) = action (activityMatrix 0) f
    rw [activityMatrix_action, h.pointed.average_action, activityMatrix_action]
  · change action (residualProjection 0) (action D f) = action (D - activityMatrix 0) f
    rw [residualProjection_action, wordResidual, h.pointed.average_action,
      kernel_action_sub, activityMatrix_action]

def substitutionKernel (D : BinaryWord 8 → BinaryWord 8 → ℝ) :
    (Fin 4 → BinaryWord 8) → (Fin 4 → BinaryWord 8) → ℝ :=
  coordinateKernel (fun _ => D)

def residualDegree (a : Fin 4 → Bool) : ℕ :=
  (Finset.univ.filter (fun i => a i = true)).card

theorem residualDegree_le (a : Fin 4 → Bool) : residualDegree a ≤ 4 := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem bytePieceBound_product (a : Fin 4 → Bool) :
    (∏ i, bytePieceBound (a i)) = (9/128 : ℝ)^residualDegree a := by
  simp [bytePieceBound, residualDegree, Finset.prod_ite, div_pow]

theorem substitution_pattern_right {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (a : Fin 4 → Bool) :
    kernelCompose (substitutionKernel D) (productProjection 0 a) =
      coordinateKernel (fun i => bytePiece D (a i)) := by
  change kernelCompose (coordinateKernel (fun _ => D))
    (coordinateKernel (fun i => degreePiece 0 (a i))) = _
  rw [coordinateKernel_compose]
  simp_rw [byte_degree_right h]

theorem substitution_pattern_left {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (a : Fin 4 → Bool) :
    kernelCompose (productProjection 0 a) (substitutionKernel D) =
      coordinateKernel (fun i => bytePiece D (a i)) := by
  change kernelCompose (coordinateKernel (fun i => degreePiece 0 (a i)))
    (coordinateKernel (fun _ => D)) = _
  rw [coordinateKernel_compose]
  simp_rw [byte_degree_left h]

theorem substitution_pattern_commutes {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (a : Fin 4 → Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    action (productProjection 0 a) (action (substitutionKernel D) f) =
      action (substitutionKernel D) (action (productProjection 0 a) f) := by
  rw [← kernelCompose_action, ← kernelCompose_action,
    substitution_pattern_left h, substitution_pattern_right h]

theorem substitution_pattern_energy {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (a : Fin 4 → Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, action (substitutionKernel D) (action (productProjection 0 a) f) y^2) ≤
      ((9/128 : ℝ)^residualDegree a)^2 * ∑ x, action (productProjection 0 a) f x^2 := by
  let g := action (productProjection 0 a) f
  have hproj : action (productProjection 0 a) g = g := by
    change action (productProjection 0 a) (action (productProjection 0 a) f) = _
    rw [← kernelCompose_action, productProjection_compose 0 (by norm_num [BinaryWord.card])]
    simp only [if_true]
    rfl
  have he := four_coordinate_byte_piece_energy h a g
  rw [bytePieceBound_product, ← substitution_pattern_right h,
    kernelCompose_action, hproj] at he
  exact he

end AESMixing
