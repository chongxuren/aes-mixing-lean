/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.InformationOverlap
import AES8.Math.FiberIncidence

/-!
# Normalized information-set overlap

The outside maps may be arbitrary finite label maps.  The hypotheses below are
the explicit collision sums of column/row energies over each outside fiber.
In particular, no encoder bound, orthogonality, or factorization is assumed.
The exact weighted-lift energy identity proves the retained-label
orthogonality, and expansion proves the actual `J_L^* K J_R` factorization.

Empty coordinate and outside-label types and arbitrary signed inputs are
included.  Equal fiber cardinalities are needed to call the maps isometries,
but are not needed for the collision-sum estimate itself.  MDS collision
counts and numerical AES bounds belong to separate modules.

Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace AES8.PaperInformationOverlap
open AESMixing FiberIncidence

section WeightedFibers
variable {C D O : Type*} [Fintype C] [Fintype D] [Fintype O] [DecidableEq O]

/-- Retain the complete information label while creating the other labels. -/
def weightedLift (outside : C → O) (m : ℕ) (w : C → D → ℝ)
    (f : O → ℝ) (c : C) (d : D) : ℝ :=
  w c d * normalizedLift outside m f c

/-- The transpose of the retained-label encoder, as a literal finite sum. -/
def weightedAdjoint (outside : C → O) (m : ℕ) (w : C → D → ℝ)
    (g : C → D → ℝ) : O → ℝ :=
  normalizedAdjoint outside m (fun c => ∑ d, w c d * g c d)

/-- Exact Gram identity.  Different outside columns have disjoint retained
information labels; this identity derives their orthogonality algebraically. -/
theorem weightedLift_gram (outside : C → O) (m : ℕ)
    (w : C → D → ℝ) (f g : O → ℝ) :
    (∑ c, ∑ d, weightedLift outside m w f c d *
      weightedLift outside m w g c d) =
    ∑ o, (f o * g o / (m : ℝ)) *
      rawFiberSum outside (fun c => ∑ d, w c d ^ 2) o := by
  calc
    _ = ∑ c, (f (outside c) * g (outside c) / (m : ℝ)) *
        ∑ d, w c d ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [weightedLift, normalizedLift]
      calc
        _ = w c d ^ 2 * ((f (outside c) / Real.sqrt (m : ℝ)) *
            (g (outside c) / Real.sqrt (m : ℝ))) := by ring
        _ = _ := by
          rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg m)]
          ring
    _ = _ := rawFiberSum_pairing outside
      (fun o => f o * g o / (m : ℝ)) (fun c => ∑ d, w c d ^ 2)

/-- Squared encoder energy is exactly the fiber collision energy. -/
theorem weightedLift_energy_eq (outside : C → O) (m : ℕ)
    (w : C → D → ℝ) (f : O → ℝ) :
    (∑ c, ∑ d, weightedLift outside m w f c d ^ 2) =
    ∑ o, (f o ^ 2 / (m : ℝ)) *
      rawFiberSum outside (fun c => ∑ d, w c d ^ 2) o := by
  simpa only [pow_two] using weightedLift_gram outside m w f f

/-- Distinct outside basis columns are orthogonal, as a consequence of the
retained label, with no orthogonality assumption on the local maps. -/
theorem weightedLift_columns_orthogonal (outside : C → O) (m : ℕ)
    (w : C → D → ℝ) (o p : O) (hop : o ≠ p) :
    (∑ x, ∑ d,
      weightedLift outside m w (fun z => if z = o then 1 else 0) x d *
        weightedLift outside m w (fun z => if z = p then 1 else 0) x d) = 0 := by
  rw [weightedLift_gram]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hz : z = o
  · subst z
    simp [hop]
  · simp [hz]

/-- The per-fiber collision hypothesis is the only encoder-energy premise. -/
theorem weightedLift_energy (outside : C → O) (m : ℕ)
    (w : C → D → ℝ) (c : ℝ)
    (hcollision : ∀ o, rawFiberSum outside (fun x => ∑ d, w x d ^ 2) o ≤ c)
    (f : O → ℝ) :
    (∑ x, ∑ d, weightedLift outside m w f x d ^ 2) ≤
      (c / (m : ℝ)) * ∑ o, f o ^ 2 := by
  rw [weightedLift_energy_eq]
  calc
    _ ≤ ∑ o, (f o ^ 2 / (m : ℝ)) * c :=
      Finset.sum_le_sum (fun o _ => mul_le_mul_of_nonneg_left
        (hcollision o) (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      ring

/-- The finite-sum transpose identity, valid for signed inputs. -/
theorem weightedAdjoint_pairing (outside : C → O) (m : ℕ)
    (w : C → D → ℝ) (f : O → ℝ) (g : C → D → ℝ) :
    (∑ o, f o * weightedAdjoint outside m w g o) =
      ∑ c, ∑ d, weightedLift outside m w f c d * g c d := by
  unfold weightedAdjoint
  rw [← normalizedAdjoint_pairing]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [weightedLift]
  ring

/-- A transpose inherits the encoder estimate by finite Cauchy--Schwarz.
This derives the adjoint estimate rather than assuming an operator bound. -/
theorem weightedAdjoint_energy (outside : C → O) (m : ℕ)
    (w : C → D → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcollision : ∀ o, rawFiberSum outside (fun x => ∑ d, w x d ^ 2) o ≤ c)
    (g : C → D → ℝ) :
    (∑ o, weightedAdjoint outside m w g o ^ 2) ≤
      (c / (m : ℝ)) * ∑ x, ∑ d, g x d ^ 2 := by
  let h := weightedAdjoint outside m w g
  let s : ℝ := ∑ o, h o ^ 2
  let t : ℝ := ∑ x, ∑ d, g x d ^ 2
  have hs : 0 ≤ s := Finset.sum_nonneg (fun o _ => sq_nonneg _)
  have ht : 0 ≤ t := Finset.sum_nonneg (fun x _ =>
    Finset.sum_nonneg (fun d _ => sq_nonneg _))
  have hpair : s = ∑ x, ∑ d, weightedLift outside m w h x d * g x d := by
    simpa only [s, h, pow_two] using weightedAdjoint_pairing outside m w h g
  have hcs : s ^ 2 ≤
      (∑ x, ∑ d, weightedLift outside m w h x d ^ 2) * t := by
    rw [hpair]
    simpa only [Fintype.sum_prod_type, t] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun z : C × D => weightedLift outside m w h z.1 z.2)
        (fun z : C × D => g z.1 z.2))
  have hbound : s * s ≤ ((c / (m : ℝ)) * t) * s := by
    calc
      _ = s ^ 2 := by ring
      _ ≤ _ := hcs
      _ ≤ ((c / (m : ℝ)) * s) * t := mul_le_mul_of_nonneg_right
        (weightedLift_energy outside m w c hcollision h) ht
      _ = _ := by ring
  by_cases hz : s = 0
  · change s ≤ (c / (m : ℝ)) * t
    rw [hz]
    exact mul_nonneg (div_nonneg hc (Nat.cast_nonneg _)) ht
  · have hpos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    exact le_of_mul_le_mul_right hbound hpos

end WeightedFibers

section InformationCoordinates
variable {A B E V OL OR : Type*}
  [Fintype A] [Fintype B] [Fintype E] [Fintype V]
  [Fintype OL] [Fintype OR]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]
  [DecidableEq OL] [DecidableEq OR]

/-- Product of actual local column energies at the right codeword. -/
def columnEnergy
    (leftCode : ((B → V) × (E → V)) → A → V)
    (KA : A → V → V → ℝ) (x : (B → V) × (E → V)) : ℝ :=
  ∏ a, ∑ v, KA a v (leftCode x a) ^ 2

/-- Product of actual local row energies at the left codeword. -/
def rowEnergy
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ) (y : (A → V) × (B → V)) : ℝ :=
  ∏ e, ∑ v, KE e (rightCode y e) v ^ 2

theorem columnEnergy_eq
    (leftCode : ((B → V) × (E → V)) → A → V)
    (KA : A → V → V → ℝ) (x : (B → V) × (E → V)) :
    columnEnergy leftCode KA x =
      ∑ a : A → V, (∏ i, KA i (a i) (leftCode x i)) ^ 2 := by
  simp only [columnEnergy, ← Finset.prod_pow]
  exact Fintype.prod_sum _

theorem rowEnergy_eq
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ) (y : (A → V) × (B → V)) :
    rowEnergy rightCode KE y =
      ∑ e : E → V, (∏ i, KE i (rightCode y i) (e i)) ^ 2 := by
  simp only [rowEnergy, ← Finset.prod_pow]
  exact Fintype.prod_sum _

/-- Literal normalized overlap `J_L^* K J_R`, without an isometry premise. -/
def normalizedOverlap
    (outsideL : ((A → V) × (B → V)) → OL)
    (outsideR : ((B → V) × (E → V)) → OR) (mL mR : ℕ)
    (leftCode : ((B → V) × (E → V)) → A → V)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KA : A → V → V → ℝ) (KB : B → V → V → ℝ)
    (KE : E → V → V → ℝ) (f : OR → ℝ) : OL → ℝ :=
  normalizedAdjoint outsideL mL
    (action (InformationOverlap.kernel leftCode rightCode KA KB KE)
      (normalizedLift outsideR mR f))

/-- The right encoder, keeping both right information-coordinate sets. -/
def rightEncoder
    (outsideR : ((B → V) × (E → V)) → OR) (mR : ℕ)
    (leftCode : ((B → V) × (E → V)) → A → V)
    (KA : A → V → V → ℝ) (f : OR → ℝ) :=
  InformationOverlap.leftStage leftCode KA (normalizedLift outsideR mR f)

/-- The left encoder retains both left information-coordinate sets. -/
def leftEncoder
    (outsideL : ((A → V) × (B → V)) → OL) (mL : ℕ)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ) (f : OL → ℝ)
    (a : A → V) (b : B → V) (e : E → V) : ℝ :=
  (∏ i, KE i (rightCode (a,b) i) (e i)) * normalizedLift outsideL mL f (a,b)

/-- The left encoder's actual transpose, keeping the left information labels. -/
def leftEncoderAdjoint
    (outsideL : ((A → V) × (B → V)) → OL) (mL : ℕ)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ)
    (g : (A → V) → (B → V) → (E → V) → ℝ) : OL → ℝ :=
  normalizedAdjoint outsideL mL (InformationOverlap.rightStage rightCode KE g)

/-- The left encoder and its named transpose have the signed pairing claimed
by the manuscript; this is derived from the literal finite sums. -/
theorem leftEncoder_pairing
    (outsideL : ((A → V) × (B → V)) → OL) (mL : ℕ)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ) (f : OL → ℝ)
    (g : (A → V) → (B → V) → (E → V) → ℝ) :
    (∑ l, f l * leftEncoderAdjoint outsideL mL rightCode KE g l) =
      ∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
        leftEncoder outsideL mL rightCode KE f a b e * g a b e := by
  unfold leftEncoderAdjoint InformationOverlap.rightStage
  simpa only [Fintype.sum_prod_type, weightedLift, weightedAdjoint,
    leftEncoder] using
    weightedAdjoint_pairing outsideL mL
      (fun (y : (A → V) × (B → V)) (e : E → V) =>
        ∏ i, KE i (rightCode y i) (e i)) f
      (fun y e => g y.1 y.2 e)

/-- Expanding the actual normalized overlap gives the encoder factorization. -/
theorem normalizedOverlap_factor
    (outsideL : ((A → V) × (B → V)) → OL)
    (outsideR : ((B → V) × (E → V)) → OR) (mL mR : ℕ)
    (leftCode : ((B → V) × (E → V)) → A → V)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KA : A → V → V → ℝ) (KB : B → V → V → ℝ)
    (KE : E → V → V → ℝ) (f : OR → ℝ) :
    normalizedOverlap outsideL outsideR mL mR leftCode rightCode KA KB KE f =
      leftEncoderAdjoint outsideL mL rightCode KE
        (InformationOverlap.middleStage KB
          (rightEncoder outsideR mR leftCode KA f)) := by
  have hfactor :
      action (InformationOverlap.kernel leftCode rightCode KA KB KE)
          (normalizedLift outsideR mR f) =
        InformationOverlap.rightStage rightCode KE
          (InformationOverlap.middleStage KB
            (InformationOverlap.leftStage leftCode KA (normalizedLift outsideR mR f))) := by
    funext y
    exact InformationOverlap.action_factor leftCode rightCode KA KB KE _ y
  simp only [normalizedOverlap, leftEncoderAdjoint, rightEncoder, hfactor]

/-- Right encoder bound from column collision sums on each outside fiber. -/
theorem rightEncoder_energy
    (outsideR : ((B → V) × (E → V)) → OR) (mR : ℕ)
    (leftCode : ((B → V) × (E → V)) → A → V)
    (KA : A → V → V → ℝ) (cR : ℝ)
    (hR : ∀ r, rawFiberSum outsideR (columnEnergy leftCode KA) r ≤ cR)
    (f : OR → ℝ) :
    (∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
      rightEncoder outsideR mR leftCode KA f a b e ^ 2) ≤
      (cR / (mR : ℝ)) * ∑ r, f r ^ 2 := by
  have he := weightedLift_energy outsideR mR
    (fun (x : (B → V) × (E → V)) (a : A → V) =>
      ∏ i, KA i (a i) (leftCode x i)) cR
    (by simpa only [← columnEnergy_eq] using hR) f
  calc
    _ = ∑ b : B → V, ∑ e : E → V, ∑ a : A → V,
        rightEncoder outsideR mR leftCode KA f a b e ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ ≤ _ := by
      simpa only [Fintype.sum_prod_type, weightedLift, rightEncoder,
        InformationOverlap.leftStage] using he

/-- Left encoder bound from the same explicit row collision sums. -/
theorem leftEncoder_energy
    (outsideL : ((A → V) × (B → V)) → OL) (mL : ℕ)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ) (cL : ℝ)
    (hL : ∀ l, rawFiberSum outsideL (rowEnergy rightCode KE) l ≤ cL)
    (f : OL → ℝ) :
    (∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
      leftEncoder outsideL mL rightCode KE f a b e ^ 2) ≤
      (cL / (mL : ℝ)) * ∑ l, f l ^ 2 := by
  have he := weightedLift_energy outsideL mL
    (fun (y : (A → V) × (B → V)) (e : E → V) =>
      ∏ i, KE i (rightCode y i) (e i)) cL
    (by simpa only [← rowEnergy_eq] using hL) f
  simpa only [Fintype.sum_prod_type, weightedLift, leftEncoder] using he

/-- Left adjoint bound from row collision sums on each outside fiber. -/
theorem leftEncoderAdjoint_energy
    (outsideL : ((A → V) × (B → V)) → OL) (mL : ℕ)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KE : E → V → V → ℝ) (cL : ℝ) (hcL : 0 ≤ cL)
    (hL : ∀ l, rawFiberSum outsideL (rowEnergy rightCode KE) l ≤ cL)
    (g : (A → V) → (B → V) → (E → V) → ℝ) :
    (∑ l, leftEncoderAdjoint outsideL mL rightCode KE g l ^ 2) ≤
      (cL / (mL : ℝ)) *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V, g a b e ^ 2 := by
  unfold leftEncoderAdjoint InformationOverlap.rightStage
  have he := weightedAdjoint_energy outsideL mL
    (fun (y : (A → V) × (B → V)) (e : E → V) =>
      ∏ i, KE i (rightCode y i) (e i)) cL hcL
    (by simpa only [← rowEnergy_eq] using hL)
    (fun y e => g y.1 y.2 e)
  simpa only [Fintype.sum_prod_type, weightedAdjoint] using he

/-- Signed normalized overlap energy with the two fiber averages retained. -/
theorem normalized_overlap_energy
    (outsideL : ((A → V) × (B → V)) → OL)
    (outsideR : ((B → V) × (E → V)) → OR) (mL mR : ℕ)
    (leftCode : ((B → V) × (E → V)) → A → V)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KA : A → V → V → ℝ) (KB : B → V → V → ℝ)
    (KE : E → V → V → ℝ) (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (nu : B → ℝ)
    (hL : ∀ l, rawFiberSum outsideL (rowEnergy rightCode KE) l ≤ cL)
    (hR : ∀ r, rawFiberSum outsideR (columnEnergy leftCode KA) r ≤ cR)
    (hKB : ∀ b g, (∑ y, action (KB b) g y ^ 2) ≤
      nu b ^ 2 * ∑ x, g x ^ 2) (f : OR → ℝ) :
    (∑ l, normalizedOverlap outsideL outsideR mL mR leftCode rightCode KA KB KE f l ^ 2) ≤
      (cL * cR / ((mL : ℝ) * (mR : ℝ))) *
        (∏ b, nu b) ^ 2 * ∑ r, f r ^ 2 := by
  rw [normalizedOverlap_factor]
  calc
    _ ≤ (cL / (mL : ℝ)) *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
          InformationOverlap.middleStage KB
            (rightEncoder outsideR mR leftCode KA f) a b e ^ 2 :=
      leftEncoderAdjoint_energy outsideL mL rightCode KE cL hcL hL _
    _ ≤ (cL / (mL : ℝ)) * ((∏ b, nu b) ^ 2 *
        ∑ a : A → V, ∑ b : B → V, ∑ e : E → V,
          rightEncoder outsideR mR leftCode KA f a b e ^ 2) :=
      mul_le_mul_of_nonneg_left (InformationOverlap.middleStage_energy KB nu hKB _)
        (div_nonneg hcL (Nat.cast_nonneg _))
    _ ≤ (cL / (mL : ℝ)) * ((∏ b, nu b) ^ 2 *
        ((cR / (mR : ℝ)) * ∑ r, f r ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (rightEncoder_energy outsideR mR leftCode KA cR hR f)
          (sq_nonneg _)) (div_nonneg hcL (Nat.cast_nonneg _))
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The paper's normalized counting-norm bound, on arbitrary signed input. -/
theorem normalized_overlap_l2
    (outsideL : ((A → V) × (B → V)) → OL)
    (outsideR : ((B → V) × (E → V)) → OR) (mL mR : ℕ)
    (leftCode : ((B → V) × (E → V)) → A → V)
    (rightCode : ((A → V) × (B → V)) → E → V)
    (KA : A → V → V → ℝ) (KB : B → V → V → ℝ)
    (KE : E → V → V → ℝ) (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (nu : B → ℝ) (hnu : ∀ b, 0 ≤ nu b)
    (hL : ∀ l, rawFiberSum outsideL (rowEnergy rightCode KE) l ≤ cL)
    (hR : ∀ r, rawFiberSum outsideR (columnEnergy leftCode KA) r ≤ cR)
    (hKB : ∀ b g, (∑ y, action (KB b) g y ^ 2) ≤
      nu b ^ 2 * ∑ x, g x ^ 2) (f : OR → ℝ) :
    l2 (normalizedOverlap outsideL outsideR mL mR leftCode rightCode KA KB KE f) ≤
      (Real.sqrt (cL * cR / ((mL : ℝ) * (mR : ℝ))) * (∏ b, nu b)) * l2 f := by
  have hc : 0 ≤ cL * cR / ((mL : ℝ) * (mR : ℝ)) :=
    div_nonneg (mul_nonneg hcL hcR) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  apply l2_le_of_energy _ f _
    (mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg (fun b _ => hnu b)))
  simpa only [mul_pow, Real.sq_sqrt hc, mul_assoc] using
    normalized_overlap_energy outsideL outsideR mL mR leftCode rightCode KA KB KE
      cL cR hcL hcR nu hL hR hKB f

end InformationCoordinates
end AES8.PaperInformationOverlap
