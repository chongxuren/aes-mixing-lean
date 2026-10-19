import AESConcrete.ActivityFrame

/-!
# Exact effective input activity metric

The starting kernel is the actual normalized activity-frame Gram.  Its empty
and full mask block is eliminated by an exact completed-square identity for
arbitrary sixteen real coefficients.  The resulting lower bound is a metric
fact, independent of any residual Gram estimate or diagonal-dominance claim.
Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityEffectiveMetric
open AESMixing
open AESMixing.AES (maskBit maskSize)

set_option maxRecDepth 100000

def xi : ℝ := 1 / 16
def t : ℝ := xi^4
def det : ℝ := 1-t^2

def activityMetric (A B : Fin 16) : ℝ :=
  ActivityFrame.frameMetric (maskBit A) (maskBit B)

def k0 (A : Fin 16) : ℝ := xi^(maskSize A)
def k1 (A : Fin 16) : ℝ := xi^(4-maskSize A)

abbrev Interior := {A : Fin 16 // A ≠ 0 ∧ A ≠ 15}

def qForm {I : Type*} [Fintype I] (u : I → ℝ) (K : I → I → ℝ) : ℝ :=
  ∑ A : I, ∑ B : I, u A*u B*K A B

def fullEnergy (u : Fin 16 → ℝ) : ℝ := qForm u activityMetric
def interiorEnergy (u : Fin 16 → ℝ) : ℝ :=
  qForm (fun A : Interior => u A.val) (fun A B => activityMetric A.val B.val)
def r0 (u : Fin 16 → ℝ) : ℝ := ∑ A : Interior, u A.val*k0 A.val
def r1 (u : Fin 16 → ℝ) : ℝ := ∑ A : Interior, u A.val*k1 A.val

def rankCorrection (A B : Fin 16) : ℝ :=
  k0 A*k0 B + k1 A*k1 B - t*(k0 A*k1 B + k1 A*k0 B)

def effectiveMetric (A B : Fin 16) : ℝ :=
  activityMetric A B - rankCorrection A B / det

def effectiveEnergy (u : Fin 16 → ℝ) : ℝ :=
  qForm (fun A : Interior => u A.val) (fun A B => effectiveMetric A.val B.val)

set_option maxRecDepth 100000 in
private theorem mismatch_count : ∀ A B : Fin 16,
    (Finset.univ.filter (fun i : Fin 4 => maskBit A i ≠ maskBit B i)).card =
      maskSize A + maskSize B - 2*maskSize (maskIntersection A B) := by decide

private theorem mask_size_bound : ∀ A : Fin 16, maskSize A ≤ 4 := by decide
private theorem distance_empty : ∀ A : Fin 16,
    maskSize 0 + maskSize A - 2*maskSize (maskIntersection 0 A) = maskSize A := by decide
private theorem distance_full : ∀ A : Fin 16,
    maskSize 15 + maskSize A - 2*maskSize (maskIntersection 15 A) = 4-maskSize A := by decide

/-- The entry formula is proved from the actual tensor frame metric. -/
theorem activityMetric_formula (A B : Fin 16) :
    activityMetric A B = xi^(maskSize A + maskSize B - 2*maskSize (maskIntersection A B)) := by
  change (∏ i : Fin 4, if maskBit A i = maskBit B i then (1 : ℝ) else xi) = _
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [mismatch_count]

theorem activityMetric_symmetric (A B : Fin 16) : activityMetric A B = activityMetric B A := by
  unfold activityMetric ActivityFrame.frameMetric
  apply Finset.prod_congr rfl
  intro i _
  exact ActivityFrame.byteMetric_symmetric _ _

theorem activityMetric_self (A : Fin 16) : activityMetric A A = 1 := by
  simp [activityMetric, ActivityFrame.frameMetric, ActivityFrame.byteMetric]

theorem activityMetric_empty_left (A : Fin 16) : activityMetric 0 A = k0 A := by
  rw [activityMetric_formula, distance_empty]
  rfl

theorem activityMetric_empty_right (A : Fin 16) : activityMetric A 0 = k0 A := by
  rw [activityMetric_symmetric]
  exact activityMetric_empty_left A

theorem activityMetric_full_left (A : Fin 16) : activityMetric 15 A = k1 A := by
  rw [activityMetric_formula, distance_full]
  rfl

theorem activityMetric_full_right (A : Fin 16) : activityMetric A 15 = k1 A := by
  rw [activityMetric_symmetric]
  exact activityMetric_full_left A

theorem activityMetric_empty_full : activityMetric 0 15 = t := by
  rw [activityMetric_empty_left]
  norm_num [k0, t, show maskSize (15 : Fin 16) = 4 by decide]

theorem det_pos : 0 < det := by norm_num [det, t, xi]

/-- Split the two boundary labels from the fourteen retained labels. -/
theorem sum_split (f : Fin 16 → ℝ) :
    (∑ A : Fin 16, f A) = f 0 + f 15 + ∑ A : Interior, f A.val := by
  classical
  have hi : (∑ A : Interior, f A.val) =
      ∑ A : Fin 16, if A ≠ 0 ∧ A ≠ 15 then f A else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hp (A : Fin 16) : f A =
      (if A = 0 then f 0 else 0) + (if A = 15 then f 15 else 0) +
        (if A ≠ 0 ∧ A ≠ 15 then f A else 0) := by
    by_cases h0 : A = 0
    · subst A; simp
    by_cases h15 : A = 15
    · subst A; simp
    · simp [h0, h15]
  calc
    _ = ∑ A : Fin 16, ((if A = 0 then f 0 else 0) + (if A = 15 then f 15 else 0) +
        (if A ≠ 0 ∧ A ≠ 15 then f A else 0)) := Finset.sum_congr rfl (fun A _ => hp A)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← hi]

/-- Actual boundary block and its couplings, before eliminating anything. -/
theorem fullEnergy_split (u : Fin 16 → ℝ) :
    fullEnergy u = interiorEnergy u + u 0^2 + 2*t*u 0*u 15 + u 15^2 +
      2*u 0*r0 u + 2*u 15*r1 u := by
  have h0l : (∑ A : Interior, u 0*u A.val*activityMetric 0 A.val) = u 0*r0 u := by
    rw [r0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [activityMetric_empty_left]
    ring
  have h1l : (∑ A : Interior, u 15*u A.val*activityMetric 15 A.val) = u 15*r1 u := by
    rw [r1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [activityMetric_full_left]
    ring
  have h0r : (∑ A : Interior, u A.val*u 0*activityMetric A.val 0) = u 0*r0 u := by
    rw [r0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [activityMetric_empty_right]
    ring
  have h1r : (∑ A : Interior, u A.val*u 15*activityMetric A.val 15) = u 15*r1 u := by
    rw [r1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    rw [activityMetric_full_right]
    ring
  unfold fullEnergy qForm
  simp_rw [sum_split]
  simp only [Finset.sum_add_distrib]
  rw [h0l, h1l, h0r, h1r, activityMetric_self, activityMetric_self,
    activityMetric_empty_full, activityMetric_symmetric 15 0, activityMetric_empty_full]
  unfold interiorEnergy qForm
  ring

private theorem qForm_rank {I : Type*} [Fintype I] (u a b : I → ℝ) :
    qForm u (fun A B => a A*b B) = (∑ A : I, u A*a A)*(∑ B : I, u B*b B) := by
  unfold qForm
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  ring

theorem rankCorrection_energy (u : Fin 16 → ℝ) :
    qForm (fun A : Interior => u A.val) (fun A B => rankCorrection A.val B.val) =
      (r0 u)^2 + (r1 u)^2 - 2*t*r0 u*r1 u := by
  have hp (A B : Interior) : u A.val*u B.val*rankCorrection A.val B.val =
      u A.val*u B.val*(k0 A.val*k0 B.val) + u A.val*u B.val*(k1 A.val*k1 B.val) -
        t*(u A.val*u B.val*(k0 A.val*k1 B.val) + u A.val*u B.val*(k1 A.val*k0 B.val)) := by
    unfold rankCorrection
    ring
  unfold qForm
  change (∑ A : Interior, ∑ B : Interior, u A.val*u B.val*rankCorrection A.val B.val) = _
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change qForm (fun A : Interior => u A.val) (fun A B => k0 A.val*k0 B.val) +
      qForm (fun A : Interior => u A.val) (fun A B => k1 A.val*k1 B.val) -
      t*(qForm (fun A : Interior => u A.val) (fun A B => k0 A.val*k1 B.val) +
        qForm (fun A : Interior => u A.val) (fun A B => k1 A.val*k0 B.val)) = _
  rw [qForm_rank, qForm_rank, qForm_rank, qForm_rank]
  unfold r0 r1
  ring

/-- Exact Schur quadratic obtained by eliminating the boundary block. -/
theorem effectiveEnergy_eq (u : Fin 16 → ℝ) :
    effectiveEnergy u = interiorEnergy u -
      ((r0 u)^2 + (r1 u)^2 - 2*t*r0 u*r1 u) / det := by
  unfold effectiveEnergy qForm effectiveMetric
  simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div]
  change interiorEnergy u -
      qForm (fun A : Interior => u A.val) (fun A B => rankCorrection A.val B.val) / det = _
  rw [rankCorrection_energy]

/-- Exact completed-square identity for arbitrary sixteen coefficients. -/
theorem completed_square (u : Fin 16 → ℝ) :
    fullEnergy u = effectiveEnergy u + (u 0+t*u 15+r0 u)^2 +
      det*(u 15+(r1 u-t*r0 u)/det)^2 := by
  rw [fullEnergy_split, effectiveEnergy_eq]
  field_simp [ne_of_gt det_pos]
  unfold det
  ring

theorem effectiveEnergy_le_fullEnergy (u : Fin 16 → ℝ) : effectiveEnergy u ≤ fullEnergy u := by
  rw [completed_square]
  have h0 := sq_nonneg (u 0+t*u 15+r0 u)
  have h1 := mul_nonneg (le_of_lt det_pos) (sq_nonneg (u 15+(r1 u-t*r0 u)/det))
  linarith

/-- The explicit entry formula from the four-coordinate activity sizes.
All exponent subtraction is bounded by the proved mask-size limits. -/
theorem effectiveMetric_formula (A B : Fin 16) :
    effectiveMetric A B =
      xi^(maskSize A+maskSize B-2*maskSize (maskIntersection A B)) -
      (xi^(maskSize A+maskSize B) + xi^(8-(maskSize A+maskSize B)) -
        xi^((8+maskSize A)-maskSize B) - xi^((8-maskSize A)+maskSize B)) / (1-xi^8) := by
  have hA := mask_size_bound A
  have hB := mask_size_bound B
  have h00 : k0 A*k0 B = xi^(maskSize A+maskSize B) := by
    unfold k0
    rw [← pow_add]
  have h11 : k1 A*k1 B = xi^(8-(maskSize A+maskSize B)) := by
    unfold k1
    rw [← pow_add]
    congr 1
    omega
  have h01 : t*(k0 A*k1 B) = xi^((8+maskSize A)-maskSize B) := by
    unfold t k0 k1
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h10 : t*(k1 A*k0 B) = xi^((8-maskSize A)+maskSize B) := by
    unfold t k0 k1
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hd : det = 1-xi^8 := by
    unfold det t
    rw [← pow_mul]
  have hn : rankCorrection A B =
      xi^(maskSize A+maskSize B) + xi^(8-(maskSize A+maskSize B)) -
        xi^((8+maskSize A)-maskSize B) - xi^((8-maskSize A)+maskSize B) := by
    unfold rankCorrection
    rw [mul_add, h00, h11, h01, h10]
    ring
  unfold effectiveMetric
  rw [activityMetric_formula, hn, hd]

/-- The quadratic is the energy of the actual normalized four-byte frame,
proved from its existing Gram theorem, not postulated as a metric formula. -/
theorem actual_frame_energy (u : Fin 16 → ℝ) :
    (∑ x : Fin 4 → BinaryWord 8,
      (∑ A : Fin 16, ActivityFrame.frameColumn (maskBit A) x*u A)^2) = fullEnergy u := by
  rw [gram_quadratic]
  simp only [gram, ActivityFrame.frame_gram (V := BinaryWord 8) (by norm_num [BinaryWord.card])]
  rfl

theorem actual_frame_energy_ge_effective (u : Fin 16 → ℝ) :
    effectiveEnergy u ≤ ∑ x : Fin 4 → BinaryWord 8,
      (∑ A : Fin 16, ActivityFrame.frameColumn (maskBit A) x*u A)^2 := by
  rw [actual_frame_energy]
  exact effectiveEnergy_le_fullEnergy u

end AESConcrete.ActivityEffectiveMetric
