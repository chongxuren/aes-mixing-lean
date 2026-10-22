import AESRound.Recurrence
import AESRound.AllRounds
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.FieldSimp

/-!
# From block operators to the profile recurrence

This file proves a generic analytic bridge.  Its hypotheses concern vectors,
continuous linear maps, exact decomposition identities, and operator norms.
Neither the coordinate recurrence nor a final scalar error bound is assumed.

For the intended AES application, the blocks are `P_(i,t) f_(4+2n)`;
`step`, `low`, and `ret` represent the appropriate projected one-step,
low-degree, and two-step high-degree-return maps.  The exact decompositions
must still be instantiated from the AES projections and memory identity.  The
local AES estimates, initialization, and terminal TV conversion remain separate
obligations.  This is constructive bound formalization, not attack development.
-/

noncomputable section

namespace AESRound.OperatorBridge

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual vector-valued blocks and two exact ways to evolve them.  The maps
are not numerical majorants: their actions reconstruct the actual next block.
The memory decomposition has the explicit indices `n+2`, `n+1`, and `n`. -/
structure BlockEvolution (ι E : Type*) [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  blocks : ℕ → ι → E
  step : ι → ι → E →L[ℝ] E
  low : ι → ι → E →L[ℝ] E
  ret : ι → ι → E →L[ℝ] E
  step_decomposition : ∀ n i,
    blocks (n + 1) i = ∑ j, step i j (blocks n j)
  memory_decomposition : ∀ n i,
    blocks (n + 2) i =
      (∑ j, low i j (blocks (n + 1) j)) +
      ∑ j, ret i j (blocks n j)

/-- The generic triangle-inequality step; term bounds follow from genuine
operator-norm bounds, not from any hypothesis about component profiles. -/
theorem norm_sum_maps_le (maps : ι → E →L[ℝ] E)
    (vectors : ι → E) (caps : ι → ℝ)
    (hcaps : ∀ j, ‖maps j‖ ≤ caps j) :
    ‖∑ j, maps j (vectors j)‖ ≤ ∑ j, caps j * ‖vectors j‖ := by
  calc
    ‖∑ j, maps j (vectors j)‖ ≤ ∑ j, ‖maps j (vectors j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, caps j * ‖vectors j‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact le_trans ((maps j).le_opNorm (vectors j))
        (mul_le_mul_of_nonneg_right (hcaps j) (norm_nonneg _))

def blockProfile (blocks : ℕ → ι → E) : ℕ → Profile ι :=
  fun n i => ‖blocks n i‖

omit [Fintype ι] [NormedSpace ℝ E] in
theorem blockProfile_nonneg (blocks : ℕ → ι → E) :
    ∀ n i, 0 ≤ blockProfile blocks n i := by
  intro n i
  exact norm_nonneg _

namespace BlockEvolution

variable (G : BlockEvolution ι E)

theorem one_step_bound {A : ι → ι → ℝ}
    (hA : ∀ i j, ‖G.step i j‖ ≤ A i j) (n : ℕ) :
    blockProfile G.blocks (n + 1) ≤ matVec A (blockProfile G.blocks n) := by
  intro i
  change ‖G.blocks (n + 1) i‖ ≤ ∑ j, A i j * ‖G.blocks n j‖
  rw [G.step_decomposition n i]
  exact norm_sum_maps_le (G.step i) (G.blocks n) (A i) (hA i)

theorem memory_bound {B C : ι → ι → ℝ}
    (hB : ∀ i j, ‖G.low i j‖ ≤ B i j)
    (hC : ∀ i j, ‖G.ret i j‖ ≤ C i j) (n : ℕ) :
    blockProfile G.blocks (n + 2) ≤ fun i =>
      matVec B (blockProfile G.blocks (n + 1)) i +
      matVec C (blockProfile G.blocks n) i := by
  intro i
  change ‖G.blocks (n + 2) i‖ ≤
    (∑ j, B i j * ‖G.blocks (n + 1) j‖) +
    ∑ j, C i j * ‖G.blocks n j‖
  rw [G.memory_decomposition n i]
  exact le_trans (norm_add_le _ _)
    (add_le_add
      (norm_sum_maps_le (G.low i) (G.blocks (n + 1)) (B i) (hB i))
      (norm_sum_maps_le (G.ret i) (G.blocks n) (C i) (hC i)))

/-- The coordinatewise minimum is derived from the two exact decompositions.
The matrices are operator-norm caps, not hypotheses asserting this conclusion. -/
theorem unscaled_recurrence {A B C : ι → ι → ℝ}
    (hA : ∀ i j, ‖G.step i j‖ ≤ A i j)
    (hB : ∀ i j, ‖G.low i j‖ ≤ B i j)
    (hC : ∀ i j, ‖G.ret i j‖ ≤ C i j) :
    ∀ n, blockProfile G.blocks (n + 2) ≤
      comparisonStep A B C (blockProfile G.blocks (n + 1))
        (blockProfile G.blocks n) := by
  intro n i
  apply le_min
  · simpa only [Nat.add_assoc] using (G.one_step_bound hA (n + 1)) i
  · exact (G.memory_bound hB hC n) i

end BlockEvolution

/-- In the AES application, `K = 2^80 = q^(5/2)` and `rate = lambda⁻¹`.
Using inverse powers makes the two distinct memory normalizations explicit. -/
def scaledProfile (blocks : ℕ → ι → E) (K rate : ℝ) : ℕ → Profile ι :=
  fun n i => (K * rate ^ n) * ‖blocks n i‖

omit [Fintype ι] [NormedSpace ℝ E] in
theorem scaledProfile_nonneg (blocks : ℕ → ι → E) {K rate : ℝ}
    (hK : 0 ≤ K) (hrate : 0 ≤ rate) :
    ∀ n i, 0 ≤ scaledProfile blocks K rate n i := by
  intro n i
  exact mul_nonneg (mul_nonneg hK (pow_nonneg hrate n)) (norm_nonneg _)

namespace BlockEvolution

variable (G : BlockEvolution ι E)

/-- Normalization is proved from the actual vector laws.  The one-step and
low terms acquire one factor of `rate`; the return acquires two factors. -/
theorem scaled_recurrence {A B C : ι → ι → ℝ} {K rate : ℝ}
    (hK : 0 ≤ K) (hrate : 0 ≤ rate)
    (hA : ∀ i j, ‖G.step i j‖ ≤ A i j)
    (hB : ∀ i j, ‖G.low i j‖ ≤ B i j)
    (hC : ∀ i j, ‖G.ret i j‖ ≤ C i j) :
    ∀ n, scaledProfile G.blocks K rate (n + 2) ≤
      comparisonStep (fun i j => rate * A i j)
        (fun i j => rate * B i j) (fun i j => rate ^ 2 * C i j)
        (scaledProfile G.blocks K rate (n + 1))
        (scaledProfile G.blocks K rate n) := by
  intro n i
  have hfactor : 0 ≤ K * rate ^ (n + 2) :=
    mul_nonneg hK (pow_nonneg hrate _)
  apply le_min
  · calc
      scaledProfile G.blocks K rate (n + 2) i ≤
          (K * rate ^ (n + 2)) *
            matVec A (blockProfile G.blocks (n + 1)) i := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Nat.add_assoc, blockProfile] using
            (G.one_step_bound hA (n + 1)) i)
          hfactor
      _ = matVec (fun i j => rate * A i j)
          (scaledProfile G.blocks K rate (n + 1)) i := by
        simp only [matVec, blockProfile, scaledProfile, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [pow_succ]
        ring
  · calc
      scaledProfile G.blocks K rate (n + 2) i ≤
          (K * rate ^ (n + 2)) *
            (matVec B (blockProfile G.blocks (n + 1)) i +
              matVec C (blockProfile G.blocks n) i) :=
        mul_le_mul_of_nonneg_left ((G.memory_bound hB hC n) i) hfactor
      _ = matVec (fun i j => rate * B i j)
            (scaledProfile G.blocks K rate (n + 1)) i +
          matVec (fun i j => rate ^ 2 * C i j)
            (scaledProfile G.blocks K rate n) i := by
        rw [mul_add]
        congr 1
        · simp only [matVec, blockProfile, scaledProfile, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [pow_succ]
          ring
        · simp only [matVec, blockProfile, scaledProfile, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [pow_succ]
          ring

end BlockEvolution

theorem first_normalization (q lambda b : ℝ) (hq : q ≠ 0) (h_lambda : lambda ≠ 0) :
    lambda⁻¹ * (b / q) = b / (q * lambda) := by
  field_simp [hq, h_lambda]

theorem return_normalization (q lambda c : ℝ) (hq : q ≠ 0) (h_lambda : lambda ≠ 0) :
    (lambda⁻¹) ^ 2 * (c / q ^ 3) = c / (q ^ 3 * lambda ^ 2) := by
  field_simp [hq, h_lambda]

namespace BlockEvolution

variable (G : BlockEvolution ι E)

/-- The source normalization, with actual block caps scaled by q and q³.
`Bminus` is the one-step matrix with the high-source-degree columns removed.
At `K=2^80` and `lambda=101/2^48`, this has exactly the scaling required by
`ProfileInterface.recurrence`. -/
theorem q_scaled_recurrence {B Bminus C : ι → ι → ℝ} {K q lambda : ℝ}
    (hK : 0 ≤ K) (hq : 0 < q) (h_lambda : 0 < lambda)
    (hB : ∀ i j, ‖G.step i j‖ ≤ B i j / q)
    (hBminus : ∀ i j, ‖G.low i j‖ ≤ Bminus i j / q)
    (hC : ∀ i j, ‖G.ret i j‖ ≤ C i j / q ^ 3) :
    ∀ n, scaledProfile G.blocks K lambda⁻¹ (n + 2) ≤
      comparisonStep (fun i j => B i j / (q * lambda))
        (fun i j => Bminus i j / (q * lambda))
        (fun i j => C i j / (q ^ 3 * lambda ^ 2))
        (scaledProfile G.blocks K lambda⁻¹ (n + 1))
        (scaledProfile G.blocks K lambda⁻¹ n) := by
  have h := G.scaled_recurrence hK (inv_nonneg.mpr h_lambda.le) hB hBminus hC
  have hfirst : (fun i j => lambda⁻¹ * (B i j / q)) =
      (fun i j => B i j / (q * lambda)) := by
    funext i j
    exact first_normalization q lambda (B i j) hq.ne' h_lambda.ne'
  have hlow : (fun i j => lambda⁻¹ * (Bminus i j / q)) =
      (fun i j => Bminus i j / (q * lambda)) := by
    funext i j
    exact first_normalization q lambda (Bminus i j) hq.ne' h_lambda.ne'
  have hret : (fun i j => (lambda⁻¹) ^ 2 * (C i j / q ^ 3)) =
      (fun i j => C i j / (q ^ 3 * lambda ^ 2)) := by
    funext i j
    exact return_normalization q lambda (C i j) hq.ne' h_lambda.ne'
  simpa only [hfirst, hlow, hret] using h

end BlockEvolution

/-- A state-level wrapper exposes the remaining exact operator identities.
The map families are applied to projected state components, and their sums
must equal the actual projected first and second updates.  Proving these
identities for AES remains a separate algebraic instantiation obligation. -/
structure ProjectionSystem (ι E : Type*) [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  project : ι → E →L[ℝ] E
  update : E →L[ℝ] E
  step : ι → ι → E →L[ℝ] E
  low : ι → ι → E →L[ℝ] E
  ret : ι → ι → E →L[ℝ] E
  step_identity : ∀ v i,
    project i (update v) = ∑ j, step i j (project j v)
  memory_identity : ∀ v i,
    project i (update (update v)) =
      (∑ j, low i j (project j (update v))) +
      ∑ j, ret i j (project j v)

/-- A genuine state evolution produces the exact vector decompositions needed
above.  No coordinate norm inequality is an input to this construction. -/
def ProjectionSystem.toBlockEvolution (P : ProjectionSystem ι E)
    (state : ℕ → E) (hevolve : ∀ n, state (n + 1) = P.update (state n)) :
    BlockEvolution ι E where
  blocks := fun n i => P.project i (state n)
  step := P.step
  low := P.low
  ret := P.ret
  step_decomposition := by
    intro n i
    rw [hevolve n]
    exact P.step_identity (state n) i
  memory_decomposition := by
    intro n i
    rw [show state (n + 2) = P.update (state (n + 1)) by
      simpa only [Nat.add_assoc] using hevolve (n + 1)]
    rw [hevolve n]
    exact P.memory_identity (state n) i

/-- The AES word size is q=2^32, so q^(5/2)=2^80 exactly.  This profile uses
only an integer power and the source's explicitly fixed inverse rate. -/
def certificateProfile (G : BlockEvolution (Fin 14) E) : ℕ → Profile (Fin 14) :=
  scaledProfile G.blocks ((2 : ℝ) ^ 80) Terminal.lambda⁻¹

namespace BlockEvolution

variable (G : BlockEvolution (Fin 14) E)

/-- Operator caps in physical, unnormalized units.  Since the numerical
certificate stores L=B/(q*lambda), H=Bminus/(q*lambda), and
J=C/(q³*lambda²), these are exactly the caps B/q, Bminus/q, and C/q³.
The proved conclusion supplies `ProfileInterface.recurrence`. -/
theorem certificate_recurrence
    (hstep : ∀ i j, ‖G.step i j‖ ≤ Terminal.lambda * Certificate.L i j)
    (hlow : ∀ i j, ‖G.low i j‖ ≤ Terminal.lambda * Certificate.H i j)
    (hret : ∀ i j, ‖G.ret i j‖ ≤ Terminal.lambda ^ 2 * Certificate.J i j) :
    ∀ n, certificateProfile G (n + 2) ≤
      comparisonStep Certificate.L Certificate.H Certificate.J
        (certificateProfile G (n + 1)) (certificateProfile G n) := by
  have h_lambda : 0 < Terminal.lambda := by norm_num [Terminal.lambda]
  have h := G.scaled_recurrence
    (K := (2 : ℝ) ^ 80) (rate := Terminal.lambda⁻¹)
    (by positivity) (inv_nonneg.mpr h_lambda.le) hstep hlow hret
  have hcancel : ∀ b : ℝ,
      Terminal.lambda⁻¹ * (Terminal.lambda * b) = b := by
    intro b
    field_simp [h_lambda.ne']
  have hcancel₂ : ∀ b : ℝ,
      (Terminal.lambda⁻¹) ^ 2 * (Terminal.lambda ^ 2 * b) = b := by
    intro b
    field_simp [h_lambda.ne']
  simpa only [certificateProfile, hcancel, hcancel₂] using h

/-- The recurrence is a theorem of the block-operator data.  Initialization
and terminal conversion are independent obligations supplied explicitly here;
no scalar tail envelope or target error bound is an input. -/
def toProfileInterface (error : ℕ → ℝ) (w : Fin 4)
    (hstep : ∀ i j, ‖G.step i j‖ ≤ Terminal.lambda * Certificate.L i j)
    (hlow : ∀ i j, ‖G.low i j‖ ≤ Terminal.lambda * Certificate.H i j)
    (hret : ∀ i j, ‖G.ret i j‖ ≤ Terminal.lambda ^ 2 * Certificate.J i j)
    (hinitial₀ : certificateProfile G 0 ≤ Certificate.y w 0)
    (hinitial₁ : certificateProfile G 1 ≤ Certificate.y w 1)
    (hterminal : ∀ m, error (4 + 2 * m) ≤
      Terminal.lambda ^ m / 2 ^ 17 * Terminal.phi (certificateProfile G m)) :
    ProfileInterface error where
  w := w
  x := certificateProfile G
  nonneg := scaledProfile_nonneg G.blocks (by positivity)
    (by norm_num [Terminal.lambda])
  initial_zero := hinitial₀
  initial_one := hinitial₁
  recurrence := G.certificate_recurrence hstep hlow hret
  terminal := hterminal

/-- The requested corollaries now follow from vector-level operator hypotheses,
the separate starting estimates, and the separate TV conversion.  Instantiating
these objects and estimates for actual independently keyed AES is still open. -/
theorem operator_round_targets (error : ℕ → ℝ) (w : Fin 4)
    (hstep : ∀ i j, ‖G.step i j‖ ≤ Terminal.lambda * Certificate.L i j)
    (hlow : ∀ i j, ‖G.low i j‖ ≤ Terminal.lambda * Certificate.H i j)
    (hret : ∀ i j, ‖G.ret i j‖ ≤ Terminal.lambda ^ 2 * Certificate.J i j)
    (hinitial₀ : certificateProfile G 0 ≤ Certificate.y w 0)
    (hinitial₁ : certificateProfile G 1 ≤ Certificate.y w 1)
    (hterminal : ∀ m, error (4 + 2 * m) ≤
      Terminal.lambda ^ m / 2 ^ 17 * Terminal.phi (certificateProfile G m)) :
    error 10 < (1 : ℝ) / 2 ^ (128 : ℕ) ∧
    error 14 < (1 : ℝ) / 2 ^ (192 : ℕ) ∧
    error 16 < (1 : ℝ) / 2 ^ (256 : ℕ) :=
  (G.toProfileInterface error w hstep hlow hret hinitial₀ hinitial₁ hterminal).round_targets

end BlockEvolution

end AESRound.OperatorBridge
