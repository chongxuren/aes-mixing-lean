import AESConcrete.PhysicalProjectionSystem
import AESConcrete.DegreeResidualStep
import AESRound.CertificateData
import AESRound.Terminal

/-!
# Conditional first high-return cap

The generic high-return composition identity, norm inequality, exact scalar
comparison and actual-system conditional wrapper have distinct roles below.
The actual return through indices 11, 12 and 13 is identified exactly.

The final cap still assumes the two missing concrete step caps `(13,11)` and
`(13,12)`. This module does not discharge either assumption, and therefore
does not supply an unconditional return theorem or a complete AES theorem.
Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and the 10/14/16 target stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FirstHighReturn
open AESMixing
open AESRound.Terminal (lambda)
open AESRound.Certificate (L J)
open AESConcrete.PhysicalProjectionSystem (system decomposition isLow step_eq_physical)

local notation "ρ" => (21 / 131072 : ℝ)

section GenericComposition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sum_high_three {M : Type*} [AddCommMonoid M] (f : Fin 14 → M) :
    (∑ k : Fin 14, if decide (k.val ≤ 10) then (0 : M) else f k) =
      f 11 + f 12 + f 13 := by
  simp [Fin.sum_univ_succ, add_assoc]

/-- Generic algebra only: a fourteen-type decomposition whose high indices
are precisely 11, 12 and 13 has exactly these three composed return terms. -/
theorem ret_eq_three_steps
    (G : AESRound.ProjectionAssembly.Decomposition (Fin 14) E)
    (low : Fin 14 → Bool) (hpartition : ∀ k, low k = decide (k.val ≤ 10))
    (i j : Fin 14) :
    G.ret low i j =
      (G.step i 11).comp (G.step 11 j) +
      (G.step i 12).comp (G.step 12 j) +
      (G.step i 13).comp (G.step 13 j) := by
  rw [G.ret_eq_sum_step_comp_step]
  simp_rw [hpartition]
  exact sum_high_three (fun k => (G.step i k).comp (G.step k j))

private theorem norm_comp_le_of_caps (A B : E →L[ℝ] E) (a b : ℝ)
    (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) : ‖A.comp B‖ ≤ a * b := by
  exact (A.opNorm_comp_le B).trans
    (mul_le_mul hA hB (norm_nonneg B) ((norm_nonneg A).trans hA))

/-- The analytic triangle and composition step. Caps are attached to the
six actual operators; their nonnegativity follows from the norm premises. -/
theorem norm_three_compositions_le
    (A₁ A₂ A₃ B₁ B₂ B₃ : E →L[ℝ] E)
    (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (hA₁ : ‖A₁‖ ≤ a₁) (hA₂ : ‖A₂‖ ≤ a₂) (hA₃ : ‖A₃‖ ≤ a₃)
    (hB₁ : ‖B₁‖ ≤ b₁) (hB₂ : ‖B₂‖ ≤ b₂) (hB₃ : ‖B₃‖ ≤ b₃) :
    ‖A₁.comp B₁ + A₂.comp B₂ + A₃.comp B₃‖ ≤
      a₁ * b₁ + a₂ * b₂ + a₃ * b₃ := by
  calc
    ‖A₁.comp B₁ + A₂.comp B₂ + A₃.comp B₃‖
        ≤ ‖A₁.comp B₁ + A₂.comp B₂‖ + ‖A₃.comp B₃‖ := norm_add_le _ _
    _ ≤ (‖A₁.comp B₁‖ + ‖A₂.comp B₂‖) + ‖A₃.comp B₃‖ :=
      -- Preserve the right summand explicitly, without a one-sided lemma convention.
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ a₁ * b₁ + a₂ * b₂ + a₃ * b₃ :=
      add_le_add
        (add_le_add (norm_comp_le_of_caps A₁ B₁ a₁ b₁ hA₁ hB₁)
          (norm_comp_le_of_caps A₂ B₂ a₂ b₂ hA₂ hB₂))
        (norm_comp_le_of_caps A₃ B₃ a₃ b₃ hA₃ hB₃)

end GenericComposition

section ScalarCertificate

/-- Exact ratio of the conditional norm majorant to the frozen return cap.
This is scalar arithmetic only, not a return-operator premise. -/
theorem first_high_return_scalar_ratio :
    (lambda * (L 13 11 + L 13 12) * ρ ^ 3 + ρ ^ 8) /
        (lambda ^ 2 * J 13 13) =
      (78566776167802774186746199593 : ℝ) /
        157044573087890643353600000000 := by
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L, AESRound.Certificate.J]

/-- The frozen conditional majorant fits the return cap with strict slack. -/
theorem first_high_return_scalar_lt :
    lambda * (L 13 11 + L 13 12) * ρ ^ 3 + ρ ^ 8 <
      lambda ^ 2 * J 13 13 := by
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L, AESRound.Certificate.J]

end ScalarCertificate

section ActualSystem

/-- The concrete source-degree partition agrees with the generic three-high
index ordering. Only the finite type labels are evaluated here. -/
theorem actual_low_partition (k : Fin 14) : isLow k = decide (k.val ≤ 10) := by
  fin_cases k <;> decide

/-- Exact actual-system return identity; no norm cap is assumed. -/
theorem system_ret_eq_three_steps (i j : Fin 14) :
    system.ret i j =
      (system.step i 11).comp (system.step 11 j) +
      (system.step i 12).comp (system.step 12 j) +
      (system.step i 13).comp (system.step 13 j) := by
  change decomposition.ret isLow i j =
    (decomposition.step i 11).comp (decomposition.step 11 j) +
    (decomposition.step i 12).comp (decomposition.step 12 j) +
    (decomposition.step i 13).comp (decomposition.step 13 j)
  exact ret_eq_three_steps decomposition isLow actual_low_partition i j

/-- Accepted degree damping for the source-13 leg with target index 11. -/
theorem system_step_eleven_thirteen_norm : ‖system.step 11 13‖ ≤ ρ ^ 3 := by
  rw [step_eq_physical]
  have h := DegreeResidualStep.physical_degree_norm (11 : Fin 14) 13 (by decide)
  simpa [RefinedStepZeros.blockType] using h

/-- Accepted degree damping for the source-13 leg with target index 12. -/
theorem system_step_twelve_thirteen_norm : ‖system.step 12 13‖ ≤ ρ ^ 3 := by
  rw [step_eq_physical]
  have h := DegreeResidualStep.physical_degree_norm (12 : Fin 14) 13 (by decide)
  simpa [RefinedStepZeros.blockType] using h

/-- Accepted four-residual norm bound for both occurrences of `(13,13)`. -/
theorem system_step_thirteen_thirteen_norm : ‖system.step 13 13‖ ≤ ρ ^ 4 := by
  rw [step_eq_physical]
  exact FourResidualStep.physical_thirteen_thirteen_norm

-- Required missing premises: preserve these as two explicit hypotheses until
-- actual graph/Fourier support estimates establish the corresponding physical
-- step caps. Scalar slack must not be read as evidence for either premise.

/-- Conditional analytic majorant, before the frozen scalar comparison. -/
theorem system_first_high_return_bound
    (h₁₁ : ‖system.step 13 11‖ ≤ lambda * L 13 11)
    (h₁₂ : ‖system.step 13 12‖ ≤ lambda * L 13 12) :
    ‖system.ret 13 13‖ ≤
      lambda * (L 13 11 + L 13 12) * ρ ^ 3 + ρ ^ 8 := by
  have h := norm_three_compositions_le
    (system.step 13 11) (system.step 13 12) (system.step 13 13)
    (system.step 11 13) (system.step 12 13) (system.step 13 13)
    (lambda * L 13 11) (lambda * L 13 12) (ρ ^ 4) (ρ ^ 3) (ρ ^ 3) (ρ ^ 4)
    h₁₁ h₁₂ system_step_thirteen_thirteen_norm
    system_step_eleven_thirteen_norm system_step_twelve_thirteen_norm
    system_step_thirteen_thirteen_norm
  rw [← system_ret_eq_three_steps 13 13] at h
  calc
    ‖system.ret 13 13‖ ≤
        (lambda * L 13 11) * ρ ^ 3 + (lambda * L 13 12) * ρ ^ 3 +
          ρ ^ 4 * ρ ^ 4 := h
    _ = lambda * (L 13 11 + L 13 12) * ρ ^ 3 + ρ ^ 8 := by ring

/-- Conditional frozen return cap. Both unproved concrete step caps remain
explicit; this theorem alone is not an unconditional physical return result. -/
theorem system_first_high_return_cap
    (h₁₁ : ‖system.step 13 11‖ ≤ lambda * L 13 11)
    (h₁₂ : ‖system.step 13 12‖ ≤ lambda * L 13 12) :
    ‖system.ret 13 13‖ ≤ lambda ^ 2 * J 13 13 :=
  (system_first_high_return_bound h₁₁ h₁₂).trans (le_of_lt first_high_return_scalar_lt)

/-- Same conditional interface in physical-kernel units, for eventual proofs
of the two missing concrete step estimates. -/
theorem system_first_high_return_cap_of_physical
    (h₁₁ : ‖kernelOperator (RefinedStepZeros.physicalBlock 13 11)‖ ≤ lambda * L 13 11)
    (h₁₂ : ‖kernelOperator (RefinedStepZeros.physicalBlock 13 12)‖ ≤ lambda * L 13 12) :
    ‖system.ret 13 13‖ ≤ lambda ^ 2 * J 13 13 := by
  apply system_first_high_return_cap
  · rw [step_eq_physical]
    exact h₁₁
  · rw [step_eq_physical]
    exact h₁₂

end ActualSystem
end AESConcrete.FirstHighReturn
