import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Reductions.Return.PaperAESIncidence
import AES8.Math.PaperThinLinesOperator

/-!
# Literal return through the normalized middle overlap

The middle kernel lives on the two actual code types. Its normalized compression
lives on their attained outside images. The factorization below identifies the
literal raw return with that operator, an outside encoder, and outside restriction.
The algebra needs only positive normalization parameters; MDS supplies their
intended fiber-cardinality interpretation and the encoder estimate separately.
Constructive proof validation only; no attacks, searches, or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESNormalizedReturn
open AESMixing PaperMDSGram PaperGraphResponseMatrix PaperKernelBounds
open PaperAESIncidence PaperFiberKernel PaperWholeGraphReturn

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable

variable {I J M V : Type*} [Fintype I] [Fintype J] [Fintype M] [Fintype V]
  [DecidableEq I] [DecidableEq J] [DecidableEq M]
  [AddCommGroup V] [DecidableEq V]

/-- Product middle map restricted to literal left and right codewords. -/
def middleKernel (CL : AddSubgroup ((I ⊕ M) → V))
    (CR : AddSubgroup ((J ⊕ M) → V)) (W : V → V → ℝ)
    (c : CL) (d : CR) : ℝ :=
  ∏ p : M, W (middle CL c p) (middle CR d p)

/-- Normalized fiber sum on the attained outside images. -/
def normalizedKernel (CL : AddSubgroup ((I ⊕ M) → V))
    (CR : AddSubgroup ((J ⊕ M) → V)) (a b : ℕ) (W : V → V → ℝ) :
    outsideSet CL → outsideSet CR → ℝ :=
  compressedKernel (outside CL) (outside CR) a b (middleKernel CL CR W)

/-- Actual Euclidean operator, rather than an assumed operator identification. -/
def normalizedOverlap (CL : AddSubgroup ((I ⊕ M) → V))
    (CR : AddSubgroup ((J ⊕ M) → V)) (a b : ℕ) (W : V → V → ℝ) :
    EuclideanSpace ℝ (outsideSet CR) →L[ℝ] EuclideanSpace ℝ (outsideSet CL) :=
  kernelOperator (normalizedKernel CL CR a b W)

/-- Restricting the ambient middle tensor really gives the code kernel. -/
theorem middle_compression (CL : AddSubgroup ((I ⊕ M) → V))
    (CR : AddSubgroup ((J ⊕ M) → V)) (W : V → V → ℝ) :
    (middleInclusion CL).adjoint.comp
      ((kernelOperator (coordinateKernel (fun _ : M => W))).comp
        (middleInclusion CR)) = kernelOperator (middleKernel CL CR W) := by
  exact PaperThinLines.coordinateInclusion_compression (middle CL) (middle CR)
    (coordinateKernel (fun _ : M => W))

/-- The normalized overlap is the actual five-factor middle compression. -/
theorem normalizedOverlap_eq (CL : AddSubgroup ((I ⊕ M) → V))
    (CR : AddSubgroup ((J ⊕ M) → V)) (a b : ℕ) (W : V → V → ℝ) :
    normalizedOverlap CL CR a b W =
      (fiberLift (outside CL) a).adjoint.comp
        (((middleInclusion CL).adjoint.comp
          ((kernelOperator (coordinateKernel (fun _ : M => W))).comp
            (middleInclusion CR))).comp (fiberLift (outside CR) b)) := by
  rw [middle_compression]
  exact compression_eq_adjoint_comp (outside CL) (outside CR) a b (middleKernel CL CR W)

/-- Right graph incidence is the transpose of the counting incidence identity. -/
theorem right_factorization (C : AddSubgroup ((J ⊕ M) → V))
    (c : ℝ) (b : ℕ) (hb : 0 < b) :
    kernelOperator (fun x y => rawGraphMatrix C c y x) =
      (c * Real.sqrt (b : ℝ)) • (middleInclusion C).comp
        ((fiberLift (outside C) b).comp (outsideInclusion C).adjoint) := by
  have htranspose : kernelOperator (fun x y => rawGraphMatrix C c y x) =
      (kernelOperator (rawGraphMatrix C c)).adjoint := by
    rw [kernelOperator_adjoint]
    congr 1
  rw [htranspose, coefficient_operator, raw_incidence_identity C b hb]
  simp only [map_smulₛₗ, starRingEnd_apply, star_trivial,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_smul]
  rfl

/-- Outside restriction is a contraction on arbitrary vectors. -/
theorem outsideRestriction_norm (C : AddSubgroup ((I ⊕ M) → V)) :
    ‖(outsideInclusion (𝕜 := ℝ) C).adjoint‖ ≤ 1 := by
  let T : outsideSet C → (I → V) → ℝ := fun c y => if c.val = y then 1 else 0
  have hcol (y : I → V) : (∑ c, T c y) ≤ 1 := by
    change (∑ c : outsideSet C, if c.val = y then (1 : ℝ) else 0) ≤ 1
    rw [AESMixing.real_indicator_sum_card]
    haveI : Subsingleton {c : outsideSet C // c.val = y} := ⟨fun a b =>
      Subtype.ext (Subtype.ext (a.property.trans b.property.symm))⟩
    have hc := Fintype.card_le_of_injective
      (fun _ : {c : outsideSet C // c.val = y} => ())
      (fun _ _ _ => Subsingleton.elim _ _)
    have hc' : Fintype.card {c : outsideSet C // c.val = y} ≤ 1 := by simpa using hc
    exact_mod_cast hc'
  have hn := schur_operator_norm_sq T T 1 1 (by norm_num) (by norm_num)
    (fun c y => by dsimp [T]; split_ifs <;> norm_num)
    (fun c y => by dsimp [T]; split_ifs <;> simp)
    (fun c => by simp [T]) hcol
  have he : (outsideInclusion (𝕜 := ℝ) C).adjoint = kernelOperator T := by
    rw [outsideInclusion, kernelOperator_adjoint]
    congr 1
  rw [he]
  norm_num at hn
  nlinarith [norm_nonneg (kernelOperator T)]

/-- Generic raw-return factorization; no MDS or norm premise is used. -/
theorem return_factorization (CL : AddSubgroup ((I ⊕ M) → V))
    (CR : AddSubgroup ((J ⊕ M) → V))
    (cL cR : ℝ) (O W : V → V → ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    kernelOperator (kernelCompose (leftMatrix CL cL O W)
      (fun x y => rawGraphMatrix CR cR y x)) =
      ((cL * Real.sqrt (a : ℝ)) * (cR * Real.sqrt (b : ℝ))) •
        (PaperEncoding.encoder (outsideSet CL) (fun _ => O)).comp
          ((normalizedOverlap CL CR a b W).comp (outsideInclusion CR).adjoint) := by
  change kernelOperator (kernelCompose
    (kernelCompose (outsideMappedMatrix CL cL O) (coordinateKernel (fun _ : M => W)))
    (fun x y => rawGraphMatrix CR cR y x)) = _
  rw [kernelOperator_comp, kernelOperator_comp, outsideMapped_factorization CL cL O a ha,
    right_factorization CR cR b hb, normalizedOverlap_eq]
  ext f y
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul, smul_smul]
  rw [mul_comm (cR * Real.sqrt (b : ℝ)) (cL * Real.sqrt (a : ℝ))]

/-- A cap on the normalized middle overlap transfers through the literal return. -/
theorem return_norm (CL : AddSubgroup ((I ⊕ M) → V))
    (CR : AddSubgroup ((J ⊕ M) → V))
    (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (O W : V → V → ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (encoderCap overlapCap : ℝ)
    (henc : ‖PaperEncoding.encoder (outsideSet CL) (fun _ => O)‖ ≤ encoderCap)
    (hnorm : ‖normalizedOverlap CL CR a b W‖ ≤ overlapCap) :
    ‖kernelOperator (kernelCompose (leftMatrix CL cL O W)
      (fun x y => rawGraphMatrix CR cR y x))‖ ≤
      ((cL * Real.sqrt (a : ℝ)) * (cR * Real.sqrt (b : ℝ))) *
        encoderCap * overlapCap := by
  have hec : 0 ≤ encoderCap := (norm_nonneg _).trans henc
  have hoc : 0 ≤ overlapCap := (norm_nonneg _).trans hnorm
  have hcoef : 0 ≤ (cL * Real.sqrt (a : ℝ)) * (cR * Real.sqrt (b : ℝ)) :=
    mul_nonneg (mul_nonneg hcL (Real.sqrt_nonneg _))
      (mul_nonneg hcR (Real.sqrt_nonneg _))
  rw [return_factorization CL CR cL cR O W a b ha hb, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hcoef,
    mul_assoc ((cL * Real.sqrt (a : ℝ)) * (cR * Real.sqrt (b : ℝ))) encoderCap overlapCap]
  apply mul_le_mul_of_nonneg_left _ hcoef
  calc
    _ ≤ ‖PaperEncoding.encoder (outsideSet CL) (fun _ => O)‖ *
        ‖(normalizedOverlap CL CR a b W).comp (outsideInclusion CR).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ encoderCap * (overlapCap * 1) := by
      apply mul_le_mul henc _ (norm_nonneg _) hec
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hnorm (outsideRestriction_norm CR) (norm_nonneg _) hoc)
    _ = encoderCap * overlapCap := by ring

/-- AES specialization with the exact MDS fiber multiplicities. -/
def aesOverlap {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word)) (s t : ℕ) (eL eR : Bool) :=
  normalizedOverlap CL CR
    (Fintype.card AES.Word ^ (s - min s i))
    (Fintype.card AES.Word ^ (t - min t j))
    (PaperWordMixedGram.mixed false eL eR)

theorem aes_rawReturn_factorization {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (cL cR : ℝ) (eL eR : Bool) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    kernelOperator (rawReturn CL CR cL cR eL eR) =
      ((cL * Real.sqrt (a : ℝ)) * (cR * Real.sqrt (b : ℝ))) •
        (PaperEncoding.encoder (outsideSet CL)
          (fun _ => AESConcrete.WordFourierVariants.variant false eL)).comp
          ((normalizedOverlap CL CR a b
            (PaperWordMixedGram.mixed false eL eR)).comp
              (outsideInclusion CR).adjoint) :=
  return_factorization CL CR cL cR
    (AESConcrete.WordFourierVariants.variant false eL)
    (PaperWordMixedGram.mixed false eL eR) a b ha hb

/-- The outside encoder estimate uses MDS information coordinates only. -/
theorem aes_encoder_norm {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word)) (s : ℕ)
    (hC : IsMDS C s) (hmid : s ≤ m) (adjoint fourier : Bool) :
    ‖PaperEncoding.encoder (outsideSet C)
      (fun _ => AESConcrete.WordFourierVariants.variant adjoint fourier)‖ ≤
      nu ^ min s i * Real.rpow PaperWordMixedGram.delta
        (((i : ℝ) - (min s i : ℕ)) / 2) := by
  have hnorm : ‖kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier)‖ ≤ nu := by
    have h := (SharpWordNorm.variant_operator_norm_lt adjoint fourier).le
    have hs : Real.sqrt ((2 : ℝ) ^ 32) = 65536 := by
      rw [show (2 : ℝ) ^ 32 = 65536 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hop : kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier) =
        AESConcrete.kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier) := by
      ext f y
      rfl
    rw [hop]
    simpa only [hs, nu] using h
  have hcol (x : AES.Word) :
      ‖kernelOperator (AESConcrete.WordFourierVariants.variant adjoint fourier)
        (PaperEncoding.basisVector x)‖ ^ 2 ≤ PaperWordMixedGram.delta := by
    rw [PaperEncoding.basis_response_energy]
    exact (PaperAESSource.residualVariant_column_energy_lt_current adjoint fourier x).le.trans
      (by norm_num [PaperWordMixedGram.delta])
  obtain ⟨S, hS, hinfo⟩ := outside_information C s hC (by simpa using hmid)
  have he := PaperEncoding.paper_encoding_norm (outsideSet C) S hinfo
    (fun _ => AESConcrete.WordFourierVariants.variant adjoint fourier)
    nu PaperWordMixedGram.delta nu_nonneg PaperWordMixedGram.delta_nonneg
    (fun _ => hnorm) (fun _ => hcol)
  simpa only [hS, Fintype.card_fin, Real.rpow_eq_pow] using he

/-- Literal AES return bound with an explicit normalized-overlap cap.
Sharp overlap resources and physical coordinate correspondence are separate. -/
theorem aes_rawReturn_norm {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (s t : ℕ) (hCL : IsMDS CL s) (_hCR : IsMDS CR t)
    (hs : s ≤ m) (_ht : t ≤ m) (eL eR : Bool) (overlapCap : ℝ)
    (hnorm : ‖aesOverlap CL CR s t eL eR‖ ≤ overlapCap) :
    ‖kernelOperator (rawReturn CL CR (graphCoefficient i m s)
      (graphCoefficient j m t) eL eR)‖ ≤
      leftFactor i m s * rightFactor j m t * overlapCap := by
  have h := return_norm CL CR (graphCoefficient i m s) (graphCoefficient j m t)
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    (AESConcrete.WordFourierVariants.variant false eL)
    (PaperWordMixedGram.mixed false eL eR)
    (Fintype.card AES.Word ^ (s - min s i))
    (Fintype.card AES.Word ^ (t - min t j))
    (pow_pos Fintype.card_pos _) (pow_pos Fintype.card_pos _)
    _ overlapCap (aes_encoder_norm CL s hCL hs false eL) hnorm
  simp only [Nat.cast_pow, AESConcrete.WordFourierCore.word_card, Nat.cast_ofNat] at h
  rw [incidence_coefficient, incidence_coefficient] at h
  simpa only [rawReturn, leftWordMatrix, leftFactor, rightFactor, mul_assoc,
    mul_left_comm, mul_comm] using h

end AES8.PaperAESNormalizedReturn
