import AES8.Math.PaperRealComplexEnergy
import AES8.Reductions.Return.PaperGraphResponseMatrix
import AES8.Estimates.Word.PaperWordMixedGram

/-!
# Arbitrary-input whole-graph return for reduced WORD codes

This estimates the same literal composition as the incidence route.  The
outside variant and every middle map are on the left matrix; the right
matrix has only raw graph incidence.  MDS supplies both information sets
and the right incidence fibers.  Physical graph identification is separate.
Constructive proof checking only; no attacks, searches or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperWholeGraphReturn
open AESMixing AESConcrete
open PaperMDSGram PaperGraphResponseMatrix PaperWordMixedGram
open AESConcrete.WordFourierVariants

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

theorem variant_mixed (adjoint e : Bool) : variant adjoint e = mixed adjoint e e := by
  cases e <;> simp only [variant, mixed, Bool.false_eq_true, if_false, if_true,
    WordFourierCore.wordConjugate, fourierConjugate, WordFourierCore.wordFourier]

theorem mds_card_low {K V : Type*} [Fintype K] [DecidableEq K]
    [AddCommGroup V] [Fintype V] [DecidableEq V]
    (C : AddSubgroup (K → V)) (s : ℕ) (hfit : 2 * s ≤ Fintype.card K)
    (hMDS : IsMDS C s) : Fintype.card C = Fintype.card V ^ s := by
  let idx := coordinateSplit (K := K) s hfit
  have he := (split_restrictions_bijective C s hMDS idx).1
  let e := Equiv.ofBijective (fun c : C => fun i : Fin s => c.val (idx (Sum.inl i))) he
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]

def leftWordMatrix {i m : ℕ} (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (cL : ℝ) (eL eR : Bool) :
    (Fin i → AES.Word) → (Fin m → AES.Word) → ℝ :=
  leftMatrix CL cL (variant false eL) (mixed false eL eR)

theorem leftWordMatrix_hilbertSchmidt {i m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word)) (s : ℕ)
    (hCL : IsMDS CL s) (hfit : 2 * s ≤ i + m)
    (cL : ℝ) (eL eR : Bool) :
    (∑ y : Fin i → AES.Word, ∑ x : Fin m → AES.Word,
      leftWordMatrix CL cL eL eR y x ^ 2) ≤
      (cL ^ 2 * (4294967296 : ℝ) ^ s) *
        (tau ^ 2 / 4294967296) ^ s * delta ^ (i + m - 2 * s) := by
  let T := vectorizedLocal (I := Fin i) (M := Fin m)
    (variant false eL) (mixed false eL eR)
  have hmoment (p : Fin i ⊕ Fin m) :
      (∑ xz : AES.Word × AES.Word, gram (T p) xz.1 xz.2 ^ 2) ≤ tau ^ 2 := by
    cases p with
    | inl p =>
      change (∑ xz : AES.Word × AES.Word, gram (variant false eL) xz.1 xz.2 ^ 2) ≤ _
      rw [variant_mixed]
      exact (mixed_moment_lt false eL eL).le
    | inr p => exact mixed_transpose_moment_le false eL eR
  have hdiag (p : Fin i ⊕ Fin m) (a : AES.Word) : gram (T p) a a ≤ delta := by
    cases p with
    | inl p =>
      change gram (variant false eL) a a ≤ _
      rw [variant_mixed]
      exact mixed_gram_diagonal_le false eL eL a
    | inr p => exact mixed_transpose_diagonal_le false eL eR a
  have hf : 2 * s ≤ Fintype.card (Fin i ⊕ Fin m) := by simpa using hfit
  have hb := mds_mixed_energy_low T CL s hf hCL (tau ^ 2) delta
    (sq_nonneg tau) delta_nonneg hmoment hdiag
  rw [show leftWordMatrix CL cL eL eR =
      leftMatrix CL cL (variant false eL) (mixed false eL eR) from rfl,
    leftMatrix_energy_eq]
  have hcard : (Fintype.card CL : ℝ) = (4294967296 : ℝ) ^ s := by
    rw [mds_card_low CL s hf hCL, Nat.cast_pow, AESConcrete.WordFourierCore.word_card]
    norm_num
  rw [hcard]
  have hb' : (∑ z, action (coordinateKernel T) (unitSubgroupIndicator CL) z ^ 2) ≤
      (tau ^ 2 / 4294967296) ^ s * delta ^ (i + m - 2 * s) := by
    simpa only [Fintype.card_sum, Fintype.card_fin,
      AESConcrete.WordFourierCore.word_card, Nat.cast_ofNat] using hb
  exact (mul_le_mul_of_nonneg_left hb' (by positivity)).trans_eq (by ring)

/-- The composition contains the middle word maps exactly once. -/
def rawReturn {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (cL cR : ℝ) (eL eR : Bool) :
    (Fin i → AES.Word) → (Fin j → AES.Word) → ℝ :=
  kernelCompose (leftWordMatrix CL cL eL eR)
    (fun x y => rawGraphMatrix CR cR y x)

/-- Product-form energy of the same raw return, for arbitrary signed input.
Every factor is derived, rather than passed as an operator-cap premise. -/
theorem rawReturn_energy {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (s t : ℕ) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (hfit : 2 * s ≤ i + m) (htm : t ≤ m)
    (cL cR : ℝ) (eL eR : Bool) (f : (Fin j → AES.Word) → ℝ) :
    (∑ y, action (rawReturn CL CR cL cR eL eR) f y ^ 2) ≤
      ((cL ^ 2 * (4294967296 : ℝ) ^ s) *
        (tau ^ 2 / 4294967296) ^ s * delta ^ (i + m - 2 * s)) *
      (cR ^ 2 * (4294967296 : ℝ) ^ (t - min t j)) * ∑ x, f x ^ 2 := by
  have hdelta := delta_nonneg
  let g := action (fun x y => rawGraphMatrix CR cR y x) f
  have hleft := energy_le_hilbertSchmidt (leftWordMatrix CL cL eL eR) g
  have hhs := leftWordMatrix_hilbertSchmidt CL s hCL hfit cL eL eR
  have hright := transpose_rawGraphMatrix_energy CR t hCR
    (show t ≤ Fintype.card (Fin m) by simpa) cR f
  have hright' : (∑ x, g x ^ 2) ≤
      (cR ^ 2 * (4294967296 : ℝ) ^ (t - min t j)) * ∑ x, f x ^ 2 := by
    simpa only [g, Fintype.card_fin, AESConcrete.WordFourierCore.word_card,
      Nat.cast_ofNat] using hright
  have hleft' := hleft.trans (mul_le_mul_of_nonneg_right hhs
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hfinal := hleft'.trans (mul_le_mul_of_nonneg_left hright' (by positivity))
  simpa only [rawReturn, kernelCompose_action, g, mul_assoc] using hfinal

/-- Real and imaginary parts preserve the original signed cancellations. -/
theorem complex_energy_of_real {A B : Type*} [Fintype A] [Fintype B]
    (T : A → B → ℝ) (b : ℝ)
    (hreal : ∀ f : B → ℝ, (∑ y, action T f y ^ 2) ≤ b * ∑ x, f x ^ 2)
    (f : B → ℂ) :
    (∑ y, ‖PaperKernelBounds.kernelAction (fun y x => (T y x : ℂ)) f y‖ ^ 2) ≤
      b * ∑ x, ‖f x‖ ^ 2 :=
  PaperRealComplexEnergy.complex_energy_of_real T b hreal f

theorem rawReturn_complex_energy {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (s t : ℕ) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (hfit : 2 * s ≤ i + m) (htm : t ≤ m)
    (cL cR : ℝ) (eL eR : Bool) (f : (Fin j → AES.Word) → ℂ) :
    (∑ y, ‖PaperKernelBounds.kernelAction
      (fun y x => (rawReturn CL CR cL cR eL eR y x : ℂ)) f y‖ ^ 2) ≤
      ((cL ^ 2 * (4294967296 : ℝ) ^ s) *
        (tau ^ 2 / 4294967296) ^ s * delta ^ (i + m - 2 * s)) *
      (cR ^ 2 * (4294967296 : ℝ) ^ (t - min t j)) * ∑ x, ‖f x‖ ^ 2 := by
  apply complex_energy_of_real
  intro f
  simpa only [mul_assoc] using rawReturn_energy CL CR s t hCL hCR hfit htm cL cR eL eR f

theorem rpow_half_square (x a : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (a / 2) ^ 2 = Real.rpow x a := by
  change (x ^ (a / 2 : ℝ)) ^ (2 : ℕ) = x ^ a
  rw [← Real.rpow_mul_natCast hx (a / 2) 2]
  congr 1
  norm_num

theorem graphCoefficient_square (i m d : ℕ) :
    graphCoefficient i m d ^ 2 =
      Real.rpow (4294967296 : ℝ) ((i : ℝ) + (m : ℝ) - 4 - (d : ℝ)) :=
  rpow_half_square _ _ (by norm_num)

/-- Exact normalization to the displayed whole-graph candidate. -/
theorem whole_coefficient_identity (i j m s t : ℕ) (hfit : 2 * s ≤ i + m) :
    ((graphCoefficient i m s ^ 2 * (4294967296 : ℝ) ^ s) *
      (tau ^ 2 / 4294967296) ^ s * delta ^ (i + m - 2 * s)) *
      (graphCoefficient j m t ^ 2 * (4294967296 : ℝ) ^ (t - min t j)) =
    (Real.rpow (4294967296 : ℝ)
        (((i : ℝ) + (j : ℝ) + 2 * (m : ℝ) - 8 - (s : ℝ) - (min j t : ℕ)) / 2) *
      tau ^ s * Real.rpow delta (((i : ℝ) + (m : ℝ) - 2 * (s : ℝ)) / 2)) ^ 2 := by
  have hq : (0 : ℝ) < 4294967296 := by norm_num
  have hc : (4294967296 : ℝ) ^ s * (tau ^ 2 / 4294967296) ^ s = (tau ^ s) ^ 2 := by
    rw [div_pow]
    have hqn : (4294967296 : ℝ) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hd : (i : ℝ) + (m : ℝ) - 2 * (s : ℝ) = ((i + m - 2 * s : ℕ) : ℝ) := by
    rw [Nat.cast_sub hfit, Nat.cast_add, Nat.cast_mul]
    norm_num
  have hqcombine :
      Real.rpow (4294967296 : ℝ) ((i : ℝ) + (m : ℝ) - 4 - (s : ℝ)) *
        Real.rpow (4294967296 : ℝ) ((j : ℝ) + (m : ℝ) - 4 - (t : ℝ)) *
        (4294967296 : ℝ) ^ (t - min t j) =
      Real.rpow (4294967296 : ℝ)
        ((i : ℝ) + (j : ℝ) + 2 * (m : ℝ) - 8 - (s : ℝ) - (min j t : ℕ)) := by
    change (4294967296 : ℝ) ^ ((i : ℝ) + (m : ℝ) - 4 - (s : ℝ)) *
        (4294967296 : ℝ) ^ ((j : ℝ) + (m : ℝ) - 4 - (t : ℝ)) *
        (4294967296 : ℝ) ^ (t - min t j) =
      (4294967296 : ℝ) ^
        ((i : ℝ) + (j : ℝ) + 2 * (m : ℝ) - 8 - (s : ℝ) - (min j t : ℕ))
    rw [← Real.rpow_natCast (4294967296 : ℝ) (t - min t j)]
    rw [← Real.rpow_add hq ((i : ℝ) + (m : ℝ) - 4 - (s : ℝ))
      ((j : ℝ) + (m : ℝ) - 4 - (t : ℝ))]
    rw [← Real.rpow_add hq]
    congr 1
    rw [Nat.cast_sub (Nat.min_le_left _ _), min_comm t j]
    ring
  rw [mul_pow, mul_pow, rpow_half_square _ _ hq.le,
    rpow_half_square _ _ delta_nonneg, hd,
    graphCoefficient_square, graphCoefficient_square]
  calc
    _ = (Real.rpow (4294967296 : ℝ) ((i : ℝ) + (m : ℝ) - 4 - (s : ℝ)) *
        Real.rpow (4294967296 : ℝ) ((j : ℝ) + (m : ℝ) - 4 - (t : ℝ)) *
        (4294967296 : ℝ) ^ (t - min t j)) *
        ((4294967296 : ℝ) ^ s * (tau ^ 2 / 4294967296) ^ s) *
        delta ^ (i + m - 2 * s) := by ring
    _ = _ := by
      rw [hc, hqcombine]
      congr 1
      exact (Real.rpow_natCast delta (i + m - 2 * s)).symm

/-- The paper's whole-graph coefficient bounds the literal reduced-code
return on arbitrary complex input, including all four independent dual choices. -/
theorem whole_graph_aes_energy {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (s t : ℕ) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (hfit : 2 * s ≤ i + m) (htm : t ≤ m)
    (eL eR : Bool) (f : (Fin j → AES.Word) → ℂ) :
    (∑ y, ‖PaperKernelBounds.kernelAction
      (fun y x => (rawReturn CL CR (graphCoefficient i m s)
        (graphCoefficient j m t) eL eR y x : ℂ)) f y‖ ^ 2) ≤
    (Real.rpow (4294967296 : ℝ)
        (((i : ℝ) + (j : ℝ) + 2 * (m : ℝ) - 8 - (s : ℝ) - (min j t : ℕ)) / 2) *
      tau ^ s * Real.rpow delta (((i : ℝ) + (m : ℝ) - 2 * (s : ℝ)) / 2)) ^ 2 *
        ∑ x, ‖f x‖ ^ 2 := by
  have h := rawReturn_complex_energy CL CR s t hCL hCR hfit htm
    (graphCoefficient i m s) (graphCoefficient j m t) eL eR f
  rw [whole_coefficient_identity i j m s t hfit] at h
  exact h

end AES8.PaperWholeGraphReturn
