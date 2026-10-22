/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ProjectedGraph
import AES8.Reductions.Fibers.MarkedZeroOverlap
import AES8.Math.InformationEncoding
import AES8.Estimates.Transfer.SharpDegreeStep
import AES8.Estimates.Source.OneSourceEventMoment

/-!
# Exact middle transports for the three cross-frame branches

The true endpoint domains have full triple information labels. Restricting
the left domain proves the 01 bound without replacing its attained image by
all triples. The 10 encoder retains the complete two-coordinate input label.
Inputs are arbitrary signed joint functions. This module supplies middle
estimates only; endpoint frame scalars, outside encoders, and the shared
inverse metric remain in their separate exact interfaces.

  No attacks, active-source edits, or cell closure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ReturnCrossMiddle
open AESMixing AESMixing.AES
open AES8.MDSFiberCollision AES8.MarkedZeroFiber
open AES8.MarkedZeroOverlap (inputObservedEquiv outputObservedEquiv)
open AES8.ZeroOutsideProjection
open AES8.ProjectedGraph
open AESConcrete.WordCrossZero

private abbrev L := wordMixAddEquiv.toAddMonoidHom

-- These decidable facts enumerate only four position names and sixteen masks.
private theorem single_bit : ∀ c i : Fin 4,
    maskBit (AES8.MarkedZeroOverlap.singleMask c) i = true ↔ i = c := by decide
private theorem single_size : ∀ c : Fin 4, maskSize (AES8.MarkedZeroOverlap.singleMask c) = 1 := by decide
private theorem empty_bit : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
private theorem empty_size : maskSize (0 : Fin 16) = 0 := by decide
private theorem outside_size : ∀ c : Fin 4, maskSize (outsideMask c) = 3 := by decide
private theorem outside_card : ∀ c : Fin 4, Fintype.card (OutsideCoordinates c) = 3 := by
  intro c
  rw [maskCoordinates_card, outside_size]
private theorem disjoint_empty : ∀ m : Fin 16, MaskDisjoint m 0 := by decide
private theorem empty_disjoint : ∀ m : Fin 16, MaskDisjoint 0 m := by decide

private theorem left_true_iff (r c : Fin 4) (v : WordState) :
    graphPrescribed L (AES8.MarkedZeroOverlap.singleMask r) 0 (0 : WordState) 0 v ↔
      LeftConstraint r c true v := by
  constructor
  · intro h
    exact ⟨h.1 r ((single_bit r r).mpr rfl), Or.inl rfl⟩
  · intro h
    constructor
    · intro i hi
      have hir := (single_bit r i).mp hi
      subst i
      exact h.1
    · intro i hi
      rw [empty_bit] at hi
      contradiction

private theorem right_true_iff (c z : Fin 4) (x : WordState) :
    graphPrescribed L 0 (AES8.MarkedZeroOverlap.singleMask z) (0 : WordState) 0 x ↔
      RightConstraint c z true x := by
  constructor
  · intro h
    exact ⟨h.2 z ((single_bit z z).mpr rfl), Or.inl rfl⟩
  · intro h
    constructor
    · intro i hi
      rw [empty_bit] at hi
      contradiction
    · intro i hi
      have hiz := (single_bit z i).mp hi
      subst i
      exact h.1

def leftTrueGraph (r c : Fin 4) :
    LeftDomain r c true ≃ AffineGraph L (AES8.MarkedZeroOverlap.singleMask r) 0 (0 : WordState) 0 where
  toFun v := ⟨v.val, (left_true_iff r c v.val).mpr v.property⟩
  invFun v := ⟨v.val, (left_true_iff r c v.val).mp v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def rightTrueGraph (c z : Fin 4) :
    RightDomain c z true ≃ AffineGraph L 0 (AES8.MarkedZeroOverlap.singleMask z) (0 : WordState) 0 where
  toFun x := ⟨x.val, (right_true_iff c z x.val).mpr x.property⟩
  invFun x := ⟨x.val, (right_true_iff c z x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full input-middle triple on the left true domain. -/
def leftLabels (r c : Fin 4) : LeftDomain r c true ≃ (OutsideCoordinates c → AES.Word) :=
  (leftTrueGraph r c).trans
    ((informationEquiv L wordMixAddEquiv_zeroMDS (AES8.MarkedZeroOverlap.singleMask r) 0 0 (outsideMask c)
      0 0 (disjoint_empty _) (empty_disjoint _)
      (by rw [single_size, empty_size, outside_size])).trans
        (inputObservedEquiv (outsideMask c) AES.Word))

/-- Full forward-output-middle triple on the right true domain. -/
def rightLabels (c z : Fin 4) : RightDomain c z true ≃ (OutsideCoordinates c → AES.Word) :=
  (rightTrueGraph c z).trans
    ((informationEquiv L wordMixAddEquiv_zeroMDS 0 (AES8.MarkedZeroOverlap.singleMask z) (outsideMask c) 0
      0 0 (empty_disjoint _) (disjoint_empty _)
      (by rw [single_size, empty_size, outside_size])).trans
        (outputObservedEquiv (outsideMask c) AES.Word))

@[simp] theorem leftLabels_coordinate (r c : Fin 4) (v : LeftDomain r c true)
    (i : OutsideCoordinates c) : leftLabels r c v i = v.val i.val := rfl

@[simp] theorem rightLabels_coordinate (c z : Fin 4) (x : RightDomain c z true)
    (i : OutsideCoordinates c) : rightLabels c z x i = wordMixAddEquiv x.val i.val := rfl

def leftToTrue (r c : Fin 4) (v : LeftDomain r c false) : LeftDomain r c true :=
  ⟨v.val, v.property.1, Or.inl rfl⟩

private def leftFalseEquiv (r c : Fin 4) : LeftDomain r c false ≃
    {v : LeftDomain r c true // v.val c = 0} where
  toFun v := ⟨leftToTrue r c v, by
    rcases v.property.2 with h | h
    · cases h
    · exact h⟩
  invFun v := ⟨v.val.val, v.val.property.1, Or.inr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restriction to the actual constrained row domain is a counting contraction. -/
theorem left_restriction_energy (r c : Fin 4) (g : LeftDomain r c true → ℝ) :
    (∑ v : LeftDomain r c false, g (leftToTrue r c v) ^ 2) ≤
      ∑ v : LeftDomain r c true, g v ^ 2 := by
  rw [← (leftFalseEquiv r c).symm.sum_comp (fun v : LeftDomain r c false =>
    g (leftToTrue r c v) ^ 2)]
  change (∑ v : {v : LeftDomain r c true // v.val c = 0}, g v.val ^ 2) ≤ _
  have he : (∑ v : LeftDomain r c true, if v.val c = 0 then g v ^ 2 else 0) =
      ∑ v : {v : LeftDomain r c true // v.val c = 0}, g v.val ^ 2 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [← he]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : v.val c = 0
  · simp [hv]
  · simp [hv, sq_nonneg]

/-- Literal triple kernel on each exact frame domain; no frame scalar is absorbed. -/
def middleKernel (r c z : Fin 4) (s t : Bool)
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ)
    (v : LeftDomain r c s) (x : RightDomain c z t) : ℝ :=
  ∏ i : OutsideCoordinates c, K i (v.val i.val) (wordMixAddEquiv x.val i.val)

/-- Reindex only the right full triple; the left domain can remain constrained. -/
theorem true_right_action (r c z : Fin 4) (s : Bool)
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ)
    (f : RightDomain c z true → ℝ) (v : LeftDomain r c s) :
    action (middleKernel r c z s true K) f v =
      action (coordinateKernel K) (fun u => f ((rightLabels c z).symm u))
        (fun i => v.val i.val) := by
  unfold action middleKernel coordinateKernel
  rw [← (rightLabels c z).symm.sum_comp (fun x : RightDomain c z true =>
    (∏ i : OutsideCoordinates c, K i (v.val i.val) (wordMixAddEquiv x.val i.val)) * f x)]
  apply Finset.sum_congr rfl
  intro u _
  have hu : (fun i : OutsideCoordinates c =>
      wordMixAddEquiv ((rightLabels c z).symm u).val i.val) = u :=
    (rightLabels c z).apply_symm_apply u
  have hui (i : OutsideCoordinates c) :
      wordMixAddEquiv ((rightLabels c z).symm u).val i.val = u i := congrFun hu i
  simp_rw [hui]

/-- 11 middle energy: two exact full triple reindexings. -/
theorem eleven_energy (r c z : Fin 4)
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ) (nu : ℝ)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : RightDomain c z true → ℝ) :
    (∑ v : LeftDomain r c true, action (middleKernel r c z true true K) f v ^ 2) ≤
      nu ^ 6 * ∑ x : RightDomain c z true, f x ^ 2 := by
  rw [← (leftLabels r c).symm.sum_comp (fun v : LeftDomain r c true =>
    action (middleKernel r c z true true K) f v ^ 2)]
  simp_rw [true_right_action]
  have hu (u : OutsideCoordinates c → AES.Word) :
      (fun i : OutsideCoordinates c => ((leftLabels r c).symm u).val i.val) = u :=
    (leftLabels r c).apply_symm_apply u
  simp_rw [hu]
  have hb := AESConcrete.FiniteTensorEnergy.coordinate_energy K (fun _ => nu) hK
    (fun u => f ((rightLabels c z).symm u))
  have hp : (∏ _i : OutsideCoordinates c, nu) ^ 2 = nu ^ 6 := by
    simp only [Finset.prod_const, Finset.card_univ, outside_card]
    ring
  rw [hp, (rightLabels c z).symm.sum_comp (fun x => f x ^ 2)] at hb
  exact hb

/-- 01 middle energy: full tensor followed by literal constrained-row restriction. -/
theorem zero_one_energy (r c z : Fin 4)
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ) (nu : ℝ)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : RightDomain c z true → ℝ) :
    (∑ v : LeftDomain r c false, action (middleKernel r c z false true K) f v ^ 2) ≤
      nu ^ 6 * ∑ x : RightDomain c z true, f x ^ 2 := by
  have he (v : LeftDomain r c false) :
      action (middleKernel r c z false true K) f v =
      action (middleKernel r c z true true K) f (leftToTrue r c v) := rfl
  simp_rw [he]
  exact (left_restriction_energy r c
    (action (middleKernel r c z true true K) f)).trans (eleven_energy r c z K nu hK f)

theorem eleven_l2 (r c z : Fin 4)
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ) (nu : ℝ) (hnu : 0 ≤ nu)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : RightDomain c z true → ℝ) :
    l2 (action (middleKernel r c z true true K) f) ≤ nu ^ 3 * l2 f := by
  apply l2_le_of_energy _ f (nu ^ 3) (pow_nonneg hnu _)
  rw [show (nu ^ 3) ^ 2 = nu ^ 6 by ring]
  exact eleven_energy r c z K nu hK f

theorem zero_one_l2 (r c z : Fin 4)
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ) (nu : ℝ) (hnu : 0 ≤ nu)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : RightDomain c z true → ℝ) :
    l2 (action (middleKernel r c z false true K) f) ≤ nu ^ 3 * l2 f := by
  apply l2_le_of_energy _ f (nu ^ 3) (pow_nonneg hnu _)
  rw [show (nu ^ 3) ^ 2 = nu ^ 6 by ring]
  exact zero_one_energy r c z K nu hK f

/-- Actual residual factors; the literal endpoint scalars remain outside. -/
def actualKernel (r c z : Fin 4) (s t : Bool) :=
  middleKernel r c z s t (fun _ => residualMatrix wordSuperboxKernel 0)

theorem actual_eleven_energy (r c z : Fin 4) (f : RightDomain c z true → ℝ) :
    (∑ v : LeftDomain r c true, action (actualKernel r c z true true) f v ^ 2) ≤
      SharpWordNorm.rho ^ 6 * ∑ x : RightDomain c z true, f x ^ 2 :=
  eleven_energy r c z _ SharpWordNorm.rho
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g) f

theorem actual_zero_one_energy (r c z : Fin 4) (f : RightDomain c z true → ℝ) :
    (∑ v : LeftDomain r c false, action (actualKernel r c z false true) f v ^ 2) ≤
      SharpWordNorm.rho ^ 6 * ∑ x : RightDomain c z true, f x ^ 2 :=
  zero_one_energy r c z _ SharpWordNorm.rho
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g) f

/-- Connect the coordinate tensor to the exact projected-graph middle factor. -/
theorem actualKernel_eq_channelTail (r c z : Fin 4) (s t : Bool)
    (v : LeftDomain r c s) (x : RightDomain c z t) :
    actualKernel r c z s t v x =
      PhysicalZeroPattern.channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) := by
  unfold actualKernel middleKernel PhysicalZeroPattern.channelTail
  symm
  calc
    (∏ i : Fin 4, if i = c then (1 : ℝ) else
        residualMatrix wordSuperboxKernel 0 (v.val i) (wordMixAddEquiv x.val i)) =
        ∏ i : Fin 4, if maskBit (outsideMask c) i = true then
          residualMatrix wordSuperboxKernel 0 (v.val i) (wordMixAddEquiv x.val i) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = c <;> simp [outsideMask_bit_iff, hi]
    _ = ∏ i : OutsideCoordinates c,
        residualMatrix wordSuperboxKernel 0 (v.val i.val) (wordMixAddEquiv x.val i.val) := by
      rw [← Finset.prod_filter]
      exact Finset.prod_subtype _ (by simp) _

end AES8.ReturnCrossMiddle
