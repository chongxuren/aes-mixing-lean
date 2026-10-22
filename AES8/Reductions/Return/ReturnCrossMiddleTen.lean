/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ReturnCrossMiddle

/-!
# The literal 10 middle branch as a two-information-coordinate encoder

The column domain is the actual two-zero graph. Its two selected forward
output labels determine the whole graph point; the third output coordinate
is retained as a function of that complete pair. The row domain has the
full input-middle triple labels already proved in ReturnCrossMiddle.
No product-input or coordinate-independence premise is used.

  Frame endpoints and the shared inverse metric are not
absorbed in the middle estimate. No attacks or return-cell closure.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ReturnCrossMiddleTen
open AESMixing AESMixing.AES
open AES8.MDSFiberCollision AES8.MarkedZeroFiber AES8.MarkedZeroOverlap
open AES8.ZeroOutsideProjection AES8.ProjectedGraph AES8.ReturnCrossMiddle
open AESConcrete.WordCrossZero

private abbrev L := wordMixAddEquiv.toAddMonoidHom
private theorem single_bit : ∀ c i : Fin 4,
    maskBit (AES8.MarkedZeroOverlap.singleMask c) i = true ↔ i = c := by decide
private theorem single_size : ∀ c : Fin 4, maskSize (AES8.MarkedZeroOverlap.singleMask c) = 1 := by decide
private theorem empty_size : maskSize (0 : Fin 16) = 0 := by decide
private theorem disjoint_empty : ∀ m : Fin 16, MaskDisjoint m 0 := by decide

private theorem right_false_iff (c z : Fin 4) (x : WordState) :
    graphPrescribed L (AES8.MarkedZeroOverlap.singleMask c) (AES8.MarkedZeroOverlap.singleMask z) (0 : WordState) 0 x ↔
      RightConstraint c z false x := by
  constructor
  · intro h
    exact ⟨h.2 z ((single_bit z z).mpr rfl),
      Or.inr (h.1 c ((single_bit c c).mpr rfl))⟩
  · intro h
    have hx : wordMixAddEquiv x c = 0 := by
      rcases h.2 with h | h
      · cases h
      · exact h
    constructor
    · intro i hi
      have hic := (single_bit c i).mp hi
      subst i
      exact hx
    · intro i hi
      have hiz := (single_bit z i).mp hi
      subst i
      exact h.1

def rightFalseGraph (c z : Fin 4) : RightDomain c z false ≃
    AffineGraph L (AES8.MarkedZeroOverlap.singleMask c) (AES8.MarkedZeroOverlap.singleMask z) (0 : WordState) 0 where
  toFun x := ⟨x.val, (right_false_iff c z x.val).mpr x.property⟩
  invFun x := ⟨x.val, (right_false_iff c z x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem single_pair_disjoint (c : Fin 4) (s : TripleSplit (outsideMask c)) :
    MaskDisjoint (AES8.MarkedZeroOverlap.singleMask c) (pairMask s.a.val s.b.val) := by
  intro i hi hp
  have ho := pair_le s.a s.b i hp
  exact (outsideMask_bit_iff c i).mp ho ((single_bit c i).mp hi)

private def pairFlatEquiv (V : Type*) :
    ((Unit → V) × (Unit → V)) ≃ (Fin 2 → V) where
  toFun p := ![p.1 (), p.2 ()]
  invFun f := (fun _ => f 0, fun _ => f 1)
  left_inv p := by
    apply Prod.ext <;> funext i <;> cases i <;> rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

/-- Any two named retained output positions label the actual right graph. -/
def rightPairLabels (c z : Fin 4) (s : TripleSplit (outsideMask c)) :
    RightDomain c z false ≃ (Fin 2 → AES.Word) :=
  (rightFalseGraph c z).trans
    ((informationEquiv L wordMixAddEquiv_zeroMDS
      (AES8.MarkedZeroOverlap.singleMask c) (AES8.MarkedZeroOverlap.singleMask z) (pairMask s.a.val s.b.val) 0 0 0
      (single_pair_disjoint c s) (disjoint_empty _)
      (by rw [single_size, single_size,
        pairMask_size s.a.val s.b.val (fun h => s.hab (Subtype.ext h)), empty_size])).trans
          ((outputObservedEquiv (pairMask s.a.val s.b.val) AES.Word).trans
            ((pairEvalEquiv s.a.val s.b.val
              (fun h => s.hab (Subtype.ext h)) AES.Word).trans (pairFlatEquiv AES.Word))))

@[simp] theorem rightPairLabels_first (c z : Fin 4) (s : TripleSplit (outsideMask c))
    (x : RightDomain c z false) :
    rightPairLabels c z s x 0 = wordMixAddEquiv x.val s.a.val := rfl

@[simp] theorem rightPairLabels_second (c z : Fin 4) (s : TripleSplit (outsideMask c))
    (x : RightDomain c z false) :
    rightPairLabels c z s x 1 = wordMixAddEquiv x.val s.b.val := rfl

/-- Split the full triple into two information outputs and one remaining output. -/
def tripleTupleEquiv {middle : Fin 16} (s : TripleSplit middle) (V : Type*) :
    (MaskCoordinates middle → V) ≃ ((Fin 2 → V) × (Unit → V)) where
  toFun f := (![f s.a, f s.b], fun _ => f s.e)
  invFun p i := if i = s.a then p.1 0 else if i = s.b then p.1 1 else p.2 ()
  left_inv f := by
    funext i
    rcases s.cover i with h | h | h <;> subst i <;>
      simp [s.hab, s.hae, s.hbe, Ne.symm s.hab, Ne.symm s.hae, Ne.symm s.hbe]
  right_inv p := by
    apply Prod.ext
    · funext i
      fin_cases i <;>
        simp [s.hab, s.hae, s.hbe, Ne.symm s.hab, Ne.symm s.hae, Ne.symm s.hbe]
    · funext i
      cases i
      simp [s.hab, s.hae, s.hbe, Ne.symm s.hab, Ne.symm s.hae, Ne.symm s.hbe]

def leftSplitLabels (r c : Fin 4) (s : TripleSplit (outsideMask c)) :
    LeftDomain r c true ≃ ((Fin 2 → AES.Word) × (Unit → AES.Word)) :=
  (ReturnCrossMiddle.leftLabels r c).trans (tripleTupleEquiv s AES.Word)

@[simp] theorem leftSplitLabels_first (r c : Fin 4) (s : TripleSplit (outsideMask c))
    (v : LeftDomain r c true) : (leftSplitLabels r c s v).1 0 = v.val s.a.val := rfl

@[simp] theorem leftSplitLabels_second (r c : Fin 4) (s : TripleSplit (outsideMask c))
    (v : LeftDomain r c true) : (leftSplitLabels r c s v).1 1 = v.val s.b.val := rfl

@[simp] theorem leftSplitLabels_remaining (r c : Fin 4) (s : TripleSplit (outsideMask c))
    (v : LeftDomain r c true) : (leftSplitLabels r c s v).2 () = v.val s.e.val := rfl

def pairPosition {middle : Fin 16} (s : TripleSplit middle) : Fin 2 → MaskCoordinates middle :=
  ![s.a, s.b]

@[simp] theorem pairPosition_zero {middle : Fin 16} (s : TripleSplit middle) :
    pairPosition s 0 = s.a := rfl

@[simp] theorem pairPosition_one {middle : Fin 16} (s : TripleSplit middle) :
    pairPosition s 1 = s.b := rfl

-- This is a function on the whole graph point, which is equivalent to its
-- complete information pair. No coordinatewise reconstruction is asserted.
def remainingCode (c z : Fin 4) (s : TripleSplit (outsideMask c))
    (x : RightDomain c z false) (_ : Unit) : AES.Word := wordMixAddEquiv x.val s.e.val

/-- Exact factor-by-factor identification with the existing encoding theorem. -/
theorem middleKernel_eq_encoding (r c z : Fin 4) (s : TripleSplit (outsideMask c))
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ)
    (y : (Fin 2 → AES.Word) × (Unit → AES.Word)) (x : RightDomain c z false) :
    middleKernel r c z true false K ((leftSplitLabels r c s).symm y) x =
      InformationEncoding.kernel (rightPairLabels c z s) (remainingCode c z s)
        (fun i => K (pairPosition s i)) (fun _ : Unit => K s.e) y x := by
  have hYa : ((leftSplitLabels r c s).symm y).val s.a.val = y.1 0 := by
    simpa only [leftSplitLabels_first] using
      congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.1 0)
        ((leftSplitLabels r c s).apply_symm_apply y)
  have hYb : ((leftSplitLabels r c s).symm y).val s.b.val = y.1 1 := by
    simpa only [leftSplitLabels_second] using
      congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.1 1)
        ((leftSplitLabels r c s).apply_symm_apply y)
  have hYe : ((leftSplitLabels r c s).symm y).val s.e.val = y.2 () := by
    simpa only [leftSplitLabels_remaining] using
      congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.2 ())
        ((leftSplitLabels r c s).apply_symm_apply y)
  simp only [middleKernel, prod_three s, InformationEncoding.kernel,
    Fin.prod_univ_two, Fintype.prod_unique, pairPosition_zero,
    pairPosition_one, rightPairLabels_first,
    rightPairLabels_second, remainingCode]
  rw [hYa, hYb, hYe]

theorem middle_action_eq_encoding (r c z : Fin 4) (s : TripleSplit (outsideMask c))
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ)
    (f : RightDomain c z false → ℝ) (y : (Fin 2 → AES.Word) × (Unit → AES.Word)) :
    action (middleKernel r c z true false K) f ((leftSplitLabels r c s).symm y) =
      action (InformationEncoding.kernel (rightPairLabels c z s) (remainingCode c z s)
        (fun i => K (pairPosition s i)) (fun _ : Unit => K s.e)) f y := by
  unfold action
  apply Finset.sum_congr rfl
  intro x _
  rw [middleKernel_eq_encoding r c z s K y x]

/-- 10 middle energy: two information operators and one actual column energy. -/
theorem one_zero_energy (r c z : Fin 4) (s : TripleSplit (outsideMask c))
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ) (delta nu : ℝ)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hC : ∀ x, (∑ y, K s.e y x ^ 2) ≤ delta) (f : RightDomain c z false → ℝ) :
    (∑ v : LeftDomain r c true, action (middleKernel r c z true false K) f v ^ 2) ≤
      delta * nu ^ 4 * ∑ x : RightDomain c z false, f x ^ 2 := by
  rw [← (leftSplitLabels r c s).symm.sum_comp (fun v : LeftDomain r c true =>
    action (middleKernel r c z true false K) f v ^ 2)]
  simp_rw [middle_action_eq_encoding r c z s K f]
  have hb := InformationEncoding.encoding_energy
    (rightPairLabels c z s) (remainingCode c z s)
    (fun i => K (pairPosition s i)) (fun _ : Unit => K s.e) (fun _ : Fin 2 => nu) delta
    (fun i g => hK (pairPosition s i) g) (fun _ x => hC x) f
  have hp : (∏ _i : Fin 2, nu) ^ 2 * delta ^ Fintype.card Unit = delta * nu ^ 4 := by
    simp only [Fin.prod_univ_two, Fintype.card_unique, pow_one]
    ring
  rw [hp] at hb
  exact hb

theorem one_zero_l2 (r c z : Fin 4) (s : TripleSplit (outsideMask c))
    (K : OutsideCoordinates c → AES.Word → AES.Word → ℝ) (delta nu : ℝ)
    (hd : 0 ≤ delta) (hnu : 0 ≤ nu)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hC : ∀ x, (∑ y, K s.e y x ^ 2) ≤ delta) (f : RightDomain c z false → ℝ) :
    l2 (action (middleKernel r c z true false K) f) ≤
      (nu ^ 2 * Real.sqrt delta) * l2 f := by
  apply l2_le_of_energy _ f (nu ^ 2 * Real.sqrt delta)
    (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  rw [show (nu ^ 2 * Real.sqrt delta) ^ 2 = delta * nu ^ 4 by
    rw [mul_pow, Real.sq_sqrt hd]
    ring]
  exact one_zero_energy r c z s K delta nu hK hC f

/-- Actual AES local resources discharge every premise of the 10 middle bound. -/
theorem actual_one_zero_energy (r c z : Fin 4) (s : TripleSplit (outsideMask c))
    (f : RightDomain c z false → ℝ) :
    (∑ v : LeftDomain r c true, action (actualKernel r c z true false) f v ^ 2) ≤
      OneSourceEventMoment.columnCap * SharpWordNorm.rho ^ 4 *
        ∑ x : RightDomain c z false, f x ^ 2 :=
  one_zero_energy r c z s _ OneSourceEventMoment.columnCap SharpWordNorm.rho
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g)
    OneSourceEventMoment.residual_column_le f

end AES8.ReturnCrossMiddleTen
