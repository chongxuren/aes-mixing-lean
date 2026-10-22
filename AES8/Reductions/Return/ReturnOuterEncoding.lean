/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.ProjectedGraph
import AES8.Math.InformationEncoding
import AES8.Estimates.Source.OneSourceEventMoment
import AES8.Estimates.Transfer.SharpDegreeStep

/-!
# The actual outer encoders on both projected left domains

The false domain is the literal graph `(L v)_r = 0, v_c = 0`. Its two
selected forward output coordinates form an information set by the actual
MDS theorem. The third output is reconstructed from the WHOLE pair.
The true domain retains only `(L v)_r = 0`; its full outside output triple
is bijective. The three residual factors are retained in both kernels.

The actual energy constants are `columnCap * rho^4` and `rho^6`, with no
additional operator premise. All coefficient functions may be signed and
joint. The exact projected-action interface below leaves both literal
`frameScalar` factors outside the encoder; the inverse metric is absent.

This module does not close a fixed branch or the return cell.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ReturnOuterEncoding
open AESMixing AESMixing.AES
open AES8.ZeroOutsideProjection
open AES8.ProjectedGraph
open AES8.MDSFiberCollision AES8.MarkedZeroFiber
open AES8.MarkedZeroOverlap (TripleSplit selectedSplit pairMask pairMask_size pair_le
  pairFirst pairSecond pairFirst_ne_second pair_cover outputObservedEquiv)
open AES8.PhysicalZeroPattern (channelTail frameReturnKernel)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

-- These decide only four position names and four-bit masks, never AES values.
private theorem singleMask_size : ∀ r : Fin 4, maskSize (singleMask r) = 1 := by decide
private theorem outsideMask_size : ∀ r : Fin 4, maskSize (outsideMask r) = 3 := by decide
private theorem zero_mask_size : maskSize (0 : Fin 16) = 0 := by decide
private theorem zero_mask_bit : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide

private theorem disjoint_zero (m : Fin 16) : MaskDisjoint m 0 := by
  intro i _ hi
  rw [zero_mask_bit] at hi
  contradiction

private theorem single_outside_disjoint (r : Fin 4) :
    MaskDisjoint (singleMask r) (outsideMask r) := by
  intro i hi ho
  exact ((outsideMask_bit_iff r i).mp ho) ((singleMask_bit_iff r i).mp hi)

theorem boundary_apply_forward (v : WordState) : boundary v = wordMixAddEquiv v := by
  change AESPaper.GroupedRecurrence.boundary v = wordMixAddEquiv v
  rw [AESPaper.BoundaryZeros.boundary_eq_wordMixAddEquiv]

private theorem one_output_graph_iff (r : Fin 4) (v : WordState) :
    graphPrescribed boundary (singleMask r) 0 (0 : WordState) 0 v ↔
      wordMixAddEquiv v r = 0 := by
  constructor
  · intro h
    have hr := h.1 r ((singleMask_bit_iff r r).mpr rfl)
    change boundary v r = 0 at hr
    rwa [boundary_apply_forward] at hr
  · intro h
    constructor
    · intro i hi
      have hir : i = r := (singleMask_bit_iff r i).mp hi
      subst i
      change boundary v r = 0
      rw [boundary_apply_forward]
      exact h
    · intro i hi
      rw [zero_mask_bit] at hi
      contradiction

/-- The exact false projected domain, identified with its actual MDS graph. -/
def falseGraphEquiv (r c : Fin 4) :
    LeftDomain r c false ≃ ZeroGraph (singleMask r) (singleMask c) where
  toFun v := ⟨v.val, (PhysicalZeroPattern.singleton_graph_iff r c v.val).mpr
    (by simpa only [LeftConstraint, frameCondition, Bool.false_eq_true,
      false_or] using v.property)⟩
  invFun v := ⟨v.val, by
    simpa only [LeftConstraint, frameCondition, Bool.false_eq_true, false_or]
      using (PhysicalZeroPattern.singleton_graph_iff r c v.val).mp v.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The exact true projected domain: its middle frame endpoint is constant. -/
def trueGraphEquiv (r c : Fin 4) :
    LeftDomain r c true ≃ ZeroGraph (singleMask r) 0 where
  toFun v := ⟨v.val, (one_output_graph_iff r v.val).mpr v.property.1⟩
  invFun v := ⟨v.val, ⟨(one_output_graph_iff r v.val).mp v.property, Or.inl rfl⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Choose names only inside the literal outside coordinate type. -/
def outsideSplit (r : Fin 4) : TripleSplit (outsideMask r) :=
  selectedSplit (outsideMask r) (outsideMask_size r)

private theorem pair_disjoint (r : Fin 4) :
    MaskDisjoint (singleMask r)
      (pairMask (outsideSplit r).a.val (outsideSplit r).b.val) := by
  intro i hi hp
  exact single_outside_disjoint r i hi
    (pair_le (outsideSplit r).a (outsideSplit r).b i hp)

/-- Two named positions, in their displayed order, become a two-tuple. -/
def pairTupleEquiv (a b : Fin 4) (hab : a ≠ b) (V : Type*) :
    (MaskCoordinates (pairMask a b) → V) ≃ (Fin 2 → V) where
  toFun f := ![f (pairFirst a b), f (pairSecond a b)]
  invFun p i := if i = pairFirst a b then p 0 else p 1
  left_inv f := by
    funext i
    rcases pair_cover a b i with h | h
    · subst i
      simp
    · subst i
      simp [Ne.symm (pairFirst_ne_second a b hab)]
  right_inv p := by
    funext i
    fin_cases i <;> simp [Ne.symm (pairFirst_ne_second a b hab)]

/-- Reorder a literal triple into two information outputs and one last output. -/
def tripleTupleEquiv {middle : Fin 16} (s : TripleSplit middle) (V : Type*) :
    (MaskCoordinates middle → V) ≃ ((Fin 2 → V) × (Unit → V)) where
  toFun f := (![f s.a, f s.b], fun _ => f s.e)
  invFun p i := if i = s.a then p.1 0 else if i = s.b then p.1 1 else p.2 ()
  left_inv f := by
    funext i
    rcases s.cover i with h | h | h
    · subst i
      simp
    · subst i
      simp [Ne.symm s.hab]
    · subst i
      simp [Ne.symm s.hae, Ne.symm s.hbe]
  right_inv p := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [Ne.symm s.hab]
    · funext i
      cases i
      simp [Ne.symm s.hae, Ne.symm s.hbe]

/-- The constrained graph is labeled by two actual forward output positions.
This does not assert that its three-output image is all ambient triples. -/
def falseLabels (r c : Fin 4) : LeftDomain r c false ≃ (Fin 2 → AES.Word) :=
  (falseGraphEquiv r c).trans
    ((informationEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
      (singleMask r) (singleMask c)
      (pairMask (outsideSplit r).a.val (outsideSplit r).b.val) 0 0 0
      (pair_disjoint r) (disjoint_zero (singleMask c))
      (by rw [singleMask_size, singleMask_size,
        pairMask_size _ _ (fun h => (outsideSplit r).hab (Subtype.ext h)),
        zero_mask_size])).trans
      ((outputObservedEquiv _ AES.Word).trans
        (pairTupleEquiv (outsideSplit r).a.val (outsideSplit r).b.val
          (fun h => (outsideSplit r).hab (Subtype.ext h)) AES.Word)))

/-- On the one-zero hyperplane, the whole literal outside output triple labels v. -/
def trueLabels (r c : Fin 4) :
    LeftDomain r c true ≃ (OutsideCoordinates r → AES.Word) :=
  (trueGraphEquiv r c).trans
    ((informationEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
      (singleMask r) 0 (outsideMask r) 0 0 0
      (single_outside_disjoint r) (disjoint_zero 0)
      (by rw [singleMask_size, zero_mask_size, outsideMask_size])).trans
        (outputObservedEquiv _ AES.Word))

@[simp] theorem falseLabels_zero (r c : Fin 4) (v : LeftDomain r c false) :
    falseLabels r c v 0 = wordMixAddEquiv v.val (outsideSplit r).a.val := by
  change boundary v.val (outsideSplit r).a.val = _
  rw [boundary_apply_forward]

@[simp] theorem falseLabels_one (r c : Fin 4) (v : LeftDomain r c false) :
    falseLabels r c v 1 = wordMixAddEquiv v.val (outsideSplit r).b.val := by
  change boundary v.val (outsideSplit r).b.val = _
  rw [boundary_apply_forward]

@[simp] theorem trueLabels_coordinate (r c : Fin 4) (v : LeftDomain r c true)
    (i : OutsideCoordinates r) :
    trueLabels r c v i = wordMixAddEquiv v.val i.val := by
  change boundary v.val i.val = _
  rw [boundary_apply_forward]

@[simp] theorem trueLabels_symm_coordinate (r c : Fin 4)
    (x : OutsideCoordinates r → AES.Word) (i : OutsideCoordinates r) :
    wordMixAddEquiv ((trueLabels r c).symm x).val i.val = x i := by
  simpa only [trueLabels_coordinate] using
    congrFun ((trueLabels r c).apply_symm_apply x) i

/-- All three local channels remain, with literal output coordinate names. -/
def kernel {r c : Fin 4} (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ)
    (s : Bool) (w : OutsideCoordinates r → AES.Word) (v : LeftDomain r c s) : ℝ :=
  ∏ i, K i (w i) (wordMixAddEquiv v.val i.val)

def informationPosition (r : Fin 4) (i : Fin 2) : OutsideCoordinates r :=
  ![(outsideSplit r).a, (outsideSplit r).b] i

-- The third coordinate is allowed to depend on the complete source graph point,
-- equivalently the entire two-coordinate label. No coordinatewise premise enters.
def remainingOutput (r c : Fin 4) (v : LeftDomain r c false) (_ : Unit) : AES.Word :=
  wordMixAddEquiv v.val (outsideSplit r).e.val

/-- Exact identification with the information-set encoder, without a kernel premise. -/
theorem false_kernel_eq_encoding (r c : Fin 4)
    (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ)
    (y : (Fin 2 → AES.Word) × (Unit → AES.Word)) (v : LeftDomain r c false) :
    kernel K false ((tripleTupleEquiv (outsideSplit r) AES.Word).symm y) v =
      InformationEncoding.kernel (falseLabels r c) (remainingOutput r c)
        (fun i => K (informationPosition r i)) (fun _ : Unit => K (outsideSplit r).e)
        y v := by
  have hYa : ((tripleTupleEquiv (outsideSplit r) AES.Word).symm y)
      (outsideSplit r).a = y.1 0 := by
    exact congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.1 0)
      ((tripleTupleEquiv (outsideSplit r) AES.Word).apply_symm_apply y)
  have hYb : ((tripleTupleEquiv (outsideSplit r) AES.Word).symm y)
      (outsideSplit r).b = y.1 1 := by
    exact congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.1 1)
      ((tripleTupleEquiv (outsideSplit r) AES.Word).apply_symm_apply y)
  have hYe : ((tripleTupleEquiv (outsideSplit r) AES.Word).symm y)
      (outsideSplit r).e = y.2 () := by
    exact congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.2 ())
      ((tripleTupleEquiv (outsideSplit r) AES.Word).apply_symm_apply y)
  unfold kernel
  rw [AES8.MarkedZeroOverlap.prod_three (outsideSplit r)]
  simp only [InformationEncoding.kernel, Fin.prod_univ_two, Fintype.prod_unique]
  change
    K (outsideSplit r).a
        (((tripleTupleEquiv (outsideSplit r) AES.Word).symm y) (outsideSplit r).a)
        (wordMixAddEquiv v.val (outsideSplit r).a.val) *
      K (outsideSplit r).b
        (((tripleTupleEquiv (outsideSplit r) AES.Word).symm y) (outsideSplit r).b)
        (wordMixAddEquiv v.val (outsideSplit r).b.val) *
      K (outsideSplit r).e
        (((tripleTupleEquiv (outsideSplit r) AES.Word).symm y) (outsideSplit r).e)
        (wordMixAddEquiv v.val (outsideSplit r).e.val) =
      (K (outsideSplit r).a (y.1 0) (falseLabels r c v 0) *
        K (outsideSplit r).b (y.1 1) (falseLabels r c v 1)) *
        K (outsideSplit r).e (y.2 ()) (wordMixAddEquiv v.val (outsideSplit r).e.val)
  rw [hYa, hYb, hYe, falseLabels_zero, falseLabels_one]

/-- Signed action identity on the constrained graph; there is no input factorization. -/
theorem false_action_eq_encoding (r c : Fin 4)
    (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ)
    (f : LeftDomain r c false → ℝ)
    (y : (Fin 2 → AES.Word) × (Unit → AES.Word)) :
    action (kernel K false) f ((tripleTupleEquiv (outsideSplit r) AES.Word).symm y) =
      action (InformationEncoding.kernel (falseLabels r c) (remainingOutput r c)
        (fun i => K (informationPosition r i)) (fun _ : Unit => K (outsideSplit r).e))
        f y := by
  unfold action
  apply Finset.sum_congr rfl
  intro v _
  rw [false_kernel_eq_encoding]

/-- The full one-zero outer action is a literal tensor action after a bijection. -/
theorem true_action_eq_tensor (r c : Fin 4)
    (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ)
    (f : LeftDomain r c true → ℝ) (w : OutsideCoordinates r → AES.Word) :
    action (kernel K true) f w =
      action (coordinateKernel K) (fun x => f ((trueLabels r c).symm x)) w := by
  unfold action kernel coordinateKernel
  rw [← (trueLabels r c).symm.sum_comp (fun v : LeftDomain r c true =>
    (∏ i, K i (w i) (wordMixAddEquiv v.val i.val)) * f v)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [trueLabels_symm_coordinate]

/-- Two information operators plus one created column, on arbitrary signed input. -/
theorem false_tensor_energy (r c : Fin 4)
    (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ) (delta nu : ℝ)
    (hK : ∀ i g, (∑ y, action (K (informationPosition r i)) g y ^ 2) ≤
      nu ^ 2 * ∑ x, g x ^ 2)
    (hE : ∀ x, (∑ y, K (outsideSplit r).e y x ^ 2) ≤ delta)
    (f : LeftDomain r c false → ℝ) :
    (∑ w, action (kernel K false) f w ^ 2) ≤
      delta * nu ^ 4 * ∑ v, f v ^ 2 := by
  rw [← (tripleTupleEquiv (outsideSplit r) AES.Word).symm.sum_comp
    (fun w => action (kernel K false) f w ^ 2)]
  simp_rw [false_action_eq_encoding r c K f]
  have he := InformationEncoding.encoding_energy (falseLabels r c) (remainingOutput r c)
    (fun i => K (informationPosition r i)) (fun _ : Unit => K (outsideSplit r).e)
    (fun _ : Fin 2 => nu) delta hK (fun _ x => hE x) f
  have hp : (∏ _i : Fin 2, nu) ^ 2 = nu ^ 4 := by
    rw [Fin.prod_univ_two]
    ring
  simp only [hp, Fintype.card_unique, pow_one] at he
  calc
    _ ≤ nu ^ 4 * delta * ∑ v, f v ^ 2 := he
    _ = _ := by ring

/-- The full outside triple has three ordinary local operator factors. -/
theorem true_tensor_energy (r c : Fin 4)
    (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ) (nu : ℝ)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : LeftDomain r c true → ℝ) :
    (∑ w, action (kernel K true) f w ^ 2) ≤
      nu ^ 6 * ∑ v, f v ^ 2 := by
  simp_rw [true_action_eq_tensor r c K f]
  have he := AESConcrete.FiniteTensorEnergy.coordinate_energy K
    (fun _ : OutsideCoordinates r => nu) hK (fun x => f ((trueLabels r c).symm x))
  have hp : (∏ _i : OutsideCoordinates r, nu) ^ 2 = nu ^ 6 := by
    rw [Finset.prod_const, Finset.card_univ, maskCoordinates_card, outsideMask_size]
    ring
  rw [hp, (trueLabels r c).symm.sum_comp (fun v => f v ^ 2)] at he
  exact he

theorem false_tensor_l2 (r c : Fin 4)
    (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ) (delta nu : ℝ)
    (hd : 0 ≤ delta)
    (hK : ∀ i g, (∑ y, action (K (informationPosition r i)) g y ^ 2) ≤
      nu ^ 2 * ∑ x, g x ^ 2)
    (hE : ∀ x, (∑ y, K (outsideSplit r).e y x ^ 2) ≤ delta)
    (f : LeftDomain r c false → ℝ) :
    l2 (action (kernel K false) f) ≤ (nu ^ 2 * Real.sqrt delta) * l2 f := by
  apply l2_le_of_energy _ f (nu ^ 2 * Real.sqrt delta)
    (mul_nonneg (sq_nonneg nu) (Real.sqrt_nonneg _))
  rw [show (nu ^ 2 * Real.sqrt delta) ^ 2 = delta * nu ^ 4 by
    rw [mul_pow, Real.sq_sqrt hd]
    ring]
  exact false_tensor_energy r c K delta nu hK hE f

theorem true_tensor_l2 (r c : Fin 4)
    (K : OutsideCoordinates r → AES.Word → AES.Word → ℝ) (nu : ℝ) (hnu : 0 ≤ nu)
    (hK : ∀ i g, (∑ y, action (K i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : LeftDomain r c true → ℝ) :
    l2 (action (kernel K true) f) ≤ nu ^ 3 * l2 f := by
  apply l2_le_of_energy _ f (nu ^ 3) (pow_nonneg hnu _)
  rw [show (nu ^ 3) ^ 2 = nu ^ 6 by ring]
  exact true_tensor_energy r c K nu hK f

/-- The actual forward outer residual channel, with no caller-supplied norm cap. -/
def actualKernel {r c : Fin 4} (s : Bool) :
    (OutsideCoordinates r → AES.Word) → LeftDomain r c s → ℝ :=
  kernel (fun _ : OutsideCoordinates r => residualMatrix AES.wordSuperboxKernel 0) s

theorem actual_false_energy (r c : Fin 4) (f : LeftDomain r c false → ℝ) :
    (∑ w, action (actualKernel false) f w ^ 2) ≤
      OneSourceEventMoment.columnCap * SharpWordNorm.rho ^ 4 * ∑ v, f v ^ 2 :=
  -- Give K explicitly: inferring it through a selected coordinate causes Lean
  -- to unfold the finite choice and concrete boundary during definitional equality.
  false_tensor_energy r c
    (fun _ : OutsideCoordinates r => residualMatrix AES.wordSuperboxKernel 0)
    OneSourceEventMoment.columnCap SharpWordNorm.rho
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g)
    OneSourceEventMoment.residual_column_le f

theorem actual_true_energy (r c : Fin 4) (f : LeftDomain r c true → ℝ) :
    (∑ w, action (actualKernel true) f w ^ 2) ≤
      SharpWordNorm.rho ^ 6 * ∑ v, f v ^ 2 :=
  true_tensor_energy r c
    (fun _ : OutsideCoordinates r => residualMatrix AES.wordSuperboxKernel 0)
    SharpWordNorm.rho
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g) f

theorem actual_false_l2 (r c : Fin 4) (f : LeftDomain r c false → ℝ) :
    l2 (action (actualKernel false) f) ≤
      (SharpWordNorm.rho ^ 2 * Real.sqrt OneSourceEventMoment.columnCap) * l2 f :=
  false_tensor_l2 r c
    (fun _ : OutsideCoordinates r => residualMatrix AES.wordSuperboxKernel 0)
    OneSourceEventMoment.columnCap SharpWordNorm.rho
    (by norm_num [OneSourceEventMoment.columnCap, AESPaper.StartingWord.q])
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g)
    OneSourceEventMoment.residual_column_le f

theorem actual_true_l2 (r c : Fin 4) (f : LeftDomain r c true → ℝ) :
    l2 (action (actualKernel true) f) ≤ SharpWordNorm.rho ^ 3 * l2 f :=
  true_tensor_l2 r c
    (fun _ : OutsideCoordinates r => residualMatrix AES.wordSuperboxKernel 0)
    SharpWordNorm.rho (by norm_num [SharpWordNorm.rho])
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g) f

/-- The counting-triple kernel equals the outer tail in the physical identity.
The omitted y-coordinate never enters the tail, so no support premise is needed. -/
theorem actualKernel_eq_channelTail (r c : Fin 4) (s : Bool) (y : WordState)
    (v : LeftDomain r c s) :
    actualKernel s (fun i => y i.val) v =
      channelTail wordSuperboxKernel 0 r y (wordMixAddEquiv v.val) := by
  unfold actualKernel kernel channelTail
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : Fin 4 => maskBit (outsideMask r) i = true)]
  have hm (i : OutsideCoordinates r) :
      (if i.val = r then (1 : ℝ) else residualMatrix wordSuperboxKernel 0
        (y i.val) (wordMixAddEquiv v.val i.val)) =
      residualMatrix wordSuperboxKernel 0 (y i.val) (wordMixAddEquiv v.val i.val) := by
    simp only [(outsideMask_bit_iff r i.val).mp i.property, if_false]
  have hu (i : {i : Fin 4 // ¬maskBit (outsideMask r) i = true}) :
      (if i.val = r then (1 : ℝ) else residualMatrix wordSuperboxKernel 0
        (y i.val) (wordMixAddEquiv v.val i.val)) = 1 := by
    have hi : i.val = r := by
      by_contra hne
      exact i.property ((outsideMask_bit_iff r i.val).mpr hne)
    exact if_pos hi
  simp_rw [hm, hu]
  simp only [Finset.prod_const_one, _root_.mul_one]

/-- Exact interface to all four projected frame branches. Both endpoint
factors remain literal, and the input coefficient remains the full signed joint one. -/
theorem projected_frame_eq_embed_outer (r c z : Fin 4) (s t : Bool)
    (f : WordState → ℝ) :
    Q r (action (frameReturnKernel c s t) (Q z f)) =
      embedZero r (fun w => frameScalar s * frameScalar t *
        action (actualKernel s)
          (fun v : LeftDomain r c s =>
            ∑ x : RightDomain c z t,
              channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) *
                inputCoefficient z f x.val) w) := by
  funext y
  rw [projected_frame_action, embedZero_apply]
  by_cases hy : y r = 0
  · simp only [hy, if_true]
    unfold action
    simp_rw [actualKernel_eq_channelTail]
  · simp only [hy, if_false]

/-- The four-middle left hyperplane is the true frame domain with an inert c label. -/
def hyperplaneEquiv (r c : Fin 4) : LeftHyperplane r ≃ LeftDomain r c true where
  toFun v := ⟨v.val, ⟨v.property, Or.inl rfl⟩⟩
  invFun v := ⟨v.val, v.property.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The same actual three-channel encoder on the literal four-middle left domain. -/
def hyperplaneKernel (r : Fin 4) (w : OutsideCoordinates r → AES.Word)
    (v : LeftHyperplane r) : ℝ :=
  actualKernel true w (hyperplaneEquiv r 0 v)

theorem hyperplane_action_eq_true (r : Fin 4) (f : LeftHyperplane r → ℝ)
    (w : OutsideCoordinates r → AES.Word) :
    action (hyperplaneKernel r) f w =
      action (actualKernel true) (fun v => f ((hyperplaneEquiv r 0).symm v)) w := by
  unfold action hyperplaneKernel
  simpa only [Equiv.symm_apply_apply] using
    (hyperplaneEquiv r 0).sum_comp (fun v : LeftDomain r 0 true =>
      actualKernel true w v * f ((hyperplaneEquiv r 0).symm v))

theorem actual_hyperplane_energy (r : Fin 4) (f : LeftHyperplane r → ℝ) :
    (∑ w, action (hyperplaneKernel r) f w ^ 2) ≤
      SharpWordNorm.rho ^ 6 * ∑ v, f v ^ 2 := by
  simp_rw [hyperplane_action_eq_true r f]
  have he := actual_true_energy r 0 (fun v => f ((hyperplaneEquiv r 0).symm v))
  rw [(hyperplaneEquiv r 0).symm.sum_comp (fun v => f v ^ 2)] at he
  exact he

theorem actual_hyperplane_l2 (r : Fin 4) (f : LeftHyperplane r → ℝ) :
    l2 (action (hyperplaneKernel r) f) ≤ SharpWordNorm.rho ^ 3 * l2 f := by
  apply l2_le_of_energy _ f (SharpWordNorm.rho ^ 3)
    (pow_nonneg (by norm_num [SharpWordNorm.rho]) _)
  rw [show (SharpWordNorm.rho ^ 3) ^ 2 = SharpWordNorm.rho ^ 6 by ring]
  exact actual_hyperplane_energy r f

theorem hyperplaneKernel_eq_channelTail (r : Fin 4) (y : WordState)
    (v : LeftHyperplane r) :
    hyperplaneKernel r (fun i => y i.val) v =
      channelTail wordSuperboxKernel 0 r y (wordMixAddEquiv v.val) :=
  actualKernel_eq_channelTail r 0 true y (hyperplaneEquiv r 0 v)

/-- Exact four-middle action on its actual hyperplanes, using the same outer encoder. -/
theorem projected_four_eq_embed_outer (r z : Fin 4) (f : WordState → ℝ) :
    Q r (action PhysicalZeroPattern.fourReturnKernel (Q z f)) =
      embedZero r (fun w => action (hyperplaneKernel r)
        (fun v : LeftHyperplane r =>
          ∑ x : RightHyperplane z,
            AESConcrete.FourResidualStep.residualTensor v.val (wordMixAddEquiv x.val) *
              inputCoefficient z f x.val) w) := by
  funext y
  rw [projected_four_action, embedZero_apply]
  by_cases hy : y r = 0
  · simp only [hy, if_true]
    unfold action
    simp_rw [hyperplaneKernel_eq_channelTail]
  · simp only [hy, if_false]

end AES8.ReturnOuterEncoding
