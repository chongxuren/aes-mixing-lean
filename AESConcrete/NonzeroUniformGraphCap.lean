import AESConcrete.FourierGraphEnergy
import AESConcrete.MDSGraphEnergy
import AESConcrete.FourResidualStep
import AESConcrete.PhysicalProjectionSystem
import AESRound.CertificateData
import AESRound.Terminal

/-!
# graph-column cap for the actual `(13,12)` step

The source `(3,4)` projection has four orthogonal exact-support pieces. Each
has one normalized nonzero-uniform leg and an arbitrary joint three-coordinate
remainder. The exact identity `u+ = (sqrt(q) * u0 - delta0) / sqrt(q-1)`
supplies the two graph estimates. Weighted Cauchy--Schwarz combines those two
outputs; pointwise four-term Cauchy--Schwarz aggregates the support pieces.
Neither step assumes output orthogonality. Normalization, the source bridge,
analysis, and the physical and scalar certificate interfaces are separate
below.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and the 10/14/16 target stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.NonzeroUniformGraphCap
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.RefinedWordProjection (refinedKernel supportIndexKernel)
open AESConcrete.RefinedStepZeros (physicalBlock blockType)
open AESConcrete.FourResidualStep (residualTensor residualStepKernel)
open AESConcrete.MDSGraphSupport (splitAt)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

local notation "ρ" => (21 / 131072 : ℝ)
local notation "κ" => (2 / (15 * 4294967296) : ℝ)

section NormalizedLeg
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Unit vector on the nonzero symbols, with counting measure. -/
def nonzeroUniform (x : V) : ℝ :=
  supportConstant false x / Real.sqrt ((Fintype.card V : ℝ) - 1)

/-- Unit vector on all symbols, including zero. -/
def fullUniform (_x : V) : ℝ := 1 / Real.sqrt (Fintype.card V : ℝ)

/-- Unit vector supported at zero. -/
def zeroUnit (x : V) : ℝ := supportConstant true x

theorem nonzeroUniform_energy (hn : 1 < Fintype.card V) :
    (∑ x : V, nonzeroUniform x ^ 2) = 1 := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : 0 < (Fintype.card V : ℝ) - 1 := by linarith
  simp only [nonzeroUniform, div_pow]
  rw [← Finset.sum_div, supportConstant_energy]
  simp only [Bool.false_eq_true, if_false]
  rw [Real.sq_sqrt (le_of_lt hd), div_self (ne_of_gt hd)]

omit [AddCommGroup V] [DecidableEq V] in
theorem fullUniform_energy (hn : 1 < Fintype.card V) :
    (∑ x : V, fullUniform x ^ 2) = 1 := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hq : 0 < (Fintype.card V : ℝ) := by linarith
  simp only [fullUniform, div_pow, one_pow]
  rw [← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Real.sq_sqrt (le_of_lt hq), div_self (ne_of_gt hq)]

theorem zeroUnit_energy : (∑ x : V, zeroUnit x ^ 2) = 1 := by
  simpa only [zeroUnit, if_true] using (supportConstant_energy (V := V) true)

/-- The source calls this projection `constantMatrix`; it is precisely the
rank-one nonzero-constant projection, with its exact unit normalization. -/
theorem nonzeroConstantMatrix_rank_one (hn : 1 < Fintype.card V) (y x : V) :
    constantMatrix (0 : V) y x = nonzeroUniform y * nonzeroUniform x := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hd : 0 < (Fintype.card V : ℝ) - 1 := by linarith
  have hk : constantMatrix (0 : V) y x =
      supportConstant false y *
        (supportConstant false x / ((Fintype.card V : ℝ) - 1)) := by
    simpa only [supportPiece, Bool.false_eq_true, if_false, supportDualConstant] using
      (supportPiece_unmarked (V := V) false y x)
  rw [hk]
  unfold nonzeroUniform
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (le_of_lt hd)]
  ring

/-- Exact normalized identity. The zero symbol is retained in `u0`. -/
theorem nonzeroUniform_decomposition (hn : 1 < Fintype.card V) (x : V) :
    nonzeroUniform x =
      (Real.sqrt (Fintype.card V : ℝ) * fullUniform x - zeroUnit x) /
        Real.sqrt ((Fintype.card V : ℝ) - 1) := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hq : 0 < (Fintype.card V : ℝ) := by linarith
  have hs : Real.sqrt (Fintype.card V : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hc : supportConstant false x = 1 - supportConstant true x := by
    simp only [supportConstant, Bool.false_eq_true, if_false, if_true]
  have hu : Real.sqrt (Fintype.card V : ℝ) *
      (1 / Real.sqrt (Fintype.card V : ℝ)) = 1 := by field_simp [hs]
  unfold nonzeroUniform fullUniform zeroUnit
  rw [hu, ← hc]

/-- Only the distinguished leg factors. The three-coordinate remainder is
an arbitrary signed joint function. -/
def rankOneLeg (r : Fin 4) (u : V → ℝ) (h : (Fin 3 → V) → ℝ)
    (x : Fin 4 → V) : ℝ := u (x r) * h (Fin.removeNth r x)

omit [AddCommGroup V] [DecidableEq V] in
theorem rankOneLeg_energy (r : Fin 4) (u : V → ℝ)
    (hu : (∑ x, u x ^ 2) = 1) (h : (Fin 3 → V) → ℝ) :
    (∑ x, rankOneLeg r u h x ^ 2) = ∑ w, h w ^ 2 := by
  have he : (∑ x, rankOneLeg r u h x ^ 2) =
      ∑ p : V × (Fin 3 → V), (u p.1 * h p.2) ^ 2 :=
    (splitAt (V := V) r).sum_comp (fun p => (u p.1 * h p.2) ^ 2)
  rw [he, Fintype.sum_prod_type]
  simp_rw [mul_pow]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hu, one_mul]

omit [AddCommGroup V] [DecidableEq V] in
/-- A rank-one coordinate kernel exposes a joint remainder without imposing
any product structure on the other coordinates or on the original input. -/
theorem coordinateKernel_rank_one_action (T : Fin 4 → V → V → ℝ)
    (r : Fin 4) (u : V → ℝ) (hr : ∀ y x, T r y x = u y * u x)
    (f : (Fin 4 → V) → ℝ) :
    ∃ h : (Fin 3 → V) → ℝ, action (coordinateKernel T) f = rankOneLeg r u h := by
  let h : (Fin 3 → V) → ℝ := fun w =>
    ∑ x, u (x r) *
      (∏ i : Fin 3, T (r.succAbove i) (w i) (x (r.succAbove i))) * f x
  refine ⟨h, ?_⟩
  funext y
  unfold action rankOneLeg
  dsimp [h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [coordinateKernel, Fin.prod_univ_succAbove
    (fun i => T i (y i) (x i)) r, hr]
  change (u (y r) * u (x r)) *
      (∏ i : Fin 3, T (r.succAbove i) (y (r.succAbove i)) (x (r.succAbove i))) * f x =
    u (y r) * (u (x r) *
      (∏ i : Fin 3, T (r.succAbove i) (y (r.succAbove i)) (x (r.succAbove i))) * f x)
  ring

/-- A normalized rank-one source piece has exactly the remainder's energy. -/
theorem supportIndexComponent_nonzero_uniform {d : ℕ} (p : SupportIndex d)
    (r : Fin 4) (hm : maskBit p.val.1 r = false) (hi : maskBit p.val.2 r = false)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    ∃ h : (Fin 3 → V) → ℝ,
      supportIndexComponent (0 : V) p f = rankOneLeg r nonzeroUniform h ∧
      (∑ x, supportIndexComponent (0 : V) p f x ^ 2) = ∑ w, h w ^ 2 := by
  obtain ⟨h, hh⟩ := coordinateKernel_rank_one_action
    (fun i => supportPiece (0 : V) (maskBit p.val.1 i) (maskBit p.val.2 i))
    r nonzeroUniform (by
      intro y x
      simp only [hm, hi, supportPiece, Bool.false_eq_true, if_false]
      exact nonzeroConstantMatrix_rank_one hn y x) f
  have hpiece : supportIndexComponent (0 : V) p f = rankOneLeg r nonzeroUniform h := hh
  refine ⟨h, hpiece, ?_⟩
  rw [hpiece]
  exact rankOneLeg_energy r nonzeroUniform (nonzeroUniform_energy hn) h

theorem rankOneLeg_nonzero_decomposition (hn : 1 < Fintype.card V)
    (r : Fin 4) (h : (Fin 3 → V) → ℝ) :
    rankOneLeg r nonzeroUniform h = fun x =>
      (Real.sqrt (Fintype.card V : ℝ) * rankOneLeg r fullUniform h x -
        rankOneLeg r zeroUnit h x) / Real.sqrt ((Fintype.card V : ℝ) - 1) := by
  funext x
  rw [rankOneLeg, nonzeroUniform_decomposition hn]
  simp only [rankOneLeg]
  ring

omit [DecidableEq V] in
theorem fullUniform_leg_invariant (r : Fin 4) (h : (Fin 3 → V) → ℝ) :
    ∀ (x : Fin 4 → V) (t : V),
      rankOneLeg r fullUniform h (x + Pi.single r t) = rankOneLeg r fullUniform h x := by
  intro x t
  have he : Fin.removeNth r (x + Pi.single r t) = Fin.removeNth r x := by
    funext i
    change x (r.succAbove i) + (Pi.single r t : Fin 4 → V) (r.succAbove i) = x (r.succAbove i)
    simp [Fin.succAbove_ne]
  simp only [rankOneLeg, fullUniform, he]

omit [Fintype V] in
theorem zeroUnit_leg_zero_slab (r : Fin 4) (h : (Fin 3 → V) → ℝ) :
    ∀ x, rankOneLeg r zeroUnit h x ≠ 0 → x r = 0 := by
  intro x hx
  by_contra hxr
  apply hx
  simp [rankOneLeg, zeroUnit, supportConstant, identityKernel, hxr]

end NormalizedLeg

section FiniteSumAlgebra

private theorem action_sub_div {X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (a d : ℝ) (f g : X → ℝ) :
    action K (fun x => (a * f x - g x) / d) =
      fun y => (a * action K f y - action K g y) / d := by
  funext y
  unfold action
  calc
    (∑ x, K y x * ((a * f x - g x) / d)) =
        ∑ x, (a * (K y x * f x) - K y x * g x) / d := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Weighted two-vector Cauchy--Schwarz. Both input energies have the same
cap; this retains the exact `(a+1)^2` coefficient without output orthogonality
or rounded square roots. All vector entries may have either sign. -/
theorem weighted_sub_energy {Y : Type*} [Fintype Y]
    (A B : Y → ℝ) (a d C E : ℝ) (ha : 0 ≤ a)
    (hA : (∑ y, A y ^ 2) ≤ C * E) (hB : (∑ y, B y ^ 2) ≤ C * E) :
    (∑ y, ((a * A y - B y) / d) ^ 2) ≤
      ((a + 1) ^ 2 * C / d ^ 2) * E := by
  have hp (y : Y) : (a * A y - B y) ^ 2 ≤
      (a + 1) * (a * A y ^ 2 + B y ^ 2) := by
    have h := mul_nonneg ha (sq_nonneg (A y + B y))
    nlinarith
  have hsum : (∑ y, (a * A y - B y) ^ 2) ≤ (a + 1) ^ 2 * (C * E) := by
    calc
      _ ≤ ∑ y, (a + 1) * (a * A y ^ 2 + B y ^ 2) :=
        Finset.sum_le_sum (fun y _ => hp y)
      _ = (a + 1) * (a * (∑ y, A y ^ 2) + ∑ y, B y ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ (a + 1) * (a * (C * E) + C * E) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact add_le_add (mul_le_mul_of_nonneg_left hA ha) hB
      _ = _ := by ring
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  exact (div_le_div_of_nonneg_right hsum (sq_nonneg d)).trans_eq (by ring)

private theorem action_finset_sum {I X Y : Type*} [Fintype X]
    (K : Y → X → ℝ) (s : Finset I) (f : I → X → ℝ) :
    action K (fun x => ∑ i ∈ s, f i x) =
      fun y => ∑ i ∈ s, action K (f i) y := by
  funext y
  simp only [action, Finset.mul_sum]
  exact Finset.sum_comm

end FiniteSumAlgebra

section ActualLegEnergy

private theorem word_sqrt_card : Real.sqrt (Fintype.card AES.Word : ℝ) = 65536 := by
  rw [AES.word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

/-- Reindexing identity only; all analytic premises remain in their own
ordinary zero-slab and Fourier-uniform theorems. -/
theorem residualStep_action (f : AES.WordState → ℝ) :
    action residualStepKernel f =
      action residualTensor (fun z => f (wordMixAddEquiv.symm z)) := by
  exact FourResidualStep.input_permutation_action residualTensor wordMixAddEquiv.toEquiv f

/-- Exact nonzero-uniform-leg estimate on arbitrary joint three-leg inputs.
The only two analytical premises are the actual ordinary zero-slab bound and
the actual Fourier translation-invariant-coordinate bound. -/
theorem word_nonzero_uniform_leg_energy (r s : Fin 4)
    (h : (Fin 3 → AES.Word) → ℝ) :
    (∑ y, action residualStepKernel (rankOneLeg r nonzeroUniform h) y ^ 2) ≤
      (ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) *
        ∑ x, rankOneLeg r nonzeroUniform h x ^ 2 := by
  have hn : 1 < Fintype.card AES.Word := by rw [AES.word_card]; norm_num
  have hU := FourierGraphEnergy.word_residual_uniform_coordinate_energy r s
    (rankOneLeg r fullUniform h) (fullUniform_leg_invariant r h)
  have hD := MDSGraphEnergy.word_residual_zero_slab_energy r s
    (rankOneLeg r zeroUnit h) (zeroUnit_leg_zero_slab r h)
  change (∑ y, action residualTensor
    (fun z => rankOneLeg r fullUniform h (wordMixAddEquiv.symm z)) y ^ 2) ≤ _ at hU
  change (∑ y, action residualTensor
    (fun z => rankOneLeg r zeroUnit h (wordMixAddEquiv.symm z)) y ^ 2) ≤ _ at hD
  rw [← residualStep_action] at hU hD
  rw [rankOneLeg_energy r fullUniform (fullUniform_energy hn) h] at hU
  rw [rankOneLeg_energy r zeroUnit zeroUnit_energy h] at hD
  have hdec := rankOneLeg_nonzero_decomposition hn r h
  rw [word_sqrt_card] at hdec
  have hact : action residualStepKernel (rankOneLeg r nonzeroUniform h) =
      fun y => (65536 * action residualStepKernel (rankOneLeg r fullUniform h) y -
        action residualStepKernel (rankOneLeg r zeroUnit h) y) /
          Real.sqrt ((Fintype.card AES.Word : ℝ) - 1) := by
    rw [hdec]
    exact action_sub_div residualStepKernel 65536 _ _ _
  rw [hact, rankOneLeg_energy r nonzeroUniform (nonzeroUniform_energy hn) h]
  have he := weighted_sub_energy
    (action residualStepKernel (rankOneLeg r fullUniform h))
    (action residualStepKernel (rankOneLeg r zeroUnit h))
    65536 (Real.sqrt ((Fintype.card AES.Word : ℝ) - 1))
    (ρ ^ 6 * κ) (∑ w, h w ^ 2) (by norm_num) hU hD
  have hs : (Real.sqrt ((Fintype.card AES.Word : ℝ) - 1)) ^ 2 =
      (4294967296 - 1 : ℝ) := by
    rw [AES.word_card]
    exact Real.sq_sqrt (by norm_num)
  rw [hs] at he
  convert he using 1
  norm_num

/-- Any genuine support piece whose distinguished leg is unmarked and
active receives the normalized estimate; no condition on its other legs is
used in this analytic statement. -/
theorem word_nonzero_uniform_support_piece_energy {d : ℕ} (p : SupportIndex d)
    (r s : Fin 4) (hm : maskBit p.val.1 r = false) (hi : maskBit p.val.2 r = false)
    (f : AES.WordState → ℝ) :
    (∑ y, action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y ^ 2) ≤
      (ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) *
        ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 := by
  obtain ⟨h, hh, _⟩ := supportIndexComponent_nonzero_uniform p r hm hi
    (by rw [AES.word_card]; norm_num) f
  rw [hh]
  exact word_nonzero_uniform_leg_energy r s h

end ActualLegEnergy

section SelectedSupports

/-- The exact support indices selected by the physical `(3,4)` input. -/
def selectedSupport3 : Finset (SupportIndex 3) :=
  Finset.univ.filter (fun p => maskSize p.val.2 + 4 = 4)

set_option maxRecDepth 100000 in
theorem selectedSupport3_card : selectedSupport3.card = 4 := by decide

set_option maxRecDepth 100000 in
private theorem degree_three_active_uniform_coordinate : ∀ p : SupportIndex 3,
    maskSize p.val.2 + 4 = 4 →
      ∃ r : Fin 4, maskBit p.val.1 r = false ∧ maskBit p.val.2 r = false := by decide

theorem selectedSupport3_uniform_coordinate (p : SupportIndex 3)
    (hp : p ∈ selectedSupport3) :
    ∃ r : Fin 4, maskBit p.val.1 r = false ∧ maskBit p.val.2 r = false :=
  degree_three_active_uniform_coordinate p (Finset.mem_filter.mp hp).2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact action expansion of the existing source projection. -/
theorem refined_three_four_action_sum (z : V) (f : (Fin 4 → V) → ℝ) :
    action (refinedKernel z 3 4) f =
      fun x => ∑ p ∈ selectedSupport3, supportIndexComponent z p f x := by
  funext y
  unfold action refinedKernel
  change (∑ x, (∑ p : SupportIndex 3,
    if maskSize p.val.2 + 4 = 4 then supportIndexKernel z p y x else 0) * f x) =
      ∑ p ∈ selectedSupport3, supportIndexComponent z p f y
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [selectedSupport3, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : maskSize p.val.2 + 4 = 4
  · simp only [hp, if_true]
    rfl
  · simp only [hp, if_false, zero_mul, Finset.sum_const_zero]

/-- Input Pythagoras is inherited from the genuine support projections.
No analogous output-orthogonality statement is assumed. -/
theorem selected_input_energy_le (z : V) (hn : 1 < Fintype.card V)
    (f : (Fin 4 → V) → ℝ) :
    (∑ p ∈ selectedSupport3, ∑ x, supportIndexComponent z p f x ^ 2) ≤
      ∑ x, f x ^ 2 := by
  calc
    (∑ p ∈ selectedSupport3, ∑ x, supportIndexComponent z p f x ^ 2)
        ≤ ∑ p : SupportIndex 3, ∑ x, supportIndexComponent z p f x ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selectedSupport3)
      intro p _ _
      exact Finset.sum_nonneg (fun x _ => sq_nonneg _)
    _ = ∑ x, degreeComponent z (3 : Fin 5) f x ^ 2 :=
      (supportIndex_degree_energy z hn (3 : Fin 5) f).symm
    _ ≤ ∑ x, f x ^ 2 := degreeComponent_energy_le z hn 3 f

theorem selected_sum_sq_le (a : SupportIndex 3 → ℝ) :
    (∑ p ∈ selectedSupport3, a p) ^ 2 ≤ 4 * ∑ p ∈ selectedSupport3, a p ^ 2 := by
  have hcount : (∑ _ ∈ selectedSupport3, (1 : ℝ) ^ 2) = (4 : ℝ) := by
    norm_num [selectedSupport3_card]
  calc
    (∑ p ∈ selectedSupport3, a p) ^ 2 =
        (∑ p ∈ selectedSupport3, (1 : ℝ) * a p) ^ 2 := by simp only [one_mul]
    _ ≤ (∑ _ ∈ selectedSupport3, (1 : ℝ) ^ 2) *
        ∑ p ∈ selectedSupport3, a p ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq selectedSupport3
        (fun _ : SupportIndex 3 => (1 : ℝ)) a
    _ = 4 * ∑ p ∈ selectedSupport3, a p ^ 2 := by rw [hcount]

end SelectedSupports

section ActualCap

theorem selected_piece_energy (p : SupportIndex 3) (hp : p ∈ selectedSupport3)
    (f : AES.WordState → ℝ) :
    (∑ y, action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y ^ 2) ≤
      (ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) *
        ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 := by
  obtain ⟨r, hm, hi⟩ := selectedSupport3_uniform_coordinate p hp
  exact word_nonzero_uniform_support_piece_energy p r 0 hm hi f

/-- Centering and output projection are already accounted for by the
physical source identity; the selected source projection is exactly `(3,4)`. -/
theorem physical_thirteen_twelve_action_sum (f : AES.WordState → ℝ) :
    action (physicalBlock 13 12) f =
      fun y => ∑ p ∈ selectedSupport3,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y := by
  rw [FourResidualStep.physical_thirteen_kernel, kernelCompose_action]
  change action residualStepKernel (action (refinedKernel (0 : AES.Word) 3 4) f) = _
  rw [refined_three_four_action_sum]
  exact action_finset_sum residualStepKernel selectedSupport3
    (fun p => supportIndexComponent (0 : AES.Word) p f)

theorem selected_output_energy (f : AES.WordState → ℝ) :
    (∑ y, (∑ p ∈ selectedSupport3,
      action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y) ^ 2) ≤
      (4 * ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) * ∑ x, f x ^ 2 := by
  calc
    (∑ y, (∑ p ∈ selectedSupport3,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y) ^ 2)
        ≤ ∑ y, 4 * ∑ p ∈ selectedSupport3,
          action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y ^ 2 :=
      Finset.sum_le_sum (fun y _ => selected_sum_sq_le (fun p =>
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y))
    _ = 4 * ∑ p ∈ selectedSupport3, ∑ y,
        action residualStepKernel (supportIndexComponent (0 : AES.Word) p f) y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 4 * ∑ p ∈ selectedSupport3,
        (ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) *
          ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
      apply Finset.sum_le_sum
      intro p hp
      exact selected_piece_energy p hp f
    _ = (4 * ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) *
        ∑ p ∈ selectedSupport3, ∑ x, supportIndexComponent (0 : AES.Word) p f x ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (4 * ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) * ∑ x, f x ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact selected_input_energy_le (0 : AES.Word)
        (by rw [AES.word_card]; norm_num) f

/-- Exact analytic coefficient, before comparison with the frozen cap. -/
theorem physical_thirteen_twelve_graph_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 12) f y ^ 2) ≤
      (4 * ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1)) * ∑ x, f x ^ 2 := by
  rw [physical_thirteen_twelve_action_sum]
  exact selected_output_energy f

/-- Exact rational square comparison, independent of the operator proof. -/
theorem second_cap_square_le :
    4 * ρ ^ 6 * κ * 65537 ^ 2 / (4294967296 - 1) ≤ (lambda * L 13 12) ^ 2 := by
  norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L]

theorem physical_thirteen_twelve_energy (f : AES.WordState → ℝ) :
    (∑ y, action (physicalBlock 13 12) f y ^ 2) ≤
      (lambda * L 13 12) ^ 2 * ∑ x, f x ^ 2 := by
  exact (physical_thirteen_twelve_graph_energy f).trans
    (mul_le_mul_of_nonneg_right second_cap_square_le
      (Finset.sum_nonneg (fun x _ => sq_nonneg (f x))))

/-- Physical-kernel norm cap. -/
theorem physical_thirteen_twelve_step_cap :
    ‖kernelOperator (physicalBlock 13 12)‖ ≤ lambda * L 13 12 :=
  kernelOperator_norm_le _
    (by norm_num [AESRound.Terminal.lambda, AESRound.Certificate.L])
    physical_thirteen_twelve_energy

theorem system_thirteen_twelve_step_cap :
    ‖PhysicalProjectionSystem.system.step 13 12‖ ≤ lambda * L 13 12 := by
  rw [PhysicalProjectionSystem.step_eq_physical]
  exact physical_thirteen_twelve_step_cap

end ActualCap
end AESConcrete.NonzeroUniformGraphCap
