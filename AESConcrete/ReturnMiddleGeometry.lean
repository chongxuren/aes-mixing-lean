import AESConcrete.NonzeroUniformGraphCap
import AESConcrete.FourierGraphSupport
import AESMixing.MDSInverse

/-!
# Normalized three-coordinate geometry for the direct return attempt

This file supplies coordinate identities, ordinary/Fourier graph uniqueness
and the exact mixed normalization only. Quantitative channel estimates belong
to ReturnMiddleEnergy. The physical indices remain Fin.removeNth/insertNth; no
projection is moved through wordMix. All three-coordinate functions are
arbitrary signed joint functions.

Constructive AES10/14/16 scope: independent uniform retained keys, whitening,
omitted final MixColumns and ordered-distinct reference.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ReturnMiddleGeometry
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.NonzeroUniformGraphCap
open AESConcrete.MDSGraphSupport (splitAt zero_slab_points_equal)
open AESConcrete.WordFourierCore (wordFourier wordPairing)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

section FiniteLeg
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- False selects the normalized zero vector; true selects full uniformity. -/
def leg (b : Bool) : V → ℝ := if b then fullUniform else zeroUnit

/-- The genuine counting-measure adjoint of rankOneLeg. -/
def extractLeg (v : V → ℝ) (r : Fin 4) (f : (Fin 4 → V) → ℝ)
    (w : Fin 3 → V) : ℝ :=
  ∑ t : V, v t * f (Fin.insertNth r t w)

/-- Raw MDS transfer between two normalized legs. Channel action is separate. -/
def middleInput (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (r s : Fin 4) (sourceFull targetFull : Bool)
    (h : (Fin 3 → V) → ℝ) : (Fin 3 → V) → ℝ :=
  extractLeg (leg targetFull) r
    (fun z => rankOneLeg s (leg sourceFull) h (L.symm z))

omit [AddCommGroup V] [DecidableEq V] in
theorem sum_insert (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    (∑ z, f z) = ∑ t : V, ∑ w : Fin 3 → V, f (Fin.insertNth r t w) := by
  have he := (splitAt (V := V) r).symm.sum_comp f
  change (∑ p : V × (Fin 3 → V), f (Fin.insertNth r p.1 p.2)) = ∑ z, f z at he
  rw [Fintype.sum_prod_type] at he
  exact he.symm

theorem leg_energy (hn : 1 < Fintype.card V) (b : Bool) :
    (∑ x : V, leg b x ^ 2) = 1 := by
  cases b
  · exact zeroUnit_energy
  · exact fullUniform_energy hn

theorem extractLeg_zero (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    extractLeg zeroUnit r f = fun w => f (Fin.insertNth r 0 w) := by
  funext w
  simp [extractLeg, zeroUnit, supportConstant, identityKernel]

omit [AddCommGroup V] [DecidableEq V] in
/-- Coisometry bound, proved by finite Cauchy--Schwarz before any MDS use. -/
theorem extractLeg_energy_le (v : V → ℝ) (hv : (∑ x, v x ^ 2) = 1)
    (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    (∑ w, extractLeg v r f w ^ 2) ≤ ∑ x, f x ^ 2 := by
  calc
    (∑ w, extractLeg v r f w ^ 2)
        ≤ ∑ w : Fin 3 → V, ∑ t : V, f (Fin.insertNth r t w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w _
      simpa only [extractLeg, hv, one_mul] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v
          (fun t => f (Fin.insertNth r t w))
    _ = ∑ x, f x ^ 2 := by
      rw [Finset.sum_comm]
      exact (sum_insert r (fun x => f x ^ 2)).symm

theorem middleInput_energy_le
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hn : 1 < Fintype.card V)
    (r s : Fin 4) (sourceFull targetFull : Bool) (h : (Fin 3 → V) → ℝ) :
    (∑ w, middleInput L r s sourceFull targetFull h w ^ 2) ≤ ∑ w, h w ^ 2 := by
  have he := extractLeg_energy_le (leg targetFull) (leg_energy hn targetFull) r
    (fun z => rankOneLeg s (leg sourceFull) h (L.symm z))
  have hp : (∑ z, rankOneLeg s (leg sourceFull) h (L.symm z) ^ 2) =
      ∑ z, rankOneLeg s (leg sourceFull) h z ^ 2 :=
    L.symm.toEquiv.sum_comp (fun z => rankOneLeg s (leg sourceFull) h z ^ 2)
  rw [hp, rankOneLeg_energy s (leg sourceFull) (leg_energy hn sourceFull) h] at he
  exact he

/-- Delete a physical output label after fixing a physical input label to zero. -/
def droppedMix (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (r s : Fin 4)
    (w : Fin 3 → V) : Fin 3 → V :=
  Fin.removeNth r (L (Fin.insertNth s 0 w))

omit [Fintype V] [DecidableEq V] in
theorem droppedMix_injective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L) (r s : Fin 4) :
    Function.Injective (droppedMix L r s) := by
  intro w w' he
  have hx := zero_slab_points_equal L.toAddMonoidHom hL s r
    (Fin.insertNth s 0 w) (Fin.insertNth s 0 w') (by simp) (by simp)
    (by
      intro i hi
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
      rw [← hj]
      exact congrFun he j)
  simpa only [Fin.removeNth_insertNth] using congrArg (Fin.removeNth s) hx

omit [DecidableEq V] in
theorem droppedMix_bijective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L) (r s : Fin 4) :
    Function.Bijective (droppedMix L r s) := by
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨droppedMix_injective L hL r s, rfl⟩

def droppedMixEquiv
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L) (r s : Fin 4) :
    (Fin 3 → V) ≃ (Fin 3 → V) :=
  Equiv.ofBijective (droppedMix L r s) (droppedMix_bijective L hL r s)

/-- The mixed zero-source/full-target average contains exactly one summand. -/
theorem zero_full_middle_formula
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (h : (Fin 3 → V) → ℝ) (w : Fin 3 → V) :
    middleInput L r s false true h w =
      (1 / Real.sqrt (Fintype.card V : ℝ)) *
        h ((droppedMixEquiv L hL r s).symm w) := by
  let e := droppedMixEquiv L hL r s
  let a : Fin 4 → V := Fin.insertNth s (0 : V) (e.symm w)
  let t := L a r
  have ha : Fin.removeNth r (L a) = w := e.apply_symm_apply w
  have hins : Fin.insertNth r t w = L a :=
    Fin.insertNth_eq_iff.mpr ⟨rfl, ha.symm⟩
  change (∑ v : V, fullUniform v *
      rankOneLeg s zeroUnit h (L.symm (Fin.insertNth r v w))) = _
  rw [Finset.sum_eq_single t]
  · rw [hins, L.symm_apply_apply]
    simp [rankOneLeg, zeroUnit, supportConstant, identityKernel, fullUniform, a, e]
  · intro v _ hvt
    have hvzero : L.symm (Fin.insertNth r v w) s ≠ 0 := by
      intro hv
      have heq := zero_slab_points_equal L.toAddMonoidHom hL s r
        (L.symm (Fin.insertNth r v w)) a hv (by simp [a])
        (by
          intro i hi
          change L (L.symm (Fin.insertNth r v w)) i = L a i
          rw [L.apply_symm_apply, ← hins]
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
          rw [← hj]
          simp)
      have hh := congrArg (fun x => L x r) heq
      apply hvt
      simpa only [L.apply_symm_apply, Fin.insertNth_apply_same] using hh
    simp [rankOneLeg, zeroUnit, supportConstant, identityKernel, hvzero]
  · simp

/-- The opposite mixed transfer is a normalized inverse complementary map. -/
theorem full_zero_middle_formula
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (r s : Fin 4)
    (h : (Fin 3 → V) → ℝ) :
    middleInput L r s true false h = fun w =>
      (1 / Real.sqrt (Fintype.card V : ℝ)) * h (droppedMix L.symm s r w) := by
  unfold middleInput
  change extractLeg zeroUnit r (fun z => rankOneLeg s fullUniform h (L.symm z)) = _
  rw [extractLeg_zero]
  rfl

/-- Fixed dependent retained label zero; the other two labels remain physical. -/
def Graph3 (g : (Fin 3 → V) → ℝ) : Prop :=
  ∀ w w', g w ≠ 0 → g w' ≠ 0 →
    (∀ i : Fin 3, i ≠ 0 → w i = w' i) → w = w'

theorem zero_zero_middle_graph
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (h : (Fin 3 → V) → ℝ) :
    Graph3 (middleInput L r s false false h) := by
  intro w w' hw hw' heq
  have hformula : middleInput L r s false false h = fun w =>
      rankOneLeg s zeroUnit h (L.symm (Fin.insertNth r 0 w)) := by
    unfold middleInput
    exact extractLeg_zero r _
  rw [hformula] at hw hw'
  have hz : ∀ x, rankOneLeg s zeroUnit h x ≠ 0 → x s = 0 :=
    zeroUnit_leg_zero_slab s h
  have hp := zero_slab_points_equal L.toAddMonoidHom hL s (r.succAbove 0)
    (L.symm (Fin.insertNth r 0 w)) (L.symm (Fin.insertNth r 0 w'))
    (hz _ hw) (hz _ hw') (by
      intro i hi
      change L (L.symm (Fin.insertNth r 0 w)) i =
        L (L.symm (Fin.insertNth r 0 w')) i
      rw [L.apply_symm_apply, L.apply_symm_apply]
      by_cases hir : i = r
      · subst i
        simp
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hir
        have hj0 : j ≠ 0 := by
          intro hj0
          exact hi (hj0 ▸ hj.symm)
        rw [← hj]
        simpa only [Fin.insertNth_apply_succAbove] using heq j hj0)
  have he := congrArg L hp
  rw [L.apply_symm_apply, L.apply_symm_apply] at he
  simpa only [Fin.removeNth_insertNth] using congrArg (Fin.removeNth r) he

end FiniteLeg

section ActualFourier

abbrev Word := AES.Word
abbrev Three := Fin 3 → Word

theorem fullUniform_word_value (x : Word) : fullUniform x = (1 / 65536 : ℝ) := by
  unfold fullUniform
  rw [AES.word_card]
  norm_num only [Nat.cast_ofNat]
  rw [show (4294967296 : ℝ) = 65536 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

theorem wordFourier_zero_row (x : Word) : wordFourier 0 x = fullUniform x := by
  rw [WordFourierCore.wordFourier_coefficient, WordFourierCore.wordPairing.zero_left,
    fullUniform_word_value]

/-- Product Fourier restriction has the exact unit normalization; no q factor. -/
theorem fourier_extract_full (r : Fin 4) (f : AES.WordState → ℝ) (xi : Three) :
    action (coordinateKernel (fun _ : Fin 3 => wordFourier))
      (extractLeg fullUniform r f) xi =
    action (coordinateKernel (fun _ : Fin 4 => wordFourier)) f
      (Fin.insertNth r 0 xi) := by
  have hprod (t : Word) (w : Three) :
      coordinateKernel (fun _ : Fin 4 => wordFourier)
        (Fin.insertNth r 0 xi) (Fin.insertNth r t w) =
      fullUniform t * coordinateKernel (fun _ : Fin 3 => wordFourier) xi w := by
    change (∏ i : Fin 4, wordFourier
      ((Fin.insertNth r (0 : Word) xi : Fin 4 → Word) i)
      ((Fin.insertNth r t w : Fin 4 → Word) i)) =
      fullUniform t * ∏ i : Fin 3, wordFourier (xi i) (w i)
    rw [Fin.prod_univ_succAbove
      (fun i : Fin 4 => wordFourier
        ((Fin.insertNth r (0 : Word) xi : Fin 4 → Word) i)
        ((Fin.insertNth r t w : Fin 4 → Word) i)) r]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      wordFourier_zero_row]
  unfold action
  rw [sum_insert r]
  simp_rw [hprod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  unfold extractLeg
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem full_full_middle_fourier_graph (r s : Fin 4) (h : Three → ℝ) :
    Graph3 (action (coordinateKernel (fun _ : Fin 3 => wordFourier))
      (middleInput wordMixAddEquiv r s true true h)) := by
  intro w w' hw hw' heq
  let f := rankOneLeg s (fullUniform : Word → ℝ) h
  have hform (xi : Three) :
      action (coordinateKernel (fun _ : Fin 3 => wordFourier))
        (middleInput wordMixAddEquiv r s true true h) xi =
      action (coordinateKernel (fun _ : Fin 4 => wordFourier))
        (fun z => f (wordMixAddEquiv.symm z)) (Fin.insertNth r 0 xi) :=
    fourier_extract_full r (fun z => f (wordMixAddEquiv.symm z)) xi
  rw [hform] at hw hw'
  have hcoord := FourierGraphSupport.uniform_pullback_fourier_support_coordinate_eq
    WordFourierCore.wordPairing word_add_self wordMixAddEquiv wordMixAddEquiv_zeroMDS
    s (r.succAbove 0) f (fullUniform_leg_invariant s h)
    (Fin.insertNth r 0 w) (Fin.insertNth r 0 w')
    (by simpa only [productPairing_fourier, WordFourierCore.wordFourier] using hw)
    (by simpa only [productPairing_fourier, WordFourierCore.wordFourier] using hw') (by
      intro i hi
      by_cases hir : i = r
      · subst i
        simp
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hir
        have hj0 : j ≠ 0 := by
          intro hj0
          exact hi (hj0 ▸ hj.symm)
        rw [← hj]
        simpa only [Fin.insertNth_apply_succAbove] using heq j hj0)
  have hzero : w 0 = w' 0 := by
    simpa only [Fin.insertNth_apply_succAbove] using hcoord
  funext i
  by_cases hi : i = 0
  · subst i
    exact hzero
  · exact heq i hi

theorem zero_full_middle_energy (r s : Fin 4) (h : Three → ℝ) :
    (∑ w, middleInput wordMixAddEquiv r s false true h w ^ 2) =
      (1 / 4294967296 : ℝ) * ∑ w, h w ^ 2 := by
  have hform (w : Three) : middleInput wordMixAddEquiv r s false true h w =
      (1 / 65536 : ℝ) *
        h ((droppedMixEquiv wordMixAddEquiv wordMixAddEquiv_zeroMDS r s).symm w) := by
    have he := zero_full_middle_formula
      wordMixAddEquiv wordMixAddEquiv_zeroMDS r s h w
    change middleInput wordMixAddEquiv r s false true h w =
      fullUniform (0 : Word) *
        h ((droppedMixEquiv wordMixAddEquiv wordMixAddEquiv_zeroMDS r s).symm w) at he
    simpa only [fullUniform_word_value] using he
  simp_rw [hform, mul_pow]
  rw [← Finset.mul_sum,
    (droppedMixEquiv wordMixAddEquiv wordMixAddEquiv_zeroMDS r s).symm.sum_comp
      (fun w => h w ^ 2)]
  norm_num

theorem full_zero_middle_energy (r s : Fin 4) (h : Three → ℝ) :
    (∑ w, middleInput wordMixAddEquiv r s true false h w ^ 2) =
      (1 / 4294967296 : ℝ) * ∑ w, h w ^ 2 := by
  rw [full_zero_middle_formula]
  have hinv := zeroMDS_inverse wordMixAddEquiv wordMixAddEquiv_zeroMDS
  have he : (∑ w, h (droppedMix wordMixAddEquiv.symm s r w) ^ 2) =
      ∑ w, h w ^ 2 :=
    (droppedMixEquiv wordMixAddEquiv.symm hinv s r).sum_comp (fun w => h w ^ 2)
  change (∑ w, (fullUniform (0 : Word) *
      h (droppedMix wordMixAddEquiv.symm s r w)) ^ 2) = _
  simp_rw [fullUniform_word_value, mul_pow]
  rw [← Finset.mul_sum, he]
  norm_num

end ActualFourier
end AESConcrete.ReturnMiddleGeometry
