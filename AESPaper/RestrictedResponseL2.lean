import AESPaper.UniversalRestrictedResponse
import AESMixing.L2Sums

/-!
# Restricted responses indexed by zero sets
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace AESPaper.RestrictedResponseL2
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q)
open AESPaper.WordDamping (nu)
open AESPaper.WordRestrictedResponse (residual)
open AESPaper.ManySourceBounds (activeSourceCount)
open AESConcrete.RestrictedMarginalEnergy (marginal)

def setMarginal (b : AES.State) (D : Finset (Fin 4)) (out : Fin 16) :
    (MaskCoordinates out → AES.Word) → ℝ :=
  marginal (fun x (i : MaskCoordinates out) => x i.val)
    (fun x : AES.WordState => if ∀ i ∈ D, x i=0 then BiasStartup.inputLaw b x else 0)

def setResponse (b : AES.State) (D : Finset (Fin 4)) (out : Fin 16) :
    (MaskCoordinates out → AES.Word) → ℝ :=
  action (coordinateKernel (fun _ : MaskCoordinates out => residual)) (setMarginal b D out)

theorem setMarginal_eq_mask (b : AES.State) (D : Finset (Fin 4)) (r out : Fin 16)
    (hr : ∀ i, maskBit r i=true ↔ i ∈ D) :
    setMarginal b D out = ActualRestrictedSource.markedMarginal b r out (fun _ => True) := by
  unfold setMarginal ActualRestrictedSource.markedMarginal
    ActualRestrictedSource.markedCoordinates
  apply congrArg (marginal
    (fun (x : AES.WordState) (i : MaskCoordinates out) => x i.val))
  funext x
  have he : (∀ i ∈ D, x i=0) ↔ (∀ i, maskBit r i=true → x i=0) := by
    constructor
    · exact fun h i hi => h i ((hr i).mp hi)
    · exact fun h i hi => h i ((hr i).mpr hi)
  simp only [ActualRestrictedSource.boundaryRestriction, and_true, he]

theorem setResponse_eq_zero (b : AES.State) (hb : 0 < activeSourceCount b)
    (D : Finset (Fin 4)) (out : Fin 16) (hD : activeSourceCount b ≤ D.card) :
    setResponse b D out = 0 := by
  obtain ⟨r,hr,hsize⟩ := ActualZeroEvents.set_mask_exists D
  unfold setResponse
  rw [setMarginal_eq_mask b D r out hr]
  exact ActualRestrictedWordResponse.actual_response_eq_zero b hb r out (by omega) (fun _ => True)

theorem nu_le_one : nu ≤ 1 := by norm_num [nu]

theorem nu_pow_le (a m : ℕ) (h : m ≤ a) : nu^a ≤ nu^m := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have hn : nu^n ≤ 1 := pow_le_one₀ WordDamping.nu_nonnegative nu_le_one
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn
    (pow_nonneg WordDamping.nu_nonnegative m)

/-- An actual nonempty residual set always pays one contraction; impossible
zero events have already vanished. -/
theorem setResponse_norm_le (b : AES.State) (hb : 0 < activeSourceCount b)
    (D : Finset (Fin 4)) (out : Fin 16)
    (hdis : ∀ i ∈ D, maskBit out i=false) (hj : 0 < maskSize out) :
    l2 (setResponse b D out) ≤
      (6/5 : ℝ)^2 * 20^D.card * nu / (q^D.card * Real.sqrt (q^maskSize out)) := by
  by_cases hD : activeSourceCount b ≤ D.card
  · rw [setResponse_eq_zero b hb D out hD]
    have hnu := WordDamping.nu_nonnegative
    have hq := ResponseScalarBounds.q_positive
    simp only [l2, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  · obtain ⟨r,hr,hsize⟩ := ActualZeroEvents.set_mask_exists D
    have hro : MaskDisjoint r out := by
      intro i hi ho
      have hz := hdis i ((hr i).mp hi)
      simp only [hz, Bool.false_eq_true] at ho
    have h := UniversalRestrictedResponse.response_norm_le b hb r out hro (fun _ => True)
    have he : l2 (setResponse b D out) =
        Real.sqrt (UniversalRestrictedResponse.responseEnergy b r out (fun _ => True)) := by
      unfold setResponse
      rw [setMarginal_eq_mask b D r out hr]
      rfl
    rw [he]
    apply h.trans
    have ha : 1 ≤ min (activeSourceCount b-maskSize r) (maskSize out) := by omega
    have hnu : nu^(min (activeSourceCount b-maskSize r) (maskSize out)) ≤ nu := by
      simpa only [pow_one] using nu_pow_le _ 1 ha
    rw [hsize] at hnu ⊢
    apply div_le_div_of_nonneg_right _
      (mul_nonneg (pow_nonneg ResponseScalarBounds.q_positive.le _)
        (Real.sqrt_nonneg _))
    exact mul_le_mul_of_nonneg_left hnu (by positivity)

/-- With no prescribed zeros, two active sources and two residual outputs
supply two contractions. -/
theorem empty_response_norm_le (b : AES.State) (hb : 2 ≤ activeSourceCount b)
    (out : Fin 16) (hj : 2 ≤ maskSize out) :
    l2 (setResponse b ∅ out) ≤ (6/5 : ℝ)^2*nu^2/Real.sqrt (q^maskSize out) := by
  have hz : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
  have hsize : maskSize (0 : Fin 16) = 0 := by decide
  have hr : MaskDisjoint 0 out := by
    intro i hi
    simp only [hz i, Bool.false_eq_true] at hi
  have hmask : ∀ i : Fin 4, maskBit (0 : Fin 16) i = true ↔ i ∈ (∅ : Finset (Fin 4)) := by
    intro i
    simp [hz i]
  have he : l2 (setResponse b ∅ out) =
      Real.sqrt (UniversalRestrictedResponse.responseEnergy b 0 out (fun _ => True)) := by
    unfold setResponse
    rw [setMarginal_eq_mask b ∅ 0 out hmask]
    rfl
  rw [he]
  have h := UniversalRestrictedResponse.response_norm_le b (by omega) 0 out hr (fun _ => True)
  simp only [hsize, Nat.sub_zero, pow_zero, mul_one, one_mul] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left (nu_pow_le _ 2 (by omega)) (by positivity)

end AESPaper.RestrictedResponseL2
