import AESConcrete.ActualRestrictedMarginalBound
import AESConcrete.RestrictedZeroEvents
import AESConcrete.ColumnSupportResponse
import AESConcrete.ColumnSupportAggregation

/-!
# Actual positive-degree column components

The physical support projection is identified with a restricted response,
bounded by the actual restricted-marginal theorem, and normalized by its
constant nonzero coordinates. Impossible zero patterns have zero source
mass and hence zero response. No component-energy premise remains.
-/

noncomputable section
set_option maxRecDepth 100000
open scoped BigOperators
namespace AESConcrete.ActualPositiveColumnDegrees
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordColumnGram (Byte Word tensorResponse)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.ActualRestrictedDensity (restrictedSource)
open AESConcrete.RestrictedSourcePushforward (fullOutputCoordinates fullWordSource)
open AESConcrete.ColumnSupportResponse (nonzeroOutside)

theorem forbidden_response_zero (left right : Orientation) (inverse : Bool) (a : Word)
    (ha0 : a ≠ 0) (r z out : Fin 16) (hhigh : 4 ≤ maskSize r + maskSize z)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : Word → Prop) [DecidablePred event] :
    tensorResponse (fun _ : MaskCoordinates out => residualMatrix (channel left) 0)
      (fullOutputCoordinates inverse out) (fullWordSource right inverse a r event) = 0 := by
  have hm := RestrictedZeroEvents.actual_restricted_mass_zero right inverse a ha0 r z hhigh
    (fun c => event c.val)
  have hz (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
      restrictedSource right inverse a r z (fun c => event c.val) c = 0 := by
    have hn := ActualRestrictedDensity.restrictedSource_nonneg right inverse a r z (fun c => event c.val) c
    have hl : restrictedSource right inverse a r z (fun c => event c.val) c ≤
        ∑ c : ShortenedGraph (byteDiffusionHom inverse) r z,
          restrictedSource right inverse a r z (fun c => event c.val) c :=
      Finset.single_le_sum (fun c _ =>
        ActualRestrictedDensity.restrictedSource_nonneg right inverse a r z (fun c => event c.val) c)
        (Finset.mem_univ c)
    rw [hm] at hl
    exact le_antisymm hl hn
  rw [← RestrictedSourcePushforward.shortened_tensorResponse_eq_full right inverse a r z ha event]
  funext y
  simp only [tensorResponse,hz,mul_zero,Finset.sum_const_zero,Pi.zero_apply]

theorem support_component_energy_le (left right : Orientation) (inverse : Bool) (a : Word)
    (ha0 : a ≠ 0) (z : Fin 16) (t : ℕ) (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (r out : Fin 16) (hr : MaskDisjoint r out) :
    (∑ y : Word, action (supportProduct (0 : Byte) (maskBit out) (maskBit r))
      (fun v => wordKernel left right inverse v a) y^2) ≤
      ColumnSupportAggregation.supportCap t (maskSize r) (maskSize out) := by
  rw [ColumnSupportResponse.column_support_energy left right inverse a r out hr]
  by_cases hrt : maskSize r < t
  · have hshort : maskSize r + maskSize z ≤ 4 := by omega
    have h := ActualRestrictedMarginalBound.full_response_energy right inverse a r z out hr hshort ha
      (nonzeroOutside inverse r) (fun _ => left)
    have hd : 4-maskSize r-maskSize z = t-maskSize r := by omega
    rw [hd] at h
    calc
      _ ≤ (((1 : ℝ)/64)^(2*maskSize r) *
          (((65 : ℝ)/8192)*((9 : ℝ)/128)^2)^(min (t-maskSize r) (maskSize out)) *
            ((8383 : ℝ)/2088960)^(maskSize out-min (t-maskSize r) (maskSize out))) /
              255^(4-(maskSize r+maskSize out)) :=
        div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by
        simp only [ColumnSupportAggregation.supportCap,if_pos hrt,
          MultibyteColumnNumbers.atom,MultibyteColumnNumbers.rho,
          MultibyteColumnNumbers.nu,MultibyteColumnNumbers.delta]
        ring
  · rw [forbidden_response_zero left right inverse a ha0 r z out (by omega) ha
      (nonzeroOutside inverse r)]
    simp only [Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_div,
      ColumnSupportAggregation.supportCap,if_neg hrt,le_refl]

theorem positive_degree_energy_le (left right : Orientation) (inverse : Bool) (a : Word)
    (ha0 : a ≠ 0) (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (j : Fin 5) (hj : 1 ≤ j.val) :
    (∑ y : Word, degreeComponent (0 : Byte) j (fun v => wordKernel left right inverse v a) y^2) ≤
      MultibyteColumnNumbers.degreeCap t j.val := by
  apply ColumnSupportAggregation.positive_degree_energy_le t ht j hj
  intro p
  have h := support_component_energy_le left right inverse a ha0 z t hcount ha
    p.val.2 p.val.1 p.property.1
  simpa only [supportIndexComponent,p.property.2] using h

end AESConcrete.ActualPositiveColumnDegrees
