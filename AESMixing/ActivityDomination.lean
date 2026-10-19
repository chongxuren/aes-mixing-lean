import AESMixing.ActivitySpan
import AESMixing.GramCertificate

/-! A small Gram certificate controls every degree-zero input. The proof
uses the spanning identity, so it is not restricted to a product input law
or to the sixteen basis vectors separately. Numerical certificates remain
separate obligations. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

theorem degree_diffuse_activity_expansion
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (j : Fin 5) (f : (Fin 4 → V) → ℝ)
    (x : Fin 4 → V) :
    degreeComponent 0 j (fun y => degreeComponent 0 0 f (L.symm y)) x =
      ∑ a : Fin 16, degreeComponent 0 j (diffusedActivityColumn L a) x * activityCoefficient a f := by
  simp_rw [← degreeKernel_action]
  rw [degreeKernel_action 0 0 f, degree_zero_reconstruction]
  unfold action
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [diffusedActivityColumn, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem activity_transfer_from_gram_certificate {K : Type*} [Fintype K]
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (j : Fin 5)
    (S : K → Fin 16 → ℝ) (d : K → ℝ) (c : ℝ)
    (hd : ∀ k, 0 ≤ d k)
    (hc : ∀ a b, c^2 * (Fintype.card V : ℝ)^AES.maskSize (maskIntersection a b) -
        gram (fun y a => degreeComponent 0 j (diffusedActivityColumn L a) y) a b =
      ∑ k, d k * S k a * S k b)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, degreeComponent 0 j (fun x => degreeComponent 0 0 f (L.symm x)) y^2) ≤
      c^2 * ∑ y, degreeComponent 0 0 f y^2 := by
  have he := gram_domination_from_certificate
    (fun y a => activityColumn (V := V) a y)
    (fun y a => degreeComponent 0 j (diffusedActivityColumn L a) y)
    S d c hd (fun a b => by rw [activity_gram]; exact hc a b)
    (fun a => activityCoefficient a f)
  simp_rw [degree_diffuse_activity_expansion]
  simpa only [degree_zero_reconstruction] using he

end AESMixing
