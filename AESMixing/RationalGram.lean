import AESMixing.GramCertificate
import Mathlib.Data.Rat.BigOperators

/-! Transfer exact rational weighted-square certificates to the real Gram
quadratic form. The hypotheses still require the actual input/output Gram
entries; this bridge does not give invented matrices an AES interpretation. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem rational_weighted_square_cast {I K : Type*} [Fintype K]
    (G H : I → I → ℚ) (S : K → I → ℚ) (d : K → ℚ) (c : ℚ)
    (h : ∀ i j, c^2 * G i j - H i j = ∑ k, d k * S k i * S k j) (i j : I) :
    (c : ℝ)^2 * (G i j : ℝ) - (H i j : ℝ) =
      ∑ k, (d k : ℝ) * (S k i : ℝ) * (S k j : ℝ) := by
  have he := congrArg (fun x : ℚ => (x : ℝ)) (h i j)
  push_cast at he
  exact he

theorem rational_gram_domination {I K A B : Type*}
    [Fintype I] [Fintype K] [Fintype A] [Fintype B]
    (input : A → I → ℝ) (output : B → I → ℝ)
    (G H : I → I → ℚ) (S : K → I → ℚ) (d : K → ℚ) (c : ℚ)
    (hG : ∀ i j, gram input i j = (G i j : ℝ))
    (hH : ∀ i j, gram output i j = (H i j : ℝ))
    (hd : ∀ k, 0 ≤ d k)
    (hc : ∀ i j, c^2 * G i j - H i j = ∑ k, d k * S k i * S k j)
    (x : I → ℝ) :
    (∑ b, (∑ i, output b i * x i)^2) ≤
      (c : ℝ)^2 * ∑ a, (∑ i, input a i * x i)^2 := by
  apply gram_domination_from_certificate input output
    (fun k i => (S k i : ℝ)) (fun k => (d k : ℝ)) (c : ℝ) ?_ ?_ x
  · intro k
    exact_mod_cast hd k
  · intro i j
    rw [hG, hH]
    exact rational_weighted_square_cast G H S d c hc i j

end AESMixing
