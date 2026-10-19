import AESPaper.FourSourceConvolution
import AESPaper.ManySourceBounds

/-!
# Actual marginal atom bounds with several active sources
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.ConvolutionAtom
open AESMixing AESConcrete
open AESPaper.CenteredConvolution AESPaper.FourSourceConvolution

section Generic
variable {V : Type*} [Fintype V] [AddCommGroup V]

theorem atom_le_of_collisions (f g : V → ℝ) (rho : ℝ) (hr : 0 ≤ rho)
    (hf : (∑ x, f x^2) ≤ rho) (hg : (∑ x, g x^2) ≤ rho) (y : V) :
    convolution f g y ≤ rho := by
  have h := (convolution_atom_sq_le f g y).trans
    (mul_le_mul hf hg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hr)
  nlinarith [sq_nonneg (convolution f g y-rho)]

theorem convolution_cap_right (f g : V → ℝ) (rho : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hm : (∑ x, f x) = 1) (hg : ∀ x, g x ≤ rho) (y : V) :
    convolution f g y ≤ rho := by
  calc
    _ ≤ ∑ x, f x * rho :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hg (y-x)) (hf x))
    _ = rho := by rw [← Finset.sum_mul, hm, one_mul]

theorem convolution_cap_left (f g : V → ℝ) (rho : ℝ)
    (hg : ∀ x, 0 ≤ g x) (hm : (∑ x, g x) = 1) (hf : ∀ x, f x ≤ rho) (y : V) :
    convolution f g y ≤ rho := by
  rw [convolution_comm f g]
  exact convolution_cap_right g f rho hg hm hf y

theorem collision_le_left (f g : V → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hm : (∑ x, g x) = 1) :
    (∑ y, convolution f g y^2) ≤ ∑ y, f y^2 := by
  rw [convolution_comm f g]
  exact convolution_collision_le g f hg hm

/-- The mark only identifies a source with the collision cap. -/
theorem fourfold_atom_le (f : Fin 4 → V → ℝ) (b : Fin 4 → Bool)
    (rho : ℝ) (hr : 0 ≤ rho) (hn : ∀ i x, 0 ≤ f i x)
    (hm : ∀ i, (∑ x, f i x) = 1)
    (he : ∀ i, b i = true → (∑ x, f i x^2) ≤ rho)
    (hb : 2 ≤ residualDegree b) (y : V) : fourfold f y ≤ rho := by
  let p := convolution (f 0) (f 1)
  let q := convolution (f 2) (f 3)
  have hpn : ∀ x, 0 ≤ p x := convolution_nonnegative _ _ (hn 0) (hn 1)
  have hqn : ∀ x, 0 ≤ q x := convolution_nonnegative _ _ (hn 2) (hn 3)
  have hpm : (∑ x, p x) = 1 := convolution_unit_mass _ _ (hm 0) (hm 1)
  have hqm : (∑ x, q x) = 1 := convolution_unit_mass _ _ (hm 2) (hm 3)
  have hpe (h : b 0 = true ∨ b 1 = true) : (∑ x, p x^2) ≤ rho := by
    rcases h with h0 | h1
    · exact (collision_le_left _ _ (hn 1) (hm 1)).trans (he 0 h0)
    · exact (convolution_collision_le _ _ (hn 0) (hm 0)).trans (he 1 h1)
  have hqe (h : b 2 = true ∨ b 3 = true) : (∑ x, q x^2) ≤ rho := by
    rcases h with h2 | h3
    · exact (collision_le_left _ _ (hn 3) (hm 3)).trans (he 2 h2)
    · exact (convolution_collision_le _ _ (hn 2) (hm 2)).trans (he 3 h3)
  change convolution p q y ≤ rho
  rcases two_marked_pair_cases b hb with h01 | h23 | hcross
  · exact convolution_cap_left p q rho hqn hqm
      (atom_le_of_collisions _ _ rho hr (he 0 h01.1) (he 1 h01.2)) y
  · exact convolution_cap_right p q rho hpn hpm
      (atom_le_of_collisions _ _ rho hr (he 2 h23.1) (he 3 h23.2)) y
  · exact atom_le_of_collisions p q rho hr (hpe hcross.1) (hqe hcross.2) y
end Generic

open AESPaper.StartingWord (q)
open AESPaper.ManySourceLaw AESPaper.ManySourceBounds

theorem actual_marginal_atom_le (b : AES.State) (hb : 2 ≤ activeSourceCount b)
    (c : Fin 4) (y : AES.Word) :
    wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c y ≤ 6/(5*q) := by
  rw [boundary_marginal]
  exact fourfold_atom_le (transportedSource b c) (activeSourceMask b)
    (6/(5*q)) (by norm_num [q]) (transportedSource_nonnegative b c)
    (transportedSource_mass b c)
    (fun i hi => (transportedSource_collision_lt_six_fifths b c i
      ((activeSourceMask_iff b i).mp hi)).le) hb y

theorem actual_marginal_nonnegative (b : AES.State) (c : Fin 4) (y : AES.Word) :
    0 ≤ wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c y := by
  rw [boundary_marginal]
  exact fourfold_nonnegative (transportedSource b c) (transportedSource_nonnegative b c) y

theorem actual_marginal_mass (b : AES.State) (c : Fin 4) :
    (∑ y, wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c y) = 1 := by
  rw [boundary_marginal]
  exact fourfold_mass (transportedSource b c) (transportedSource_mass b c)

/-- The actual one-word zero event has probability below 2/q. -/
theorem actual_zero_probability_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b)
    (c : Fin 4) :
    wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c 0 < 2/q := by
  apply (actual_marginal_atom_le b hb c 0).trans_lt
  norm_num [q]

end AESPaper.ConvolutionAtom
