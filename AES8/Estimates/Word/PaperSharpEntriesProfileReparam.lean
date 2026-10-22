import AES8.Estimates.Word.PaperSharpEntriesReduction
import AESConcrete.ByteGramFourier

/-!
# Reparametrize actual affine opposite-side profile moments

The generic calculation retains the field-scalar relation between two physical
coordinates and the additive AES byte output map. Numerical pair predicates,
channel/profile shape equalities, and final graph entry bounds have separate
roles. No concrete sharp cap is assumed as an entry resource. Constructive only.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperSharpEntriesProfileReparam
set_option autoImplicit false

section Generic
variable {F : Type*} [Field F] [Fintype F]

def PairCap (rho : F → ℝ) (B : F ≃+ F) (r s : ℕ) (H : ℝ) : Prop :=
  ∀ alpha beta gamma : F, alpha ≠ 0 → beta ≠ 0 →
    (∑ u : F, rho u ^ r * rho (alpha * B (beta * u) + gamma) ^ s) ≤ H

def HomogeneousPairCap (rho : F → ℝ) (B : F ≃+ F) (r s : ℕ) (H : ℝ) : Prop :=
  ∀ alpha beta : F, alpha ≠ 0 → beta ≠ 0 →
    (∑ u : F, rho u ^ r * rho (alpha * B (beta * u)) ^ s) ≤ H

def pairBeta (B : F ≃+ F) (b m n : F) : F := n / (B b * m)

def pairGamma (B : F ≃+ F) (a b m n d e : F) : F :=
  a * B (e - pairBeta B b m n * (B b * d))

theorem map_ne_zero (B : F ≃+ F) (b : F) (hb : b ≠ 0) : B b ≠ 0 := by
  intro hz
  exact hb (B.injective (hz.trans (map_zero B).symm))

theorem pairBeta_ne_zero (B : F ≃+ F) (b m n : F)
    (hb : b ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) : pairBeta B b m n ≠ 0 :=
  div_ne_zero hn (mul_ne_zero (map_ne_zero B b hb) hm)

/-- Literal row/column profile transport on an affine physical section.
The output/input slopes and offsets are retained until the common finite
mixed-pair predicate is applied. -/
theorem affine_pair_sum_eq (B : F ≃+ F) (rho : F → ℝ) (C : F → F → ℝ)
    (hrow : ∀ b v, b ≠ 0 → C b v = rho (B b * v))
    (hcol : ∀ a v, a ≠ 0 → C v a = rho (a * B v))
    (a b m n d e : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (r s : ℕ) :
    (∑ v : F, C b (m * v + d) ^ r * C (n * v + e) a ^ s) =
      ∑ u : F, rho u ^ r *
        rho (a * B (pairBeta B b m n * u) + pairGamma B a b m n d e) ^ s := by
  let delta : F := B b * m
  let epsilon : F := B b * d
  have hdelta : delta ≠ 0 := mul_ne_zero (map_ne_zero B b hb) hm
  let param : F ≃ F := (Equiv.mulLeft₀ delta hdelta).trans (Equiv.addRight epsilon)
  have hbeta : pairBeta B b m n * delta = n :=
    div_mul_cancel₀ n hdelta
  have hargument (v : F) :
      pairBeta B b m n * param v +
        (e - pairBeta B b m n * epsilon) = n * v + e := by
    change pairBeta B b m n * (delta * v + epsilon) +
      (e - pairBeta B b m n * epsilon) = _
    calc
      _ = (pairBeta B b m n * delta) * v + e := by ring
      _ = _ := by rw [hbeta]
  have hpoint (v : F) :
      C b (m * v + d) ^ r * C (n * v + e) a ^ s =
        rho (param v) ^ r *
          rho (a * B (pairBeta B b m n * param v) + pairGamma B a b m n d e) ^ s := by
    rw [hrow b _ hb, hcol a _ ha]
    have hfirst : B b * (m * v + d) = param v := by
      change B b * (m * v + d) = (B b * m) * v + B b * d
      ring
    have hsecond : a * B (n * v + e) =
        a * B (pairBeta B b m n * param v) + pairGamma B a b m n d e := by
      rw [← hargument v, map_add, mul_add]
      rfl
    rw [hfirst, hsecond]
  calc
    _ = ∑ v : F, rho (param v) ^ r *
        rho (a * B (pairBeta B b m n * param v) + pairGamma B a b m n d e) ^ s :=
      Finset.sum_congr rfl (fun v _ => hpoint v)
    _ = _ := param.sum_comp (fun u => rho u ^ r *
      rho (a * B (pairBeta B b m n * u) + pairGamma B a b m n d e) ^ s)

theorem affine_pair_sum_le (B : F ≃+ F) (rho : F → ℝ) (C : F → F → ℝ)
    (hrow : ∀ b v, b ≠ 0 → C b v = rho (B b * v))
    (hcol : ∀ a v, a ≠ 0 → C v a = rho (a * B v))
    (a b m n d e : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (hn : n ≠ 0) (r s : ℕ) (H : ℝ)
    (hcap : PairCap rho B r s H) :
    (∑ v : F, C b (m * v + d) ^ r * C (n * v + e) a ^ s) ≤ H := by
  rw [affine_pair_sum_eq B rho C hrow hcol a b m n d e ha hb hm r s]
  exact hcap a (pairBeta B b m n) (pairGamma B a b m n d e) ha
    (pairBeta_ne_zero B b m n hb hm hn)

theorem homogeneous_pair_sum_le (B : F ≃+ F) (rho : F → ℝ) (C : F → F → ℝ)
    (hrow : ∀ b v, b ≠ 0 → C b v = rho (B b * v))
    (hcol : ∀ a v, a ≠ 0 → C v a = rho (a * B v))
    (a b m n : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm : m ≠ 0) (hn : n ≠ 0) (r s : ℕ) (H : ℝ)
    (hcap : HomogeneousPairCap rho B r s H) :
    (∑ v : F, C b (m * v) ^ r * C (n * v) a ^ s) ≤ H := by
  have he := affine_pair_sum_eq B rho C hrow hcol a b m n 0 0 ha hb hm r s
  simp only [add_zero, pairGamma, mul_zero, sub_zero, map_zero] at he
  rw [he]
  exact hcap a (pairBeta B b m n) ha (pairBeta_ne_zero B b m n hb hm hn)

end Generic
end AES8.PaperSharpEntriesProfileReparam
