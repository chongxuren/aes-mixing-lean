import AESConcrete.LineOverlap

/-!
# Exact three-coordinate plane spike enumerator

For a finite 65536-point coordinate code, each coordinate-zero fiber has
256 points.  If two distinct coordinate zeros force the distinguished zero
point, the nonzero points have exactly the weighted enumerator used here.
The proof is a pointwise polynomial identity followed by exact fiber sums.

These are explicit structural hypotheses, not an asserted AES geometry fact.
Actual plane instantiation and analytic containment bounds are separate.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.PlaneWeightEnumerator
open AESMixing
open AESConcrete.ByteGramCore (Byte)

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C]

def spikeProduct (d g : ℝ) (c : C → Fin 3 → Byte) (x : C) : ℝ :=
  ∏ i : Fin 3, if c x i = 0 then d else g

theorem spikeProduct_zero (d g : ℝ) (c : C → Fin 3 → Byte)
    (c0 : C) (hc0 : c c0 = 0) : spikeProduct d g c c0 = d^3 := by
  simp [spikeProduct, hc0]

/-- Away from c0 there is at most one zero coordinate.  This gives an
identity over all points by correcting the all-zero point separately. -/
theorem spikeProduct_polynomial (d g : ℝ) (c : C → Fin 3 → Byte)
    (c0 : C) (hc0 : c c0 = 0)
    (htwo : ∀ x i j, i ≠ j → c x i = 0 → c x j = 0 → x = c0) (x : C) :
    spikeProduct d g c x =
      g^3 + (∑ i : Fin 3, if c x i = 0 then d*g^2-g^3 else 0) +
        (if x = c0 then d^3-3*d*g^2+2*g^3 else 0) := by
  classical
  by_cases hx : x = c0
  · subst x
    simp [spikeProduct, hc0, Fin.sum_univ_succ]
    ring
  have hn (i j : Fin 3) (hij : i ≠ j) (hi : c x i = 0) (hj : c x j = 0) : False :=
    hx (htwo x i j hij hi hj)
  by_cases h0 : c x 0 = 0
  · have h1 : c x 1 ≠ 0 := fun h => hn 0 1 (by decide) h0 h
    have h2 : c x 2 ≠ 0 := fun h => hn 0 2 (by decide) h0 h
    simp [spikeProduct, Fin.prod_univ_succ, Fin.sum_univ_succ, h0, h1, h2, hx]
    ring_nf <;> simp
  by_cases h1 : c x 1 = 0
  · have h2 : c x 2 ≠ 0 := fun h => hn 1 2 (by decide) h1 h
    simp [spikeProduct, Fin.prod_univ_succ, Fin.sum_univ_succ, h0, h1, h2, hx]
    ring
  by_cases h2 : c x 2 = 0
  · simp [spikeProduct, Fin.prod_univ_succ, Fin.sum_univ_succ, h0, h1, h2, hx]
    ring
  · simp [spikeProduct, Fin.prod_univ_succ, Fin.sum_univ_succ, h0, h1, h2, hx]
    ring

/-- A fiber cardinality is used as a sum multiplicity, without enumerating
the finite code points. -/
theorem coordinate_zero_indicator_sum (c : C → Fin 3 → Byte)
    (hfiber : ∀ i, Fintype.card {x : C // c x i = 0} = 256)
    (i : Fin 3) (a : ℝ) :
    (∑ x : C, if c x i = 0 then a else 0) = 256*a := by
  classical
  have hc : (Finset.univ.filter (fun x : C => c x i = 0)).card = 256 := by
    simpa only [Fintype.card_subtype] using hfiber i
  rw [← Finset.sum_filter, Finset.sum_const, hc]
  simp [nsmul_eq_mul]

/-- Exact full plane spike sum, including its distinguished zero point. -/
theorem plane_spike_sum (d g : ℝ) (c : C → Fin 3 → Byte)
    (c0 : C) (hc0 : c c0 = 0) (hcard : Fintype.card C = 65536)
    (hfiber : ∀ i, Fintype.card {x : C // c x i = 0} = 256)
    (htwo : ∀ x i j, i ≠ j → c x i = 0 → c x j = 0 → x = c0) :
    (∑ x : C, spikeProduct d g c x) = d^3 + 3*255*d*g^2 + 255*254*g^3 := by
  classical
  simp_rw [spikeProduct_polynomial d g c c0 hc0 htwo, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp_rw [coordinate_zero_indicator_sum c hfiber]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    hcard, Fintype.card_fin, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num
  ring

/-- Exact nonzero plane spike sum: 3*255 points have one zero coordinate,
and 255*254 points have no zero coordinate.  There are no nonzero two-zero
points under the stated structural hypotheses. -/
theorem plane_nonzero_spike_sum (d g : ℝ) (c : C → Fin 3 → Byte)
    (c0 : C) (hc0 : c c0 = 0) (hcard : Fintype.card C = 65536)
    (hfiber : ∀ i, Fintype.card {x : C // c x i = 0} = 256)
    (htwo : ∀ x i j, i ≠ j → c x i = 0 → c x j = 0 → x = c0) :
    (∑ x : {x : C // x ≠ c0}, spikeProduct d g c x.val) =
      3*255*d*g^2 + 255*254*g^3 := by
  classical
  have hs := Fintype.sum_eq_add_sum_subtype_ne (fun x : C => spikeProduct d g c x) c0
  rw [plane_spike_sum d g c c0 hc0 hcard hfiber htwo,
    spikeProduct_zero d g c c0 hc0] at hs
  linarith

end AESConcrete.PlaneWeightEnumerator
