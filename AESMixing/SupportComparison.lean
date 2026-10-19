import AESMixing.SupportIndex
import AESMixing.IncidenceComparisonEnergy

/-! Lift the rational support-size certificates to every orthogonal
support component. Repeated sizes contribute their exact binomial
multiplicities; no equality of the individual diffusion blocks is assumed. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def supportDiagonal {j : ℕ} (p : SupportIndex j) : ℝ :=
  1/255^(supportIndexSize p).val

def supportIncidenceComparison (i j : Fin 5) (p : SupportIndex i.val)
    (q : SupportIndex j.val) : ℝ :=
  Real.sqrt (supportDiagonal p) *
    (incidenceSupportRaw i.val j.val ((supportIndexSize p).val+i.val)
      ((supportIndexSize q).val+j.val) : ℝ) * Real.sqrt (supportDiagonal q)

theorem supportIndex_weighted_sum (i j : Fin 5) (a : Fin (5-i.val))
    (v : Fin (5-j.val) → ℚ) :
    (∑ q : SupportIndex j.val,
      (incidenceSupportRaw i.val j.val (a.val+i.val) ((supportIndexSize q).val+j.val) : ℝ) *
        supportDiagonal q * (v (supportIndexSize q) : ℝ)) =
      ((∑ b, incidenceSupportRaw i.val j.val (a.val+i.val) (b.val+j.val) *
        incidenceSupportWeight j.val (b.val+j.val) * v b : ℚ) : ℝ) := by
  unfold supportDiagonal
  rw [supportIndex_sum_by_size j (fun b =>
    (incidenceSupportRaw i.val j.val (a.val+i.val) (b.val+j.val) : ℝ) *
      (1/255^b.val) * (v b : ℝ))]
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [incidenceSupportWeight,Nat.add_sub_cancel,Rat.cast_mul,Rat.cast_div,
    Rat.cast_natCast,Nat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  ring

theorem support_incidence_comparison_energy (i j : Fin 5)
    (u : Fin (5-i.val) → ℚ) (v : Fin (5-j.val) → ℚ) (c : ℚ)
    (hc : 0 ≤ c) (hu : ∀ a, 0 < u a) (hv : ∀ b, 0 < v b)
    (hrow : ∀ a, (∑ b, incidenceSupportRaw i.val j.val (a.val+i.val) (b.val+j.val) *
      incidenceSupportWeight j.val (b.val+j.val) * v b) ≤ c*u a)
    (hcol : ∀ b, (∑ a, incidenceSupportRaw i.val j.val (a.val+i.val) (b.val+j.val) *
      incidenceSupportWeight i.val (a.val+i.val) * u a) ≤ c*v b)
    (f : SupportIndex j.val → ℝ) :
    (∑ p, action (supportIncidenceComparison i j) f p^2) ≤ (c : ℝ)^2 * ∑ q, f q^2 := by
  apply diagonal_comparison_energy _ supportDiagonal supportDiagonal
    (fun p => (u (supportIndexSize p) : ℝ)) (fun q => (v (supportIndexSize q) : ℝ))
    (c : ℝ) (by exact_mod_cast hc)
  · intro p q
    exact_mod_cast incidenceSupportRaw_nonneg i.val j.val
      ((supportIndexSize p).val+i.val) ((supportIndexSize q).val+j.val)
  · intro p
    unfold supportDiagonal
    positivity
  · intro q
    unfold supportDiagonal
    positivity
  · intro p
    exact_mod_cast hu (supportIndexSize p)
  · intro q
    exact_mod_cast hv (supportIndexSize q)
  · intro p
    rw [supportIndex_weighted_sum i j (supportIndexSize p) v]
    simpa only [Rat.cast_mul] using (Rat.cast_le (K := ℝ)).mpr (hrow (supportIndexSize p))
  · intro q
    simp_rw [incidenceSupportRaw_symm i.val j.val]
    rw [supportIndex_weighted_sum j i (supportIndexSize q) u]
    have h := (Rat.cast_le (K := ℝ)).mpr (hcol (supportIndexSize q))
    simpa only [Rat.cast_mul,incidenceSupportRaw_symm j.val i.val] using h

theorem support_comparison_11_energy (f : SupportIndex 1 → ℝ) :
    (∑ p, action (supportIncidenceComparison 1 1) f p^2) ≤ (27/8000 : ℝ)^2 * ∑ q, f q^2 := by
  have h := support_incidence_comparison_energy 1 1 incidenceWitness11 incidenceWitness11 (27/8000)
    (by norm_num) incidence_witnesses_positive.1 incidence_witnesses_positive.1
    (fun a => le_of_lt (incidence_comparison_11_rows a))
    (fun b => by
      change (∑ a : Fin 4, incidenceSupportRaw 1 1 (a.val+1) (b.val+1) *
        incidenceSupportWeight 1 (a.val+1) * incidenceWitness11 a) ≤
          (27/8000)*incidenceWitness11 b
      simp_rw [incidenceSupportRaw_symm 1 1 _ (b.val+1)]
      exact le_of_lt (incidence_comparison_11_rows b)) f
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h ⊢
  exact h

theorem support_comparison_12_energy (f : SupportIndex 2 → ℝ) :
    (∑ p, action (supportIncidenceComparison 1 2) f p^2) ≤ (43/500 : ℝ)^2 * ∑ q, f q^2 := by
  have h := support_incidence_comparison_energy 1 2 incidenceWitness12Out incidenceWitness12In (43/500)
    (by norm_num) incidence_witnesses_positive.2.1 incidence_witnesses_positive.2.2.1
    (fun a => le_of_lt (incidence_comparison_12_rows a))
    (fun b => le_of_lt (incidence_comparison_12_columns b)) f
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h ⊢
  exact h

theorem support_comparison_22_energy (f : SupportIndex 2 → ℝ) :
    (∑ p, action (supportIncidenceComparison 2 2) f p^2) ≤ (9/10 : ℝ)^2 * ∑ q, f q^2 := by
  have h := support_incidence_comparison_energy 2 2 incidenceWitness22 incidenceWitness22 (9/10)
    (by norm_num) incidence_witnesses_positive.2.2.2 incidence_witnesses_positive.2.2.2
    (fun a => le_of_lt (incidence_comparison_22_rows a))
    (fun b => by
      change (∑ a : Fin 3, incidenceSupportRaw 2 2 (a.val+2) (b.val+2) *
        incidenceSupportWeight 2 (a.val+2) * incidenceWitness22 a) ≤
          (9/10)*incidenceWitness22 b
      simp_rw [incidenceSupportRaw_symm 2 2 _ (b.val+2)]
      exact le_of_lt (incidence_comparison_22_rows b)) f
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h ⊢
  exact h

end AESMixing
