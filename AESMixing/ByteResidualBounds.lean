import AESMixing.SupportNorm
import AESMixing.SupportDegreeDecomposition
import AESMixing.SupportComparison
import AESMixing.ByteIncidenceFormula
import AESMixing.OrthogonalComparison
import AESMixing.DegreeBilinear

/-! Residual-to-residual degree bounds on a byte alphabet. They apply to
the actual four-coordinate MDS diffusion and arbitrary joint inputs.
The only geometric premise is the already formalized MDS zero condition. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit maskSize)

theorem supportNormFactor_byte {j : ℕ} (p : SupportIndex j) :
    supportNormFactor (BinaryWord 8) p.val.2 p.val.1 =
      Real.sqrt (255^(supportIndexSize p).val) := by
  have he : 4-(maskSize p.val.2+maskSize p.val.1) = (supportIndexSize p).val := by
    have hj := p.property.2
    simp only [supportIndexSize]
    omega
  unfold supportNormFactor
  rw [he]
  norm_num only [BinaryWord.card,Nat.reducePow,Nat.cast_ofNat]

theorem byte_support_comparison_coefficient (i j : Fin 5)
    (p : SupportIndex i.val) (q : SupportIndex j.val) :
    shorteningNormSum 256 p.val.2 q.val.2
      (unmarkedGraphPositions p.val.2 q.val.2 p.val.1 q.val.1) p.val.1 q.val.1 /
        (supportNormFactor (BinaryWord 8) p.val.2 p.val.1 *
          supportNormFactor (BinaryWord 8) q.val.2 q.val.1) =
      supportIncidenceComparison i j p q := by
  rw [byte_shorteningNormSum p.val.2 q.val.2 p.val.1 q.val.1 p.property.1 q.property.1,
    p.property.2,q.property.2,← supportIndexSize_eq p,← supportIndexSize_eq q,
    supportNormFactor_byte p,supportNormFactor_byte q]
  simp only [supportIncidenceComparison,supportDiagonal]
  simp only [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),Real.sqrt_one]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem byte_support_bilinear
    (L : (Fin 4 → BinaryWord 8) →+ (Fin 4 → BinaryWord 8)) (hL : ZeroMDS L)
    (i j : Fin 5) (hj : 0 < j.val) (p : SupportIndex i.val) (q : SupportIndex j.val)
    (f g : (Fin 4 → BinaryWord 8) → ℝ) :
    |∑ x, supportIndexComponent 0 p g (L x)*supportIndexComponent 0 q f x| ≤
      supportIncidenceComparison i j p q*l2 (supportIndexComponent 0 q f)*
        l2 (supportIndexComponent 0 p g) := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have hcard : 0 < Fintype.card (MaskCoordinates q.val.1) := by
    rw [maskCoordinates_card,q.property.2]
    exact hj
  obtain ⟨k⟩ := Fintype.card_pos_iff.mp hcard
  have h := supportProduct_diffusion_bilinear L hL hn p.val.2 q.val.2 p.val.1 q.val.1
    p.property.1 q.property.1 k f g
  norm_num only [BinaryWord.card,Nat.reducePow,Nat.cast_ofNat] at h
  rw [byte_support_comparison_coefficient i j p q] at h
  exact h

theorem byte_residual_degree_bilinear
    (L : (Fin 4 → BinaryWord 8) →+ (Fin 4 → BinaryWord 8)) (hL : ZeroMDS L)
    (i j : Fin 5) (hj : 0 < j.val) (c : ℝ) (hc : 0 ≤ c)
    (hC : ∀ v : SupportIndex j.val → ℝ,
      (∑ p, action (supportIncidenceComparison i j) v p^2) ≤ c^2*∑ q, v q^2)
    (f g : (Fin 4 → BinaryWord 8) → ℝ) :
    |∑ x, degreeComponent 0 i g (L x)*degreeComponent 0 j f x| ≤
      c*l2 (degreeComponent 0 j f)*l2 (degreeComponent 0 i g) := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have h := orthogonal_bilinear_comparison
    (fun q : SupportIndex j.val => supportIndexComponent 0 q f)
    (fun p : SupportIndex i.val => supportIndexComponent 0 p g) L
    (fun p q hpq => supportIndex_orthogonal 0 hn p q hpq f f)
    (fun p q hpq => supportIndex_orthogonal 0 hn p q hpq g g)
    (supportIncidenceComparison i j) c hc hC
    (fun p q => byte_support_bilinear L hL i j hj p q f g)
  simpa only [congrFun (supportIndex_decomposition 0 j f),
    congrFun (supportIndex_decomposition 0 i g),supportIndex_decomposition] using h

theorem byte_residual_degree_energy
    (L : (Fin 4 → BinaryWord 8) ≃+ (Fin 4 → BinaryWord 8)) (hL : ZeroMDS L)
    (i j : Fin 5) (hj : 0 < j.val) (c : ℝ) (hc : 0 ≤ c)
    (hC : ∀ v : SupportIndex j.val → ℝ,
      (∑ p, action (supportIncidenceComparison i j) v p^2) ≤ c^2*∑ q, v q^2)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 i j L.toEquiv f x^2) ≤ c^2*∑ x, degreeComponent 0 j f x^2 := by
  apply degreeTransfer_energy_of_bilinear 0 (by norm_num [BinaryWord.card]) i j L.toEquiv c hc
  exact byte_residual_degree_bilinear L.toAddMonoidHom hL i j hj c hc hC

theorem byte_residual_11_energy
    (L : (Fin 4 → BinaryWord 8) ≃+ (Fin 4 → BinaryWord 8)) (hL : ZeroMDS L)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 1 1 L.toEquiv f x^2) ≤
      (27/8000 : ℝ)^2*∑ x, degreeComponent 0 1 f x^2 :=
  byte_residual_degree_energy L hL 1 1 (by decide) (27/8000) (by norm_num)
    support_comparison_11_energy f

theorem byte_residual_12_energy
    (L : (Fin 4 → BinaryWord 8) ≃+ (Fin 4 → BinaryWord 8)) (hL : ZeroMDS L)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 1 2 L.toEquiv f x^2) ≤
      (43/500 : ℝ)^2*∑ x, degreeComponent 0 2 f x^2 :=
  byte_residual_degree_energy L hL 1 2 (by decide) (43/500) (by norm_num)
    support_comparison_12_energy f

theorem byte_residual_22_energy
    (L : (Fin 4 → BinaryWord 8) ≃+ (Fin 4 → BinaryWord 8)) (hL : ZeroMDS L)
    (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 2 2 L.toEquiv f x^2) ≤
      (9/10 : ℝ)^2*∑ x, degreeComponent 0 2 f x^2 :=
  byte_residual_degree_energy L hL 2 2 (by decide) (9/10) (by norm_num)
    support_comparison_22_energy f

end AESMixing
