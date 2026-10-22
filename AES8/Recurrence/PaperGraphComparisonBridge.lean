import AES8.Recurrence.PaperComparisonPowers
import AES8.Reductions.Return.PaperAESIncidence
import AES8.Reductions.Return.PaperAESOverlapBound
import AES8.Reductions.Return.PaperAESOverlapHS

/-! Exact scalar interface between the physical incidence/overlap bounds and
rational certificates. This file does not assume or prove a grouped-state norm
bound. It only identifies the coefficients after multiplying by Q^3. -/
noncomputable section
namespace AES8.PaperGraphComparisonBridge
open AES8.PaperComparison AES8.PaperComparisonPowers

private theorem rpow_mul (x a b : ℝ) (hx : 0 < x) :
    Real.rpow x a * Real.rpow x b = Real.rpow x (a+b) :=
  (Real.rpow_add hx a b).symm

private theorem resources :
    AES8.PaperAESIncidence.nu = (C : ℝ)/(sqrtQ : ℝ) ∧
    AES8.PaperAESOverlapResources.nu = (C : ℝ)/(sqrtQ : ℝ) ∧
    AES8.PaperWordMixedGram.delta = (E : ℝ)^2/(q : ℝ) ∧
    AES8.PaperAESOverlapResources.delta = (E : ℝ)^2/(q : ℝ) ∧
    AES8.PaperAESOverlapResources.total = (H : ℝ)^2/(q : ℝ) := by
  norm_num [AES8.PaperAESIncidence.nu, AES8.PaperAESOverlapResources.nu,
    AES8.PaperWordMixedGram.delta, AES8.PaperAESOverlapResources.delta,
    AES8.PaperAESOverlapResources.total, AES8.PaperAESOverlapResources.q,
    C, E, H, q, sqrtQ]

/-- The exact two physical incidence factors with the Q^3 certificate scaling. -/
theorem incidence_product (i j c s t : ℕ) :
    (q : ℝ)^3 * AES8.PaperAESIncidence.leftFactor i c s *
      AES8.PaperAESIncidence.rightFactor j c t =
    Real.rpow (q : ℝ) (((i : ℝ)+j+2*c-2-min i s-min j t)/2) *
      ((C : ℝ)/(sqrtQ : ℝ))^min i s *
      Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)-min i s)/2) := by
  have hq : (0 : ℝ) < (q : ℝ) := by norm_num [q]
  unfold AES8.PaperAESIncidence.leftFactor AES8.PaperAESIncidence.rightFactor
  rw [resources.1, resources.2.2.1]
  simp only [Nat.min_comm]
  change (q : ℝ)^3 *
    (Real.rpow (q : ℝ) (((i : ℝ)+c-4-min i s)/2) *
      (((C : ℝ)/(sqrtQ : ℝ))^min i s *
        Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)-min i s)/2))) *
    Real.rpow (q : ℝ) (((j : ℝ)+c-4-min j t)/2) = _
  have hpow : (q : ℝ)^3 = Real.rpow (q : ℝ) (3 : ℝ) := by
    exact (Real.rpow_natCast (q : ℝ) 3).symm
  rw [hpow]
  have hz : 3+(((i : ℝ)+c-4-min i s)/2)+(((j : ℝ)+c-4-min j t)/2) =
      ((i : ℝ)+j+2*c-2-min i s-min j t)/2 := by ring
  calc
    _ = (Real.rpow (q : ℝ) 3 *
        Real.rpow (q : ℝ) (((i : ℝ)+c-4-min i s)/2) *
        Real.rpow (q : ℝ) (((j : ℝ)+c-4-min j t)/2)) *
        ((C : ℝ)/(sqrtQ : ℝ))^min i s *
        Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)-min i s)/2) := by ring
    _ = _ := by rw [rpow_mul _ _ _ hq, rpow_mul _ _ _ hq, hz]

/-- Q^3 times the actual large-overlap coefficient equals its rational entry. -/
theorem large_product (i j c s t : ℕ) (hc : c ≤ s+t)
    (hs : s ≤ c) (ht : t ≤ c)
    (hm : s-min i s ≤ c-s) (hn : t-min j t ≤ c-t) :
    (q : ℝ)^3 * AES8.PaperAESIncidence.leftFactor i c s *
      AES8.PaperAESIncidence.rightFactor j c t *
      AES8.PaperAESOverlapBound.paperCoefficient c s t (s-min i s) (t-min j t) =
    (overlapLarge i j c s t (min i s) (min j t) (s-min i s) (t-min j t) : ℝ) := by
  let r := min i s
  let z := min j t
  let m := s-r
  let n := t-z
  rw [incidence_product]
  unfold AES8.PaperAESOverlapBound.paperCoefficient
  rw [resources.2.1, resources.2.2.2.1, resources.2.2.2.2]
  have hq : (AES8.PaperAESOverlapResources.q : ℝ) = (q : ℝ) := by norm_num [AES8.PaperAESOverlapResources.q,q]
  rw [hq]
  have hδ : (0 : ℝ) < (E : ℝ)^2/(q : ℝ) := by norm_num [E,q]
  have hp : r+(s+t-c) = r+s+t-c := by omega
  have hd : (((i : ℝ)-r)/2)+((c : ℝ)-((s+t+m+n : ℕ) : ℝ)/2) =
      ((i : ℝ)-r+2*c-s-t-m-n)/2 := by push_cast; ring
  have hh : (H : ℝ)^2/(q : ℝ)/(q : ℝ) = (H : ℝ)^2/(q : ℝ)^2 := by ring
  have heq := largeCoefficient_eq i j c s t r z m n (Nat.min_le_left _ _) hc hs ht hm hn
  rw [overlapLarge, Nat.min_eq_right hm, Nat.min_eq_right hn]
  rw [← heq]
  unfold largeCoefficient
  change _ = Real.rpow (q : ℝ) (((i : ℝ)+j+2*c-2-r-z)/2) *
    ((C : ℝ)/(sqrtQ : ℝ))^(r+s+t-c) *
    Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)-r+2*c-s-t-m-n)/2) *
    Real.rpow ((H : ℝ)^2/(q : ℝ)^2) (((m : ℝ)+n)/2)
  rw [hh]
  simp only [Nat.cast_add]
  calc
    _ = Real.rpow (q : ℝ) (((i : ℝ)+j+2*c-2-r-z)/2) *
      (((C : ℝ)/(sqrtQ : ℝ))^r * ((C : ℝ)/(sqrtQ : ℝ))^(s+t-c)) *
      (Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)-r)/2) *
       Real.rpow ((E : ℝ)^2/(q : ℝ)) ((c : ℝ)-((s : ℝ)+t+m+n)/2)) *
      Real.rpow ((H : ℝ)^2/(q : ℝ)^2) (((m : ℝ)+n)/2) := by dsimp [r,z,m,n]; ring
    _ = _ := by
      push_cast at hd
      rw [← pow_add, hp, rpow_mul _ _ _ hδ, hd]

/-- Exact coefficient join for the equal-Fourier HS branch; this does not
supply the separately required pointwise entry bound. -/
theorem hs_product (i j c s t : ℕ) (hs : s ≤ c) (ht : t ≤ c) :
    (q : ℝ)^3 * AES8.PaperAESIncidence.leftFactor i c s *
      AES8.PaperAESIncidence.rightFactor j c t *
      AES8.PaperAESOverlapHS.coefficient c s t
        AES8.PaperAESOverlapResources.entry AES8.PaperAESOverlapResources.delta
        AES8.PaperAESOverlapResources.total =
    (overlapHS i j c s t (min i s) (min j t) : ℝ) := by
  rw [overlapHS_eq _ _ _ _ _ _ _ (Nat.min_le_left _ _) hs ht]
  rw [incidence_product]
  unfold AES8.PaperAESOverlapHS.coefficient hsCoefficient
  rw [resources.2.2.2.1, resources.2.2.2.2]
  have hentry : AES8.PaperAESOverlapResources.entry = 27/(q : ℝ) := by
    norm_num [AES8.PaperAESOverlapResources.entry,AES8.PaperAESOverlapResources.q,q]
  rw [hentry]
  have hlo : min s t ≤ max s t := le_trans (Nat.min_le_left s t) (Nat.le_max_left s t)
  rw [Nat.cast_sub hlo]
  have hδ : (0 : ℝ) < (E : ℝ)^2/(q : ℝ) := by norm_num [E,q]
  have hd : (((i : ℝ)-min i s)/2)+(((max s t : ℕ) : ℝ)-min s t)/2 =
      ((i : ℝ)-min i s+max s t-min s t)/2 := by ring
  calc
    _ = Real.rpow (q : ℝ) (((i : ℝ)+j+2*c-2-min i s-min j t)/2) *
      ((C : ℝ)/(sqrtQ : ℝ))^min i s *
      (Real.rpow ((E : ℝ)^2/(q : ℝ)) (((i : ℝ)-min i s)/2) *
        Real.rpow ((E : ℝ)^2/(q : ℝ)) ((((max s t : ℕ) : ℝ)-min s t)/2)) *
      Real.rpow ((H : ℝ)^2/(q : ℝ)) (((min s t : ℕ) : ℝ)/2) *
      (27/(q : ℝ))^(c-max s t) := by ring
    _ = _ := by rw [rpow_mul _ _ _ hδ, hd]

end AES8.PaperGraphComparisonBridge
