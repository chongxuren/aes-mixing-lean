import AESConcrete.ActualMarkedContractionEnergy
import AESConcrete.WordMomentNumbers

/-!
# Exact scalar ceilings for the unsigned marked-block row bounds

These six evaluations use the source's closed-form survivor counts. They
do not identify any AES block with those expressions. The degree-three
signed overlap bound and its all-pattern applicability remain separate.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
namespace AESConcrete.MarkedMomentNumbers

abbrev zeta := ActualMarkedContractionEnergy.zeta

def unsignedCap : ℕ → ℝ
  | 2 => 20*(256/255)^6 * zeta 2 1 * (1+9*(1/16)^2+9*(1/16)^4+(1/16)^6)
  | 4 => (256/255)^4 *
      (8*zeta 4 1*((1+1/16)^4-1/16-(1/16)^3) +
       6*zeta 4 2*((1+1/16)^4-2*(1/16)^2))
  | 5 => (1-1/16)^(-3:ℤ) * (2*zeta 5 1+6*zeta 5 2)
  | 6 => (1-1/16)^(-2:ℤ) * (2*zeta 6 2+2*zeta 6 3)
  | 7 => 2*(1-1/16)^(-1:ℤ) * zeta 7 3
  | 8 => zeta 8 4
  | _ => 0

theorem zeta_nonneg (ell d : ℕ) : 0 ≤ zeta ell d := by
  unfold zeta ActualMarkedContractionEnergy.zeta MixedCodeMoment.byteMoment MixedCodeMoment.byteDelta
  positivity

theorem unsigned_two_lt : unsignedCap 2 < WordMomentNumbers.markedCap 2 := by
  norm_num [unsignedCap, zeta, ActualMarkedContractionEnergy.zeta, MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta,
    WordMomentNumbers.markedCap]

theorem unsigned_four_lt : unsignedCap 4 < WordMomentNumbers.markedCap 4 := by
  norm_num [unsignedCap, zeta, ActualMarkedContractionEnergy.zeta, MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta,
    WordMomentNumbers.markedCap]

theorem unsigned_five_lt : unsignedCap 5 < WordMomentNumbers.markedCap 5 := by
  norm_num [unsignedCap, zeta, ActualMarkedContractionEnergy.zeta, MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta,
    WordMomentNumbers.markedCap]

theorem unsigned_six_lt : unsignedCap 6 < WordMomentNumbers.markedCap 6 := by
  norm_num [unsignedCap, zeta, ActualMarkedContractionEnergy.zeta, MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta,
    WordMomentNumbers.markedCap]

theorem unsigned_seven_lt : unsignedCap 7 < WordMomentNumbers.markedCap 7 := by
  norm_num [unsignedCap, zeta, ActualMarkedContractionEnergy.zeta, MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta,
    WordMomentNumbers.markedCap]

theorem unsigned_eight_lt : unsignedCap 8 < WordMomentNumbers.markedCap 8 := by
  norm_num [unsignedCap, zeta, ActualMarkedContractionEnergy.zeta, MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta,
    WordMomentNumbers.markedCap]

end AESConcrete.MarkedMomentNumbers
