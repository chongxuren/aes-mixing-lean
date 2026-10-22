import AES8.Estimates.Byte.PaperMixedCodeMoment
import AESConcrete.ActualMarkedCodeDual

/-!
# Marked-code energy from the printed byte Gram upper bound

Module role: supply the primal and dual marked-code energy inequalities.
Physical projections, code/image identities and adjoint orientations are reused
unchanged; the quantitative byte premise enters only through the owned
PaperMixedCodeMoment bound-bearing endpoints. No legacy actual code-energy
bound is invoked. Source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperMarkedCodeEnergy
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.MarkedBlockVectorization (Marked Activity markedLeg)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.ActualMarkedCodeMoment
  (Byte markedOrientation actual_markedLeg marked_projection_bijective)
open AESConcrete.ActualMarkedCodeDual
  (markedCode normalized_source_eq_code actual_dual_projection_bijective)
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000

section Energy
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Actual low-dimensional marked-code bound; no information-set premise remains. -/
theorem actual_normalized_low_energy_le (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (idx : CodePosition I J ≃ Marked m)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card I = 4) :
    (∑ y : Marked m → Byte,
      MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
        (sourceCoordinates (byteDiffusionHom inverse) m s) y^2) ≤
      (MixedCodeMoment.byteMoment / 256)^Fintype.card I * MixedCodeMoment.byteDelta^Fintype.card J := by
  rw [actual_markedLeg]
  apply AES8.PaperMixedCodeMoment.actual_normalizedResponse_energy_le
    (markedOrientation left right m) (sourceCoordinates (byteDiffusionHom inverse) m s) idx
  · apply marked_projection_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      m s (fun i : I => idx (Sum.inl i)) _ hsize
    intro i j h
    exact Sum.inl.inj (idx.injective h)
  · apply marked_projection_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      m s (fun i : I => idx (Sum.inr (Sum.inl i))) _ hsize
    intro i j h
    exact Sum.inl.inj (Sum.inr.inj (idx.injective h))


/-- Actual high-dimensional branch with no assumed dual information set. -/
theorem actual_normalized_high_energy_le (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool) (idx : CodePosition I J ≃ Marked m)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      (Fintype.card (Marked m)-Fintype.card I) = 4) :
    (∑ y : Marked m → Byte,
      MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
        (sourceCoordinates (byteDiffusionHom inverse) m s) y^2) ≤
      (MixedCodeMoment.byteMoment / 256)^Fintype.card I * MixedCodeMoment.byteDelta^Fintype.card J := by
  have hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m) := by omega
  rw [actual_markedLeg, normalized_source_eq_code inverse m s hhigh]
  apply AES8.PaperMixedCodeMoment.actual_subgroup_energy_dual_le (markedOrientation left right m)
    (markedCode inverse m s) idx
  · apply actual_dual_projection_bijective inverse m s (fun i : I => idx (Sum.inl i)) _ hsize
    intro i j h
    exact Sum.inl.inj (idx.injective h)
  · apply actual_dual_projection_bijective inverse m s (fun i : I => idx (Sum.inr (Sum.inl i))) _ hsize
    intro i j h
    exact Sum.inl.inj (Sum.inr.inj (idx.injective h))

/-- Both actual branches in the requested min(d,ell-d) form. -/
theorem actual_normalized_energy_min (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool) (idx : CodePosition I J ≃ Marked m)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) (hI : Fintype.card I = min d (ell-d)) :
    (∑ y : Marked m → Byte,
      MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
        (sourceCoordinates (byteDiffusionHom inverse) m s) y^2) ≤
      (MixedCodeMoment.byteMoment / 256)^min d (ell-d) *
        MixedCodeMoment.byteDelta^(ell-2*min d (ell-d)) := by
  have hc := Fintype.card_congr idx
  simp only [CodePosition, Fintype.card_sum] at hc
  have hJ : Fintype.card J = ell-2*min d (ell-d) := by omega
  have hb :
      (∑ y : Marked m → Byte,
        MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
          (sourceCoordinates (byteDiffusionHom inverse) m s) y^2) ≤
        (MixedCodeMoment.byteMoment / 256)^Fintype.card I * MixedCodeMoment.byteDelta^Fintype.card J := by
    by_cases hd : d ≤ ell-d
    · have hm : min d (ell-d) = d := min_eq_left hd
      exact actual_normalized_low_energy_le left right inverse m s idx (by omega)
    · have hm : min d (ell-d) = ell-d := min_eq_right (by omega)
      exact actual_normalized_high_energy_le left right inverse m s idx (by omega)
  simpa only [hI, hJ] using hb

end Energy

/-- The physical leg partition exists by finite cardinality; the actual
MDS projection proofs, rather than that cardinality, establish its information sets. -/
theorem actual_normalized_energy_bound (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d ell : ℕ) (hlen : Fintype.card (Marked m) = ell)
    (hdim : maskSize (outputZeros m s) + maskSize (inputZeros m s) + d = 4)
    (hdle : d ≤ ell) :
    (∑ y : Marked m → Byte,
      MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
        (sourceCoordinates (byteDiffusionHom inverse) m s) y^2) ≤
      (MixedCodeMoment.byteMoment / 256)^min d (ell-d) *
        MixedCodeMoment.byteDelta^(ell-2*min d (ell-d)) := by
  let dstar := min d (ell-d)
  let rest := ell-2*dstar
  have htwo : 2*dstar ≤ ell := by
    have hl := min_le_left d (ell-d)
    have hr := min_le_right d (ell-d)
    dsimp only [dstar]
    omega
  let idx : CodePosition (Fin dstar) (Fin rest) ≃ Marked m :=
    Fintype.equivOfCardEq (by
      simp only [CodePosition, Fintype.card_sum, Fintype.card_fin]
      rw [hlen]
      dsimp only [rest]
      omega)
  exact actual_normalized_energy_min left right inverse m s idx d ell hlen hdim hdle
    (by simp only [Fintype.card_fin, dstar])


#print axioms actual_normalized_low_energy_le
#print axioms actual_normalized_high_energy_le
#print axioms actual_normalized_energy_min
#print axioms actual_normalized_energy_bound
end AES8.PaperMarkedCodeEnergy
