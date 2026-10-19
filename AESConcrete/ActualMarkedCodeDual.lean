import AESConcrete.ActualMarkedCodeMoment
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual marked image codes and their trace-character dual information sets

The image subgroup is constructed from the actual shortened graph. Its
unit source is identified through an actual source/image equivalence.
Complementary primal information sets transfer to the actual annihilator
through the trace pairing. This supplies both branches of the mixed code
moment bound with no assumed information-set or scalar moment resource.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualMarkedCodeDual
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.MarkedBlockVectorization (Marked Activity markedLeg)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.ActualMarkedCodeMoment
  (Byte marked_remaining marked_projection_bijective selected_projection_injective
    markedOrientation actual_markedLeg actual_normalized_low_energy_le)
attribute [local instance] Classical.propDecidable

-- Actual byte-field/source coercions require deeper reduction when the
-- normalized enumerator is reindexed to its image subgroup.
set_option maxRecDepth 100000

section Selection
variable {A K V : Type*} [Fintype A] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V]

def selectionRange (p : A → K) (k : K) : Prop := ∃ a, p a = k

def selectionEquiv (p : A → K) (hp : Function.Injective p) :
    A ≃ {k : K // selectionRange p k} :=
  Equiv.ofBijective (fun a => ⟨p a, a, rfl⟩)
    ⟨fun _ _ h => hp (congrArg Subtype.val h), by
      rintro ⟨k,a,ha⟩
      exact ⟨a, Subtype.ext ha⟩⟩

theorem selection_complement_card (p : A → K) (hp : Function.Injective p) :
    Fintype.card {k : K // ¬ selectionRange p k} = Fintype.card K - Fintype.card A := by
  rw [Fintype.card_subtype_compl, ← Fintype.card_congr (selectionEquiv p hp)]

/-- Complementary actual primal restriction implies the selected dual restriction. -/
theorem dual_projection_bijective_of_complement (B : CharacterPairing V)
    (C : AddSubgroup (K → V)) [Fintype C] (p : A → K) (hp : Function.Injective p)
    (hc : Function.Bijective (subgroupRestriction C (fun k => ¬ selectionRange p k))) :
    Function.Bijective (fun w : (B.product K).annihilator C => fun a : A => w.val (p a)) := by
  let E : A ≃ {k : K // ¬ ¬ selectionRange p k} :=
    (selectionEquiv p hp).trans (Equiv.subtypeEquivRight (fun k : K => not_not)).symm
  have hd := dual_restriction_bijective B C (fun k => ¬ selectionRange p k) hc
  have hr : Function.Bijective
      (fun g : {k : K // ¬ ¬ selectionRange p k} → V => fun a : A => g (E a)) :=
    (Equiv.arrowCongr E.symm (Equiv.refl V)).bijective
  have h := hr.comp hd
  change Function.Bijective (fun w : (B.product K).annihilator C => fun a : A => w.val (p a)) at h
  exact h

end Selection

def markedHom (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool) :
    ShortenedPlane.graphSubgroup inverse (outputZeros m s) (inputZeros m s) →+ (Marked m → Byte) where
  toFun c := sourceCoordinates (byteDiffusionHom inverse) m s c
  map_zero' := by
    funext p
    change graphCoordinate (byteDiffusionHom inverse) (0 : Fin 4 → Byte) p.val = 0
    cases p.val <;> simp [graphCoordinate]
  map_add' x y := by
    funext p
    change graphCoordinate (byteDiffusionHom inverse) (x.val+y.val) p.val =
      graphCoordinate (byteDiffusionHom inverse) x.val p.val +
        graphCoordinate (byteDiffusionHom inverse) y.val p.val
    cases p.val <;> simp [graphCoordinate, map_add]

def markedCode (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool) :
    AddSubgroup (Marked m → Byte) := (markedHom inverse m s).range

instance markedCodeFintype (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Fintype (markedCode inverse m s) := Fintype.ofFinite _

theorem markedHom_injective (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m)) :
    Function.Injective (markedHom inverse m s) := by
  exact selected_projection_injective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    (outputZeros m s) (inputZeros m s) (fun p : Marked m => p.val) Subtype.val_injective
    (fun p => marked_remaining m s p) hhigh

def sourceCodeEquiv (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m)) :
    ShortenedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) ≃
      markedCode inverse m s :=
  Equiv.ofBijective (markedHom inverse m s).rangeRestrict
    ⟨fun _ _ h => markedHom_injective inverse m s hhigh (congrArg Subtype.val h),
      (markedHom inverse m s).rangeRestrict_surjective⟩

theorem sourceCodeEquiv_apply (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m))
    (c : ShortenedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s)) :
    (sourceCodeEquiv inverse m s hhigh c).val = sourceCoordinates (byteDiffusionHom inverse) m s c := rfl

/-- A source enumeration and the actual image subgroup have the same unit response. -/
theorem normalized_source_eq_code (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m))
    (T : Marked m → Byte → Byte → ℝ) :
    MixedCodeMoment.normalizedResponse T (sourceCoordinates (byteDiffusionHom inverse) m s) =
      action (coordinateKernel T) (unitSubgroupIndicator (markedCode inverse m s)) := by
  rw [MixedCodeMoment.subgroup_response]
  funext y
  let e := sourceCodeEquiv inverse m s hhigh
  unfold MixedCodeMoment.normalizedResponse
  rw [Fintype.card_congr e]
  congr 1
  have h := e.sum_comp (fun c : markedCode inverse m s =>
    MixedCodeMoment.responseKernel T (fun c : markedCode inverse m s => c.val) y c)
  simpa only [MixedCodeMoment.responseKernel, e, sourceCodeEquiv_apply] using h

theorem markedCode_projection_bijective {A : Type*} [Fintype A]
    (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (p : A → Marked m) (hp : Function.Injective p)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card A = 4) :
    Function.Bijective (fun c : markedCode inverse m s => fun a : A => c.val (p a)) := by
  have hs := marked_projection_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    m s p hp hsize
  constructor
  · intro c d h
    obtain ⟨x,hx⟩ := c.property
    obtain ⟨y,hy⟩ := d.property
    have hxy : x = y := by
      apply hs.1
      funext a
      change markedHom inverse m s x (p a) = markedHom inverse m s y (p a)
      rw [hx, hy]
      exact congrFun h a
    apply Subtype.ext
    exact hx.symm.trans ((congrArg (markedHom inverse m s) hxy).trans hy)
  · intro v
    obtain ⟨x,hx⟩ := hs.2 v
    exact ⟨(markedHom inverse m s).rangeRestrict x, hx⟩

/-- The actual trace annihilator information set comes from its actual primal complement. -/
theorem actual_dual_projection_bijective {A : Type*} [Fintype A]
    (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (p : A → Marked m) (hp : Function.Injective p)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      (Fintype.card (Marked m)-Fintype.card A) = 4) :
    Function.Bijective (fun c : (bytePairing.product (Marked m)).annihilator (markedCode inverse m s) =>
      fun a : A => c.val (p a)) := by
  apply dual_projection_bijective_of_complement bytePairing (markedCode inverse m s) p hp
  have hcard := selection_complement_card p hp
  exact markedCode_projection_bijective inverse m s
    (fun k : {k : Marked m // ¬ selectionRange p k} => k.val) Subtype.val_injective (by omega)

section Energy
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

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
  apply MixedCodeMoment.actual_subgroup_energy_dual_le (markedOrientation left right m)
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

end AESConcrete.ActualMarkedCodeDual
