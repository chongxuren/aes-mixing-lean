import AES8.Recurrence.TransferAssembly
import AES8.Recurrence.PaperNormalizedOutput
import AES8.Recurrence.PaperTwoStep

/-!
# Actual AES profile assembly for arbitrary comparison matrices

The physical errors, centered step and high return are the existing concrete
AES operators. Reusable linearity and normalization come from TransferAssembly;
the current matrices and startup data are explicit parameters. This checks the
paper's reduction from its component estimates to the normalized recurrence,
without importing the historical comparison coefficients as current ones.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AES8.PaperProfileAssembly
open AESMixing AESMixing.AES
open AES8.TransferAssembly AES8.SupportEvolution
open AESPaper.GroupedLaw (error)

/-- Actual normalized first-step and memory estimates for the given maps. -/
structure ActualTransfer (B C : Fin 14 → Fin 14 → ℝ) (g : AES8.Profile) : Prop where
  first : ∀ a : AES.State, a ≠ 0 → NormalizedProfile.actual a 1 ≤ fun i =>
    AESRound.matVec B (NormalizedProfile.actual a 0) i + 1000 * g i
  step : ∀ a : AES.State, a ≠ 0 →
    PaperTwoStep.MemoryRecurrence B C (NormalizedProfile.actual a)

theorem matVec_low {B : Fin 14 → Fin 14 → ℝ}
    (hzero : ∀ (i : Fin 14) (k : Fin 3), B i (Fin.natAdd 11 k) = 0) (v : AES8.Profile) (i : Fin 14) :
    AESRound.matVec B v i = ∑ k : Fin 11, B i (Fin.castAdd 3 k) * v (Fin.castAdd 3 k) := by
  unfold AESRound.matVec
  rw [Fin.sum_univ_add (a := 11) (b := 3)]
  simp only [hzero, zero_mul, Finset.sum_const_zero, add_zero]

/-- Physical block caps, independently required for the current matrices. -/
structure PhysicalCaps (B C : Fin 14 → Fin 14 → ℝ) (g : AES8.Profile) : Prop where
  low : ∀ (f : WordState → ℝ) (i : Fin 14) (k : Fin 11),
    SupportProfile.profile (centeredStep (SupportProfile.component f (Fin.castAdd 3 k))) i ≤
      physicalCoeff 1 i (Fin.castAdd 3 k) (B i (Fin.castAdd 3 k)) *
        SupportProfile.profile f (Fin.castAdd 3 k)
  high : ∀ (f : WordState → ℝ) (i k : Fin 14),
    SupportProfile.profile (highReturn (SupportProfile.component f k)) i ≤
      physicalCoeff 2 i k (C i k) * SupportProfile.profile f k
  firstHigh : ∀ (a : AES.State), a ≠ 0 → ∀ i : Fin 14,
    SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤
      (d i / NormalizedProfile.factor 1) * (1000 * g i)

section Assembly
variable {B C : Fin 14 → Fin 14 → ℝ} {g : AES8.Profile}

theorem low_profile_le (h : PhysicalCaps B C g) (f : WordState → ℝ) (i : Fin 14) :
    SupportProfile.profile (centeredStep (lowPart f)) i ≤
      ∑ k : Fin 11, physicalCoeff 1 i (Fin.castAdd 3 k) (B i (Fin.castAdd 3 k)) *
        SupportProfile.profile f (Fin.castAdd 3 k) := by
  change SupportProfile.profile (centeredStep
    (fun x => ∑ k : Fin 11, SupportProfile.component f (Fin.castAdd 3 k) x)) i ≤ _
  rw [centeredStep_sum]
  exact (profile_sum_le _ i).trans (Finset.sum_le_sum (fun k _ => h.low f i k))

theorem high_profile_le (h : PhysicalCaps B C g) (f : WordState → ℝ) (hz : f 0 = 0)
    (i : Fin 14) :
    SupportProfile.profile (highReturn f) i ≤
      ∑ k : Fin 14, physicalCoeff 2 i k (C i k) *
        SupportProfile.profile f k := by
  have hf : f = fun x => ∑ k : Fin 14, SupportProfile.component f k x :=
    funext (fun x => (SupportProfile.component_decomposition f hz x).symm)
  have he : highReturn f =
      fun x => ∑ k : Fin 14, highReturn (SupportProfile.component f k) x := by
    calc
      highReturn f = highReturn (fun x => ∑ k : Fin 14, SupportProfile.component f k x) :=
        congrArg highReturn hf
      _ = _ := highReturn_sum _
  rw [he]
  exact (profile_sum_le _ i).trans (Finset.sum_le_sum (fun k _ => h.high f i k))

theorem normalized_low_le (h : PhysicalCaps B C g)
    (hzero : ∀ (i : Fin 14) (k : Fin 3), B i (Fin.natAdd 11 k) = 0) (f : WordState → ℝ)
    (j : ℕ) (i : Fin 14) :
    (NormalizedProfile.factor (j + 1) / d i) *
        SupportProfile.profile (centeredStep (lowPart f)) i ≤
      AESRound.matVec B (fun k => NormalizedProfile.factor j * SupportProfile.profile f k / d k) i := by
  have hs : 0 ≤ NormalizedProfile.factor (j + 1) / d i :=
    div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
  calc
    _ ≤ (NormalizedProfile.factor (j + 1) / d i) *
        (∑ k : Fin 11, physicalCoeff 1 i (Fin.castAdd 3 k) (B i (Fin.castAdd 3 k)) *
          SupportProfile.profile f (Fin.castAdd 3 k)) :=
      mul_le_mul_of_nonneg_left (low_profile_le h f i) hs
    _ = ∑ k : Fin 11, B i (Fin.castAdd 3 k) *
        (NormalizedProfile.factor j * SupportProfile.profile f (Fin.castAdd 3 k) /
          d (Fin.castAdd 3 k)) :=
      normalized_sum (Fin.castAdd 3) (fun k => B i (Fin.castAdd 3 k)) (SupportProfile.profile f) j 1 i
    _ = _ := (matVec_low hzero
      (fun k => NormalizedProfile.factor j * SupportProfile.profile f k / d k) i).symm

theorem normalized_high_le (h : PhysicalCaps B C g) (f : WordState → ℝ) (hz : f 0 = 0)
    (j : ℕ) (i : Fin 14) :
    (NormalizedProfile.factor (j + 2) / d i) * SupportProfile.profile (highReturn f) i ≤
      AESRound.matVec C (fun k => NormalizedProfile.factor j * SupportProfile.profile f k / d k) i := by
  have hs : 0 ≤ NormalizedProfile.factor (j + 2) / d i :=
    div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
  calc
    _ ≤ (NormalizedProfile.factor (j + 2) / d i) *
        (∑ k : Fin 14, physicalCoeff 2 i k (C i k) * SupportProfile.profile f k) :=
      mul_le_mul_of_nonneg_left (high_profile_le h f hz i) hs
    _ = ∑ k : Fin 14, C i k *
        (NormalizedProfile.factor j * SupportProfile.profile f k / d k) :=
      normalized_sum (fun k => k) (C i) (SupportProfile.profile f) j 2 i
    _ = _ := rfl

theorem normalized_firstHigh_le (h : PhysicalCaps B C g) (a : AES.State) (ha : a ≠ 0)
    (i : Fin 14) :
    (NormalizedProfile.factor 1 / d i) *
      SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤ 1000 * g i := by
  have hs : 0 ≤ NormalizedProfile.factor 1 / d i :=
    div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
  have hi : d i ≠ 0 := (NormalizedProfile.diagonal_pos i).ne'
  have hf : NormalizedProfile.factor 1 ≠ 0 := (NormalizedProfile.factor_pos 1).ne'
  calc
    _ ≤ (NormalizedProfile.factor 1 / d i) *
        ((d i / NormalizedProfile.factor 1) * (1000 * g i)) :=
      mul_le_mul_of_nonneg_left (h.firstHigh a ha i) hs
    _ = 1000 * g i := by field_simp [hi, hf]

/-- The current recurrence follows from physical component estimates for the
specified matrices. Neither historical L/M nor their finite certificates occur. -/
theorem transferEstimates (h : PhysicalCaps B C g)
    (hzero : ∀ (i : Fin 14) (k : Fin 3), B i (Fin.natAdd 11 k) = 0) :
    ActualTransfer B C g where
  first := by
    intro a ha i
    have ht := profile_add_le (centeredStep (lowPart (error 1 a)))
      (centeredStep (highPart (error 1 a))) i
    rw [← centered_actual_first a ha] at ht
    have hl := normalized_low_le h hzero (error 1 a) 0 i
    change _ ≤ AESRound.matVec B (NormalizedProfile.actual a 0) i at hl
    have hh := normalized_firstHigh_le h a ha i
    have hs : 0 ≤ NormalizedProfile.factor 1 / d i :=
      div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
    change NormalizedProfile.factor 1 * SupportProfile.profile (error 2 a) i / d i ≤ _
    calc
      _ = (NormalizedProfile.factor 1 / d i) * SupportProfile.profile (error 2 a) i := by ring
      _ ≤ (NormalizedProfile.factor 1 / d i) *
          (SupportProfile.profile (centeredStep (lowPart (error 1 a))) i +
            SupportProfile.profile (centeredStep (highPart (error 1 a))) i) :=
        mul_le_mul_of_nonneg_left ht hs
      _ = (NormalizedProfile.factor 1 / d i) *
            SupportProfile.profile (centeredStep (lowPart (error 1 a))) i +
          (NormalizedProfile.factor 1 / d i) *
            SupportProfile.profile (centeredStep (highPart (error 1 a))) i := by ring
      _ ≤ _ := add_le_add hl hh
  step := by
    intro a ha j i
    have ht := profile_add_le (centeredStep (lowPart (error (j + 2) a)))
      (highReturn (error (j + 1) a)) i
    rw [← centered_actual_memory j a ha] at ht
    have hl : (NormalizedProfile.factor (j + 2) / d i) *
        SupportProfile.profile (centeredStep (lowPart (error (j + 2) a))) i ≤
        AESRound.matVec B (NormalizedProfile.actual a (j + 1)) i := by
      have hl0 := normalized_low_le h hzero (error (j + 2) a) (j + 1) i
      have hindex : (j + 1) + 1 = j + 2 := by omega
      rw [hindex] at hl0
      have hactual :
          (fun k => NormalizedProfile.factor (j + 1) *
            SupportProfile.profile (error (j + 2) a) k / d k) =
          NormalizedProfile.actual a (j + 1) := by
        funext k
        simp only [NormalizedProfile.actual, SupportProfile.actual, hindex]
      rw [hactual] at hl0
      exact hl0
    have hh := normalized_high_le h (error (j + 1) a)
      (AESPaper.GroupedLaw.error_zero _ a ha) j i
    change _ ≤ AESRound.matVec C (NormalizedProfile.actual a j) i at hh
    have hs : 0 ≤ NormalizedProfile.factor (j + 2) / d i :=
      div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
    change NormalizedProfile.factor (j + 2) *
      SupportProfile.profile (error (j + 3) a) i / d i ≤ _
    calc
      _ = (NormalizedProfile.factor (j + 2) / d i) *
          SupportProfile.profile (error (j + 3) a) i := by ring
      _ ≤ (NormalizedProfile.factor (j + 2) / d i) *
          (SupportProfile.profile (centeredStep (lowPart (error (j + 2) a))) i +
            SupportProfile.profile (highReturn (error (j + 1) a)) i) :=
        mul_le_mul_of_nonneg_left ht hs
      _ = (NormalizedProfile.factor (j + 2) / d i) *
            SupportProfile.profile (centeredStep (lowPart (error (j + 2) a))) i +
          (NormalizedProfile.factor (j + 2) / d i) *
            SupportProfile.profile (highReturn (error (j + 1) a)) i := by ring
      _ ≤ _ := add_le_add hl hh

end Assembly

/-- Exact diagonal conversion of the paper's four-round startup estimate. -/
theorem normalized_initial (u : AES8.Profile) (a : AES.State)
    (h : ∀ i, NormalizedProfile.factor 0 * SupportProfile.actual a 0 i ≤
      d i * (1000 * u i)) : NormalizedProfile.actual a 0 ≤ AES8.scale 1000 u := by
  intro i
  apply (div_le_iff₀ (NormalizedProfile.diagonal_pos i)).mpr
  simpa only [AES8.scale, _root_.mul_comm] using h i

end AES8.PaperProfileAssembly
