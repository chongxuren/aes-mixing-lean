/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.FiberCollision
import AESMixing.Block
import AESMixing.IncidenceKernel
import Mathlib.Tactic.FieldSimp

/-!
# Normalized finite fibers and raw incidence

For a projection with exactly `m > 0` points over every target label,
`normalizedLift` is the manuscript's normalized fiber map `J`: pull a
function back and divide by `sqrt m`.  Its counting-energy is unchanged.
The signed pairing identity identifies `normalizedAdjoint` as its adjoint,
and multiplication by `sqrt m` recovers the raw sum over a fiber.

The last theorem connects these maps to the existing raw incidence kernel.
Restriction to the middle coordinates is written explicitly as composition
with `middle`; no constancy or uniformity of that input function is assumed.
For the manuscript's admissible outside image, instantiate the target type
with that image.  Equal-fiber cardinalities are required over every element
of the chosen target type, not over a silently restricted set of labels.

These are generic real-vector identities, not AES/MDS fiber counts or
operator bounds.  Code dimensions, coordinate inclusions into ambient
spaces, and local AES bounds remain separate instantiation obligations.
Constructive proof work only; no attacks or predecessor/manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AES8.FiberIncidence

section FiberMaps
variable {C B : Type*} [Fintype C] [Fintype B] [DecidableEq B]

/-- Pullback normalized for fibers of cardinality `m`. -/
def normalizedLift (proj : C → B) (m : ℕ) (f : B → ℝ) : C → ℝ :=
  fun c => f (proj c) / Real.sqrt (m : ℝ)

/-- Raw sum of an arbitrary signed function over one fiber. -/
def rawFiberSum (proj : C → B) (g : C → ℝ) : B → ℝ :=
  fun b => ∑ c : C, if proj c = b then g c else 0

/-- The normalized fiber sum, adjoint to `normalizedLift`. -/
def normalizedAdjoint (proj : C → B) (m : ℕ) (g : C → ℝ) : B → ℝ :=
  fun b => rawFiberSum proj g b / Real.sqrt (m : ℝ)

/-- Regrouping by a fiber preserves the signed counting pairing. -/
theorem rawFiberSum_pairing (proj : C → B) (f : B → ℝ) (g : C → ℝ) :
    (∑ c : C, f (proj c) * g c) =
      ∑ b : B, f b * rawFiberSum proj g b := by
  unfold rawFiberSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp

/-- The adjoint identity holds for arbitrary signed inputs and any `m`.
Positive equal fibers are needed for the isometry, not this pairing identity. -/
theorem normalizedAdjoint_pairing (proj : C → B) (m : ℕ)
    (f : B → ℝ) (g : C → ℝ) :
    (∑ c : C, normalizedLift proj m f c * g c) =
      ∑ b : B, f b * normalizedAdjoint proj m g b := by
  calc
    (∑ c : C, normalizedLift proj m f c * g c) =
        (∑ c : C, f (proj c) * g c) / Real.sqrt (m : ℝ) := by
      simp only [normalizedLift, div_mul_eq_mul_div, Finset.sum_div]
    _ = (∑ b : B, f b * rawFiberSum proj g b) / Real.sqrt (m : ℝ) := by
      rw [rawFiberSum_pairing]
    _ = ∑ b : B, f b * normalizedAdjoint proj m g b := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [normalizedAdjoint]
      ring

/-- Squared-energy form of the equal-cardinality fiber-map isometry.
The cardinality hypothesis covers every target value, and `f` may be signed. -/
theorem normalizedLift_energy (proj : C → B) (m : ℕ) (hm : 0 < m)
    (hfiber : ∀ b, Fintype.card {c : C // proj c = b} = m) (f : B → ℝ) :
    (∑ c : C, normalizedLift proj m f c ^ 2) = ∑ b : B, f b ^ 2 := by
  have hmR : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  calc
    (∑ c : C, normalizedLift proj m f c ^ 2) =
        (∑ c : C, f (proj c) ^ 2) / (m : ℝ) := by
      simp only [normalizedLift, div_pow, Real.sq_sqrt (Nat.cast_nonneg m),
        Finset.sum_div]
    _ = ((m : ℝ) * ∑ b : B, f b ^ 2) / (m : ℝ) := by
      rw [AES8.FiberCollision.constant_fiber_sum proj m hfiber (fun b => f b ^ 2)]
    _ = ∑ b : B, f b ^ 2 := by
      field_simp [hmR]

/-- The same isometry for the repository's counting `l2` norm. -/
theorem normalizedLift_l2 (proj : C → B) (m : ℕ) (hm : 0 < m)
    (hfiber : ∀ b, Fintype.card {c : C // proj c = b} = m) (f : B → ℝ) :
    AESMixing.l2 (normalizedLift proj m f) = AESMixing.l2 f := by
  unfold AESMixing.l2
  rw [normalizedLift_energy proj m hm hfiber f]

/-- Exact raw/normalized conversion; no bound or equal-fiber premise is used. -/
theorem rawFiberSum_eq_sqrt_mul_adjoint (proj : C → B) (m : ℕ) (hm : 0 < m)
    (g : C → ℝ) (b : B) :
    rawFiberSum proj g b =
      Real.sqrt (m : ℝ) * normalizedAdjoint proj m g b := by
  have hs : Real.sqrt (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm))
  unfold normalizedAdjoint
  field_simp [hs] <;> ring

end FiberMaps

section RawIncidence
variable {C O I : Type*} [Fintype C] [Fintype O] [Fintype I]
  [DecidableEq O] [DecidableEq I]

/-- Signed raw incidence is exactly `sqrt m` times the normalized adjoint
after restriction along `middle`.  No condition is imposed on `f` along a
fiber.  To obtain an isometric lift, supply equal fibers separately to
`normalizedLift_energy`; this algebraic identity itself needs only `m > 0`. -/
theorem incidenceMultiplicity_eq_sqrt_mul_adjoint
    (outside : C → O) (middle : C → I) (m : ℕ) (hm : 0 < m)
    (f : I → ℝ) (y : O) :
    AESMixing.action (AESMixing.incidenceMultiplicity outside middle) f y =
      Real.sqrt (m : ℝ) *
        normalizedAdjoint outside m (fun c => f (middle c)) y := by
  rw [AESMixing.incidenceMultiplicity_action]
  exact rawFiberSum_eq_sqrt_mul_adjoint outside m hm (fun c => f (middle c)) y

end RawIncidence

end AES8.FiberIncidence
