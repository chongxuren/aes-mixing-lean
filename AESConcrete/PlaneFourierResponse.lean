import AESConcrete.ByteLineBounds
import AESMixing.ProductFourier

/-!
# Pointwise plane-to-Fourier-line responses

Fourier acts on the input indicator of an explicit additive subgroup, not on
the output response. Thus the transformed leg is T F in the original output
space; no residual/Fourier commutation or output-space conjugation is assumed.

The actual byte trace pairing is used throughout the byte specialization.
The plane cardinality 65536 and an explicit coordinate parameterization of its
annihilator are structural hypotheses. Identifying an actual shortened AES
plane with this subgroup, proving its annihilator is the required MDS line,
and constructing the parameter equivalence are separate obligations.
Constructive proof support only; no attacks or manuscript/historical edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.PlaneFourierResponse
open AESMixing
open AESConcrete.ByteGramCore (Byte)
open AESConcrete.ByteGramFourier (byteFourier_pairing)
open AESConcrete.DampedLineGram (lineResponse)
attribute [local instance] Classical.propDecidable

section SubgroupIndicators
variable {X Y : Type*} [AddCommGroup X] [Fintype X]

/-- Ordinary subgroup indicator, without unit-vector normalization. -/
def subgroupIndicator (C : AddSubgroup X) (x : X) : ℝ :=
  if x ∈ C then 1 else 0

theorem action_subgroupIndicator (K : Y → X → ℝ) (C : AddSubgroup X)
    [Fintype C] (y : Y) :
    action K (subgroupIndicator C) y = ∑ c : C, K y c.val := by
  classical
  unfold action subgroupIndicator
  have ht (x : X) : K y x * (if x ∈ C then (1 : ℝ) else 0) =
      if x ∈ C then K y x else 0 := by
    split_ifs <;> simp
  simp_rw [ht]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem action_unitSubgroupIndicator (K : Y → X → ℝ) (C : AddSubgroup X)
    [Fintype C] (y : Y) :
    action K (unitSubgroupIndicator C) y =
      (∑ c : C, K y c.val) / Real.sqrt (Fintype.card C) := by
  classical
  have ht (x : X) : K y x * unitSubgroupIndicator C x =
      (if x ∈ C then K y x else 0) / Real.sqrt (Fintype.card C) := by
    by_cases hx : x ∈ C <;> simp [unitSubgroupIndicator, hx, div_eq_mul_inv]
  unfold action
  simp_rw [ht]
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem fourier_subgroupIndicator (B : CharacterPairing X) (C : AddSubgroup X)
    [Fintype C] (w : X) :
    action (pairingFourier B) (subgroupIndicator C) w =
      if w ∈ B.annihilator C then
        (Fintype.card C : ℝ) / Real.sqrt (Fintype.card X) else 0 := by
  rw [action_subgroupIndicator]
  simp only [pairingFourier]
  rw [← Finset.sum_div, B.subgroup_sum]
  split_ifs <;> simp

end SubgroupIndicators

section ProductResponse
variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V]

/-- Pointwise input duality for arbitrary per-leg response kernels.
The output y is unchanged and each right-hand leg is exactly T_i F. -/
theorem unit_response_dual_pointwise (B : CharacterPairing V)
    (hchar : ∀ x : V, x+x = 0) (T : I → V → V → ℝ)
    (C : AddSubgroup (I → V)) [Fintype C] (y : I → V) :
    action (coordinateKernel T) (unitSubgroupIndicator C) y =
      action (coordinateKernel (fun i => kernelCompose (T i) (pairingFourier B)))
        (unitSubgroupIndicator ((B.product I).annihilator C)) y := by
  have hp : ∀ x : I → V, x+x = 0 := by
    intro x
    funext i
    exact hchar (x i)
  have hback : action (pairingFourier (B.product I))
      (unitSubgroupIndicator ((B.product I).annihilator C)) = unitSubgroupIndicator C := by
    rw [← pairingFourier_subgroup (B.product I) C]
    exact pairingFourier_twice (B.product I) hp (unitSubgroupIndicator C)
  rw [← hback, ← kernelCompose_action, productPairing_fourier, coordinateKernel_compose]

end ProductResponse

-- Actual byte-field/pairing coercions need more unfolding depth than the
-- generic subgroup algebra. This changes no certificate or trust mechanism.
set_option maxRecDepth 65536

abbrev Triple := Fin 3 → Byte

/-- The actual polynomial-byte trace pairing on three physical labels. -/
def triplePairing : CharacterPairing Triple := bytePairing.product (Fin 3)

def byteDual (C : AddSubgroup Triple) : AddSubgroup Triple :=
  triplePairing.annihilator C

theorem byte_unit_response_dual_pointwise (T : Fin 3 → Byte → Byte → ℝ)
    (C : AddSubgroup Triple) [Fintype C] (y : Triple) :
    action (coordinateKernel T) (unitSubgroupIndicator C) y =
      action (coordinateKernel (fun i => kernelCompose (T i) byteFourierMatrix))
        (unitSubgroupIndicator (byteDual C)) y := by
  have h := unit_response_dual_pointwise bytePairing BinaryWord.add_self T C y
  -- The named annihilator and the byteDual wrapper synthesize different
  -- Fintype values on the same subtype. Nat.card removes that implementation
  -- choice from the normalization before the functions are compared.
  unfold unitSubgroupIndicator at h ⊢
  simpa only [byteDual, triplePairing, ← byteFourier_pairing,
    ← Nat.card_eq_fintype_card] using h

/-- A byte plane of the displayed cardinality has a 256-point trace
annihilator. The subgroup cardinality law supplies this rather than a table. -/
theorem byte_dual_card (C : AddSubgroup Triple) [Fintype C]
    (hC : Fintype.card C = 65536) : Fintype.card (byteDual C) = 256 := by
  have h := triplePairing.annihilator_card C
  have hn : Nat.card (byteDual C) * Nat.card C = Nat.card Triple := by
    simpa only [byteDual, ← Nat.card_eq_fintype_card] using h
  have hCn : Nat.card C = 65536 := by
    simpa only [← Nat.card_eq_fintype_card] using hC
  have hX : Nat.card Triple = 16777216 := by
    rw [Nat.card_eq_fintype_card]
    norm_num [Triple, Fintype.card_fun, BinaryWord.card]
  rw [hCn, hX] at hn
  have hD : Nat.card (byteDual C) = 256 := by omega
  simpa only [← Nat.card_eq_fintype_card] using hD

private theorem triple_sqrt_card : Real.sqrt (Fintype.card Triple) = (4096 : ℝ) := by
  have h : (Fintype.card Triple : ℝ) = (4096 : ℝ)^2 := by
    norm_num [Triple, Fintype.card_fun, BinaryWord.card]
  rw [h, Real.sqrt_sq_eq_abs]
  norm_num

/-- Exact factor 16 for the ordinary plane indicator under the normalized
three-byte Fourier transform. This does not move any output coordinate. -/
theorem byte_plane_fourier_indicator (C : AddSubgroup Triple) [Fintype C]
    (hC : Fintype.card C = 65536) (w : Triple) :
    action (pairingFourier triplePairing) (subgroupIndicator C) w =
      16 * subgroupIndicator (byteDual C) w := by
  rw [fourier_subgroupIndicator, triple_sqrt_card, hC]
  change (if w ∈ byteDual C then (65536 : ℝ)/4096 else 0) =
    16 * subgroupIndicator (byteDual C) w
  by_cases hw : w ∈ byteDual C <;> norm_num [subgroupIndicator, hw]

def rawResponse (T : Fin 3 → Byte → Byte → ℝ) (C : AddSubgroup Triple)
    [Fintype C] (y : Triple) : ℝ :=
  ∑ c : C, coordinateKernel T y c.val

/-- The source's three-byte plane convention is a raw response divided
by sqrt(256^3)=4096, not the unit-plane divisor sqrt(65536)=256. -/
def planeResponse (T : Fin 3 → Byte → Byte → ℝ) (C : AddSubgroup Triple)
    [Fintype C] (y : Triple) : ℝ := rawResponse T C y / 4096

private theorem sqrt_plane_card (C : AddSubgroup Triple) [Fintype C]
    (hC : Fintype.card C = 65536) : Real.sqrt (Fintype.card C) = (256 : ℝ) := by
  rw [hC]
  norm_num only [Nat.cast_ofNat]
  rw [show (65536 : ℝ) = (256 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

private theorem sqrt_dual_card (C : AddSubgroup Triple) [Fintype C]
    (hC : Fintype.card C = 65536) : Real.sqrt (Fintype.card (byteDual C)) = (16 : ℝ) := by
  rw [byte_dual_card C hC]
  norm_num only [Nat.cast_ofNat]
  rw [show (256 : ℝ) = (16 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num

/-- Pointwise normalized plane-to-dual response in the original joint
output space. Only the input legs acquire Fourier: T_i becomes T_i F. -/
theorem plane_response_dual_pointwise (T : Fin 3 → Byte → Byte → ℝ)
    (C : AddSubgroup Triple) [Fintype C] (hC : Fintype.card C = 65536) (y : Triple) :
    planeResponse T C y =
      rawResponse (fun i => kernelCompose (T i) byteFourierMatrix) (byteDual C) y / 256 := by
  have h := byte_unit_response_dual_pointwise T C y
  rw [action_unitSubgroupIndicator, action_unitSubgroupIndicator] at h
  change rawResponse T C y / Real.sqrt (Fintype.card C) =
    rawResponse (fun i => kernelCompose (T i) byteFourierMatrix) (byteDual C) y /
      Real.sqrt (Fintype.card (byteDual C)) at h
  rw [sqrt_plane_card C hC, sqrt_dual_card C hC] at h
  unfold planeResponse
  linarith

/-- Structural parameterization contract for a dual line. No such
parameter equivalence is inferred from cardinality alone. -/
theorem parameterized_dual_response (T : Fin 3 → Byte → Byte → ℝ)
    (C : AddSubgroup Triple) (e : Fin 3 → Equiv.Perm Byte)
    (param : Byte ≃ byteDual C)
    (hcoord : ∀ (x : Byte) (i : Fin 3), (param x).val i = e i x) (y : Triple) :
    rawResponse T (byteDual C) y / 256 = lineResponse T e y := by
  unfold rawResponse
  rw [← Equiv.sum_comp param (fun c : byteDual C => coordinateKernel T y c.val)]
  unfold lineResponse
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  unfold coordinateKernel
  apply Finset.prod_congr rfl
  intro i _
  rw [hcoord]

/-- Final pointwise form, conditional only on explicit subgroup size and
coordinate parameterization. Actual shortened-plane/annihilator identification
is intentionally not supplied or hidden in a numerical estimate. -/
theorem plane_response_eq_fourier_line (T : Fin 3 → Byte → Byte → ℝ)
    (C : AddSubgroup Triple) [Fintype C] (hC : Fintype.card C = 65536)
    (e : Fin 3 → Equiv.Perm Byte) (param : Byte ≃ byteDual C)
    (hcoord : ∀ (x : Byte) (i : Fin 3), (param x).val i = e i x) (y : Triple) :
    planeResponse T C y =
      lineResponse (fun i => kernelCompose (T i) byteFourierMatrix) e y := by
  exact (plane_response_dual_pointwise T C hC y).trans
    (parameterized_dual_response (fun i => kernelCompose (T i) byteFourierMatrix)
      C e param hcoord y)

end AESConcrete.PlaneFourierResponse
