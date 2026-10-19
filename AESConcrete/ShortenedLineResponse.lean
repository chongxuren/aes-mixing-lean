import AESConcrete.ByteLineBounds
import AESMixing.ShortenedIncidence
import AESMixing.GraphExpansion
import AESMixing.MDSInverse
import AESMixing.CodeResponse
import AESMixing.AESGramOrientation

/-!
# Actual shortened MDS graphs as three-leg line responses

Three zero constraints on the input/output graph leave one alphabet
parameter. Every remaining graph coordinate is a bijective parameter,
by the existing MDS information-set theorem. The three marked coordinates
are consequently actual zero-preserving permutations of a common parameter.
The product-kernel action on the projected code indicator is then reindexed,
with its counting-measure and unit-code normalizations kept explicit.

The final finite statements count ten three-zero choices and ten two-zero
choices outside a fixed marked output triple. They do not identify the
plane's Fourier dual, prove pairwise code-intersection cases, or assemble
the degree-three word block. Constructive scope only; no attacks, local
workloads, manuscript edits, or historical-source edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedLineResponse
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.DampedLineGram (lineResponse)

/-- A genuine singleton subset of the four physical coordinate labels. -/
def singletonMask (i : Fin 4) : Fin 16 :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | _ => 8

theorem singletonMask_bit (i j : Fin 4) : maskBit (singletonMask i) j = true ↔ j = i := by
  fin_cases i <;> fin_cases j <;> decide

theorem singletonMask_size (i : Fin 4) : maskSize (singletonMask i) = 1 := by
  fin_cases i <;> decide

/-- A remaining graph position is outside the already imposed zero masks. -/
def remaining (r z : Fin 16) : GraphPosition → Prop :=
  Sum.elim (fun i => maskBit r i ≠ true) (fun i => maskBit z i ≠ true)

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def zeroGraph (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :
    ShortenedGraph L r z :=
  ⟨0, by constructor <;> intro i _ <;> simp⟩

def coordinateMap (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (p : GraphPosition) (x : ShortenedGraph L r z) : V :=
  graphCoordinate L x.val p

theorem output_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (i : Fin 4) (hi : maskBit r i ≠ true) :
    Function.Bijective (fun x : ShortenedGraph L r z => L x.val i) := by
  have hr : MaskDisjoint r (singletonMask i) := by
    intro j hj hs
    have hji := (singletonMask_bit i j).mp hs
    subst j
    exact hi hj
  have hsize : maskSize r + maskSize z + maskSize (singletonMask i) + maskSize 0 = 4 := by
    rw [singletonMask_size, show maskSize 0 = 0 by decide]
    omega
  have hb := shortened_projection_bijective L hL r z (singletonMask i) 0
    hr (mask_disjoint_empty z) hsize
  constructor
  · intro x y hxy
    apply hb.1
    apply Prod.ext
    · funext j
      have hji := (singletonMask_bit i j.val).mp j.property
      change L x.val j.val = L y.val j.val
      simpa only [hji] using hxy
    · funext j
      exact (empty_mask_coordinate j).elim
  · intro v
    obtain ⟨x, hx⟩ := hb.2 ((fun _ => v), fun _ => 0)
    refine ⟨x, ?_⟩
    exact congrFun (congrArg Prod.fst hx) ⟨i, (singletonMask_bit i i).mpr rfl⟩

theorem input_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (i : Fin 4) (hi : maskBit z i ≠ true) :
    Function.Bijective (fun x : ShortenedGraph L r z => x.val i) := by
  have hz : MaskDisjoint z (singletonMask i) := by
    intro j hj hs
    have hji := (singletonMask_bit i j).mp hs
    subst j
    exact hi hj
  have hsize : maskSize r + maskSize z + maskSize 0 + maskSize (singletonMask i) = 4 := by
    rw [singletonMask_size, show maskSize 0 = 0 by decide]
    omega
  have hb := shortened_projection_bijective L hL r z 0 (singletonMask i)
    (mask_disjoint_empty r) hz hsize
  constructor
  · intro x y hxy
    apply hb.1
    apply Prod.ext
    · funext j
      exact (empty_mask_coordinate j).elim
    · funext j
      have hji := (singletonMask_bit i j.val).mp j.property
      change x.val j.val = y.val j.val
      simpa only [hji] using hxy
  · intro v
    obtain ⟨x, hx⟩ := hb.2 ((fun _ => 0), fun _ => v)
    refine ⟨x, ?_⟩
    exact congrFun (congrArg Prod.snd hx) ⟨i, (singletonMask_bit i i).mpr rfl⟩

theorem coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (p : GraphPosition) (hp : remaining r z p) :
    Function.Bijective (coordinateMap L r z p) := by
  cases p with
  | inl i => exact output_coordinate_bijective L hL r z hshort i hp
  | inr i => exact input_coordinate_bijective L hL r z hshort i hp

def coordinateEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (p : GraphPosition) (hp : remaining r z p) :
    ShortenedGraph L r z ≃ V :=
  Equiv.ofBijective (coordinateMap L r z p) (coordinate_bijective L hL r z hshort p hp)

theorem coordinateEquiv_apply
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (p : GraphPosition) (hp : remaining r z p)
    (x : ShortenedGraph L r z) :
    coordinateEquiv L hL r z hshort p hp x = graphCoordinate L x.val p := by
  simp only [coordinateEquiv, Equiv.ofBijective_apply, coordinateMap]

theorem coordinateEquiv_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (p : GraphPosition) (hp : remaining r z p) :
    coordinateEquiv L hL r z hshort p hp (zeroGraph L r z) = 0 := by
  rw [coordinateEquiv_apply]
  cases p <;> simp [zeroGraph, graphCoordinate]

theorem coordinateEquiv_symm_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (p : GraphPosition) (hp : remaining r z p) :
    (coordinateEquiv L hL r z hshort p hp).symm 0 = zeroGraph L r z := by
  apply (coordinateEquiv L hL r z hshort p hp).injective
  rw [Equiv.apply_symm_apply, coordinateEquiv_zero]

/-- The first marked coordinate is the common parameter; every marked
coordinate is its actual zero-preserving permutation. -/
def lineCoordinatePerm
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) : Equiv.Perm V :=
  (coordinateEquiv L hL r z hshort (marked 0) (hm 0)).symm.trans
    (coordinateEquiv L hL r z hshort (marked i) (hm i))

theorem lineCoordinatePerm_apply
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) (x : V) :
    lineCoordinatePerm L hL r z hshort marked hm i x =
      graphCoordinate L
        ((coordinateEquiv L hL r z hshort (marked 0) (hm 0)).symm x).val (marked i) := by
  exact coordinateEquiv_apply L hL r z hshort (marked i) (hm i) _

theorem lineCoordinatePerm_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (i : Fin 3) :
    lineCoordinatePerm L hL r z hshort marked hm i 0 = 0 := by
  rw [lineCoordinatePerm_apply, coordinateEquiv_symm_zero]
  cases h : marked i <;> simp [zeroGraph, graphCoordinate, h]

def markedGraph (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (marked : Fin 3 → GraphPosition) (x : ShortenedGraph L r z) : Fin 3 → V :=
  fun i => graphCoordinate L x.val (marked i)

theorem markedGraph_injective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) : Function.Injective (markedGraph L r z marked) := by
  intro x y hxy
  apply (coordinate_bijective L hL r z hshort (marked 0) (hm 0)).1
  exact congrFun hxy 0

def shortenedResponse (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (marked : Fin 3 → GraphPosition) (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) : ℝ :=
  ∑ x : ShortenedGraph L r z, ∏ i, T i (y i) (markedGraph L r z marked x i)

theorem shortened_response_eq_card_line
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) :
    shortenedResponse L r z marked T y =
      (Fintype.card V : ℝ) * lineResponse T (lineCoordinatePerm L hL r z hshort marked hm) y := by
  let e := coordinateEquiv L hL r z hshort (marked 0) (hm 0)
  have he : shortenedResponse L r z marked T y =
      ∑ x : V, ∏ i, T i (y i) (lineCoordinatePerm L hL r z hshort marked hm i x) := by
    calc
      _ = ∑ x : V, ∏ i, T i (y i) (markedGraph L r z marked (e.symm x) i) :=
        (Equiv.sum_comp e.symm
          (fun x => ∏ i, T i (y i) (markedGraph L r z marked x i))).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.prod_congr rfl
        intro i _
        rw [lineCoordinatePerm_apply]
        rfl
  rw [he, lineResponse]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hn]

theorem shortened_card
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) :
    Fintype.card (ShortenedGraph L r z) = Fintype.card V := by
  rw [mds_graph_zero_count L hL r z, hshort]
  norm_num

end Generic

section Indicator
variable {C W Y : Type*} [Fintype C] [Fintype W] [DecidableEq W]

/-- The ordinary indicator of the actual projected code, without multiplicities. -/
def codeIndicator (c : C → W) (x : W) : ℝ := by
  classical
  exact if ∃ u, c u = x then 1 else 0

theorem codeIndicator_as_sum (c : C → W) (hc : Function.Injective c) (x : W) :
    codeIndicator c x = ∑ u, identityKernel x (c u) := by
  classical
  by_cases hx : ∃ u, c u = x
  · rw [codeIndicator, if_pos hx]
    obtain ⟨u, hu⟩ := hx
    symm
    rw [Finset.sum_eq_single u]
    · simp [identityKernel, hu]
    · intro v _ hv
      have hxv : x ≠ c v := by
        intro h
        exact hv (hc (h.symm.trans hu.symm))
      simp [identityKernel, hxv]
    · simp
  · rw [codeIndicator, if_neg hx]
    symm
    apply Finset.sum_eq_zero
    intro u _
    have hxu : x ≠ c u := by
      intro h
      exact hx ⟨u, h.symm⟩
    simp [identityKernel, hxu]

theorem action_codeIndicator (K : Y → W → ℝ) (c : C → W) (hc : Function.Injective c)
    (y : Y) : action K (codeIndicator c) y = ∑ u, K y (c u) := by
  classical
  unfold action
  simp_rw [codeIndicator_as_sum c hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [identityKernel]

end Indicator

section GenericAction
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The genuine product-kernel action on the projected shortened code.
Injectivity makes the code indicator count every graph point exactly once. -/
theorem shortened_code_action
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) :
    action (coordinateKernel T) (codeIndicator (markedGraph L r z marked)) y =
      (Fintype.card V : ℝ) * lineResponse T (lineCoordinatePerm L hL r z hshort marked hm) y := by
  rw [action_codeIndicator _ _ (markedGraph_injective L hL r z hshort marked hm)]
  exact shortened_response_eq_card_line L hL r z hshort marked hm T y

end GenericAction

abbrev Byte := BinaryWord 8

/-- Actual forward/inverse AES byte diffusion as an additive map. -/
def byteDiffusionHom (inverse : Bool) : (Fin 4 → Byte) →+ (Fin 4 → Byte) :=
  if inverse then byteDiffusionAddEquiv.symm.toAddMonoidHom else byteDiffusionAddEquiv.toAddMonoidHom

theorem byteDiffusionHom_zeroMDS (inverse : Bool) : ZeroMDS (byteDiffusionHom inverse) := by
  cases inverse
  · exact byteDiffusionAddEquiv_zeroMDS
  · exact byteDiffusionAddEquiv_inverse_zeroMDS

theorem byteDiffusionHom_apply (inverse : Bool) (x : Fin 4 → Byte) :
    byteDiffusionHom inverse x = byteDiffusionOrientation inverse x := by
  cases inverse <;> rfl

theorem byte_shortened_code_action (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    action (coordinateKernel T)
      (codeIndicator (markedGraph (byteDiffusionHom inverse) r z marked)) y =
      256 * lineResponse T
        (lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z hshort marked hm) y := by
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using
    shortened_code_action (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z hshort marked hm T y

/-- The source's damped line vector divides the raw code response by m=256.
The unit-code convention used by CodeResponse instead divides by sqrt(m). -/
theorem byte_normalized_shortened_response (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    action (coordinateKernel T)
      (codeIndicator (markedGraph (byteDiffusionHom inverse) r z marked)) y / 256 =
      lineResponse T
        (lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z hshort marked hm) y := by
  rw [byte_shortened_code_action inverse r z hshort marked hm T y]
  ring

theorem byte_unit_shortened_response (inverse : Bool) (r z : Fin 16)
    (hshort : maskSize r + maskSize z = 3) (marked : Fin 3 → GraphPosition)
    (hm : ∀ i, remaining r z (marked i)) (T : Fin 3 → Byte → Byte → ℝ) (y : Fin 3 → Byte) :
    action (coordinateKernel T)
      (codeIndicator (markedGraph (byteDiffusionHom inverse) r z marked)) y /
        Real.sqrt (Fintype.card (ShortenedGraph (byteDiffusionHom inverse) r z)) =
      16 * lineResponse T
        (lineCoordinatePerm (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z hshort marked hm) y := by
  rw [byte_shortened_code_action inverse r z hshort marked hm T y,
    shortened_card (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) r z hshort]
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
  rw [show (256 : ℝ) = (16 : ℝ)^2 by norm_num, Real.sqrt_sq_eq_abs]
  norm_num <;> ring

/-- Zero-mask choices outside one fixed marked output triple. This counts
the choices; distinctness of their projected codes is a separate statement. -/
abbrev ShorteningChoice (out : Fin 16) (n : ℕ) :=
  {p : Fin 16 × Fin 16 // MaskDisjoint p.1 out ∧ maskSize p.1 + maskSize p.2 = n}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ten_line_choices : ∀ out : Fin 16, maskSize out = 3 →
    Fintype.card (ShorteningChoice out 3) = 10 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem ten_plane_choices : ∀ out : Fin 16, maskSize out = 3 →
    Fintype.card (ShorteningChoice out 2) = 10 := by decide

theorem plane_choice_cardinality
    {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (out : Fin 16)
    (p : ShorteningChoice out 2) :
    Fintype.card (ShortenedGraph L p.val.1 p.val.2) = Fintype.card V ^ 2 := by
  rw [mds_graph_zero_count L hL p.val.1 p.val.2, p.property.2]

end AESConcrete.ShortenedLineResponse
