/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.ZeroOutsideProjection
import AES8.Reductions.Fibers.PairedWordMixFiber
import AES8.Math.PairedFiberEnergy
import AESMixing.ProjectionGram

/-!
# A zero/nonzero-constant activity average and its literal paired fiber

The output-coordinate projection is Z_c C_d I_a I_b. Here C_d is precisely
`constantMatrix 0`, the nonzero constant direction, and never the full
`activityMatrix 0`. Symmetric idempotence gives its exact quadratic energy.
The literal projection kernel then selects the full paired boundary fiber
and retains both nonzero d endpoints. Its normalization is (q-1)^{-1}.

The signed common-source response is expanded without changing its labels
or weights. The existing restricted-pair Cauchy theorem supplies the bound;
the actual forward wordMix geometry discharges both information bijections.
No output-nine conclusion, residual-pattern contraction, orthogonal pattern
count, actual-source identification or numerical AES cap is asserted here.

  No Lean/scientific execution, active-source/root/Audit
edits, attacks, manuscript changes or predecessor edits in this branch.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ActivityAverageEnergy
open AESMixing AESMixing.AES

section ProjectionInner
variable {X : Type*} [Fintype X]

/-- Counting energy of an arbitrary symmetric idempotent kernel is its
quadratic form. No positivity of the signed input is required. -/
theorem symmetric_idempotent_energy (P : X → X → ℝ)
    (hs : ∀ x y, P x y = P y x) (hi : kernelCompose P P = P) (f : X → ℝ) :
    (∑ y, action P f y ^ 2) = ∑ x, ∑ z, f x * f z * P x z := by
  have hg (x z : X) : (∑ y, P y x * P y z) = P x z :=
    projection_gram P hs hi x z
  simp only [pow_two]
  rw [kernel_bilinear]
  simp_rw [hg]

end ProjectionInner

section OutputProjection
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def denominator (V : Type*) [Fintype V] : ℝ := (Fintype.card V : ℝ) - 1

theorem denominator_pos (hn : 1 < Fintype.card V) : 0 < denominator V := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  unfold denominator
  linarith

/-- Only c and d are projected; every other output coordinate is unchanged. -/
def coordinatePiece (c d i : Fin 4) : V → V → ℝ :=
  if i = c then zeroMatrix 0 else if i = d then constantMatrix 0 else identityKernel

def kernel (c d : Fin 4) : (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  coordinateKernel (coordinatePiece c d)

def projection (c d : Fin 4) (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  action (kernel c d) f

private theorem coordinatePiece_symmetric (c d i : Fin 4) (x y : V) :
    coordinatePiece c d i x y = coordinatePiece c d i y x := by
  by_cases hic : i = c
  · simpa [coordinatePiece, hic, supportPiece] using
      (supportPiece_symmetric (0 : V) false true x y)
  · by_cases hid : i = d
    · subst i
      simpa [coordinatePiece, hic, supportPiece] using
        (supportPiece_symmetric (0 : V) false false x y)
    · simp [coordinatePiece, hic, hid, identityKernel, eq_comm]

private theorem identityKernel_compose :
    kernelCompose (identityKernel : V → V → ℝ) identityKernel = identityKernel := by
  funext y x
  simp [kernelCompose, identityKernel]

private theorem coordinatePiece_idempotent (hn : 1 < Fintype.card V)
    (c d i : Fin 4) :
    kernelCompose (coordinatePiece c d i : V → V → ℝ) (coordinatePiece c d i) =
      coordinatePiece c d i := by
  by_cases hic : i = c
  · simpa [coordinatePiece, hic, supportPiece] using
      (supportPiece_compose (0 : V) hn false true true)
  · by_cases hid : i = d
    · subst i
      simpa [coordinatePiece, hic, supportPiece] using
        (supportPiece_compose (0 : V) hn false false false)
    · simpa [coordinatePiece, hic, hid] using (identityKernel_compose (V := V))

theorem kernel_symmetric (c d : Fin 4) (x y : Fin 4 → V) :
    kernel c d x y = kernel c d y x := by
  unfold kernel coordinateKernel
  apply Finset.prod_congr rfl
  intro i _
  exact coordinatePiece_symmetric c d i (x i) (y i)

theorem kernel_idempotent (hn : 1 < Fintype.card V) (c d : Fin 4) :
    kernelCompose (kernel c d : (Fin 4 → V) → (Fin 4 → V) → ℝ) (kernel c d) =
      kernel c d := by
  unfold kernel
  rw [coordinateKernel_compose]
  funext y x
  unfold coordinateKernel
  apply Finset.prod_congr rfl
  intro i _
  exact congrFun (congrFun (coordinatePiece_idempotent hn c d i) (y i)) (x i)

theorem projection_energy_inner (hn : 1 < Fintype.card V) (c d : Fin 4)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, projection c d f y ^ 2) =
      ∑ x, ∑ z, f x * f z * kernel c d x z :=
  symmetric_idempotent_energy (kernel c d) (kernel_symmetric c d)
    (kernel_idempotent hn c d) f

/-- Explicitly distinguishes the nonzero constant block from activityMatrix. -/
theorem constantMatrix_literal (x y : V) :
    constantMatrix (0 : V) x y =
      if x ≠ 0 ∧ y ≠ 0 then (denominator V)⁻¹ else 0 := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [constantMatrix, activityMatrix, zeroMatrix, identityKernel,
      denominator, hx, hy, one_div]

abbrev pairCondition (c d : Fin 4) (y x : Fin 4 → V) : Prop :=
  y c = 0 ∧ x c = 0 ∧ ∀ j : Fin 4, j ≠ c → j ≠ d → y j = x j

abbrev nonzeroEndpoints (d : Fin 4) (y x : Fin 4 → V) : Prop :=
  y d ≠ 0 ∧ x d ≠ 0

/-- Literal kernel support, including BOTH nonzero d endpoints. -/
theorem kernel_literal (c d : Fin 4) (hcd : c ≠ d) (y x : Fin 4 → V) :
    kernel c d y x =
      if pairCondition c d y x ∧ nonzeroEndpoints d y x then
        (denominator V)⁻¹ else 0 := by
  have hdc : d ≠ c := Ne.symm hcd
  by_cases hg : pairCondition c d y x ∧ nonzeroEndpoints d y x
  · rw [if_pos hg]
    unfold kernel coordinateKernel
    calc
      _ = coordinatePiece c d d (y d) (x d) := by
        apply Finset.prod_eq_single d
        · intro j _ hjd
          by_cases hjc : j = c
          · subst j
            simp [coordinatePiece, zeroMatrix, identityKernel, hg.1.1, hg.1.2.1]
          · simp [coordinatePiece, hjc, hjd, identityKernel, hg.1.2.2 j hjc hjd]
        · simp
      _ = (denominator V)⁻¹ := by
        simp [coordinatePiece, hdc, constantMatrix_literal, hg.2.1, hg.2.2]
  · rw [if_neg hg]
    unfold kernel coordinateKernel
    have hz : ∃ i : Fin 4, coordinatePiece c d i (y i) (x i) = 0 := by
      by_cases hyc : y c = 0
      · by_cases hxc : x c = 0
        · by_cases hyd : y d = 0
          · exact ⟨d, by simp [coordinatePiece, hdc, constantMatrix_literal, hyd]⟩
          · by_cases hxd : x d = 0
            · exact ⟨d, by simp [coordinatePiece, hdc, constantMatrix_literal, hxd]⟩
            · by_cases he : ∀ j : Fin 4, j ≠ c → j ≠ d → y j = x j
              · exact (hg ⟨⟨hyc, hxc, he⟩, hyd, hxd⟩).elim
              · push_neg at he
                obtain ⟨j, hjc, hjd, hne⟩ := he
                exact ⟨j, by simp [coordinatePiece, hjc, hjd, identityKernel, hne]⟩
        · exact ⟨c, by simp [coordinatePiece, zeroMatrix, identityKernel, hxc]⟩
      · exact ⟨c, by simp [coordinatePiece, zeroMatrix, identityKernel, hyc]⟩
    obtain ⟨i, hi⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi

end OutputProjection

section BoundaryPair
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- A density transported by the forward boundary is read through its inverse. -/
def transport (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (f : (Fin 4 → V) → ℝ)
    (y : Fin 4 → V) : ℝ := f (L.symm y)

abbrev BoundaryPair (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (c d : Fin 4) :=
  PairedWordMixFiber.Pair L.toAddMonoidHom c d

abbrev allowed (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (d : Fin 4)
    {c : Fin 4} (p : BoundaryPair L c d) : Prop :=
  nonzeroEndpoints d (L p.val.1) (L p.val.2)

/-- An exact signed cross sum on the full paired domain with its event retained. -/
def pairedCross (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (c d : Fin 4)
    (f : (Fin 4 → V) → ℝ) : ℝ :=
  ∑ p : BoundaryPair L c d, if allowed L d p then f p.val.1 * f p.val.2 else 0

private theorem sum_pairCondition (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (c d : Fin 4) (F : (Fin 4 → V) → (Fin 4 → V) → ℝ) :
    (∑ g, ∑ h, if pairCondition c d (L g) (L h) then F g h else 0) =
      ∑ p : BoundaryPair L c d, F p.val.1 p.val.2 := by
  calc
    _ = ∑ p : (Fin 4 → V) × (Fin 4 → V),
        if pairCondition c d (L p.1) (L p.2) then F p.1 p.2 else 0 := by
      rw [Fintype.sum_prod_type]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp [pairCondition]) _

/-- The indicator formulation is exactly the subtype with both d values nonzero. -/
theorem pairedCross_eq_restrictedPair
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (c d : Fin 4) (f : (Fin 4 → V) → ℝ) :
    pairedCross L c d f =
      ∑ p : PairedWordMixFiber.RestrictedPair L.toAddMonoidHom c d,
        f p.val.val.1 * f p.val.val.2 := by
  unfold pairedCross
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp [allowed, nonzeroEndpoints]) _

/-- Exact activity-average energy. The boundary is forward L, and the input
density is transported by L.symm. No MDS hypothesis is needed for this identity. -/
theorem transport_energy_eq_pairedCross
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hn : 1 < Fintype.card V)
    (c d : Fin 4) (hcd : c ≠ d) (f : (Fin 4 → V) → ℝ) :
    (∑ y, projection c d (transport L f) y ^ 2) =
      (denominator V)⁻¹ * pairedCross L c d f := by
  rw [projection_energy_inner hn]
  have hreindex :
      (∑ y, ∑ x, transport L f y * transport L f x * kernel c d y x) =
        ∑ g, ∑ h, f g * f h * kernel c d (L g) (L h) := by
    rw [← L.toEquiv.sum_comp
      (fun y => ∑ x, transport L f y * transport L f x * kernel c d y x)]
    change (∑ g, ∑ x, f (L.symm (L g)) * f (L.symm x) * kernel c d (L g) x) = _
    simp only [L.symm_apply_apply]
    apply Finset.sum_congr rfl
    intro g _
    rw [← L.toEquiv.sum_comp
      (fun x => f g * f (L.symm x) * kernel c d (L g) x)]
    change (∑ h, f g * f (L.symm (L h)) * kernel c d (L g) (L h)) = _
    simp only [L.symm_apply_apply]
  rw [hreindex]
  have hw (g h : Fin 4 → V) :
      f g * f h * kernel c d (L g) (L h) =
        (denominator V)⁻¹ *
          (if pairCondition c d (L g) (L h) then
            (if nonzeroEndpoints d (L g) (L h) then f g * f h else 0) else 0) := by
    rw [kernel_literal c d hcd]
    split_ifs <;> simp_all <;> ring
  simp_rw [hw, ← Finset.mul_sum]
  rw [sum_pairCondition]
  rfl

theorem transport_energy_eq_restrictedPair
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hn : 1 < Fintype.card V)
    (c d : Fin 4) (hcd : c ≠ d) (f : (Fin 4 → V) → ℝ) :
    (∑ y, projection c d (transport L f) y ^ 2) =
      (denominator V)⁻¹ *
        ∑ p : PairedWordMixFiber.RestrictedPair L.toAddMonoidHom c d,
          f p.val.val.1 * f p.val.val.2 := by
  rw [transport_energy_eq_pairedCross L hn c d hcd, pairedCross_eq_restrictedPair]

end BoundaryPair

section SignedResponse
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- All four response legs retain their common original source label. -/
def response (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V)
    (mu : V → ℝ) (y : Fin 4 → V) : ℝ :=
  ∑ x, mu x * ∏ i : Fin 4, T i (y i) (e i x)

theorem pairedCross_response_eq
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (c d : Fin 4)
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V) (mu : V → ℝ) :
    pairedCross L c d (response T e mu) =
      PairedFiberEnergy.restrictedCross T e
        (fun p : BoundaryPair L c d => p.val.1) (fun p => p.val.2)
        (allowed L d) mu := by
  have hex (p : BoundaryPair L c d) :
      (if allowed L d p then response T e mu p.val.1 * response T e mu p.val.2 else 0) =
        ∑ x, ∑ z, if allowed L d p then mu x * mu z *
          ∏ i : Fin 4, T i (p.val.1 i) (e i x) * T i (p.val.2 i) (e i z) else 0 := by
    by_cases hp : allowed L d p
    · simp only [if_pos hp]
      unfold response
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.prod_mul_distrib]
      ring
    · simp only [if_neg hp, Finset.sum_const_zero]
  unfold pairedCross PairedFiberEnergy.restrictedCross
  simp_rw [hex]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.sum_comm

/-- Exact signed cross identity with normalization (q-1)^{-1}. Both nonzero
endpoint restrictions remain inside restrictedCross before Cauchy is used. -/
theorem transport_response_energy_eq
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hn : 1 < Fintype.card V)
    (c d : Fin 4) (hcd : c ≠ d)
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V) (mu : V → ℝ) :
    (∑ y, projection c d (transport L (response T e mu)) y ^ 2) =
      (denominator V)⁻¹ * PairedFiberEnergy.restrictedCross T e
        (fun p : BoundaryPair L c d => p.val.1) (fun p => p.val.2)
        (allowed L d) mu := by
  rw [transport_energy_eq_pairedCross L hn c d hcd, pairedCross_response_eq]

theorem transport_response_energy_le
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hn : 1 < Fintype.card V)
    (c d : Fin 4) (hcd : c ≠ d)
    (T : Fin 4 → V → V → ℝ) (e : Fin 4 → Equiv.Perm V) (mu : V → ℝ)
    (hinfoL : Function.Bijective (fun p : BoundaryPair L c d =>
      (p.val.1 0, (p.val.2 1, (p.val.2 2, p.val.2 3)))))
    (hinfoR : Function.Bijective (fun p : BoundaryPair L c d =>
      (p.val.2 0, (p.val.1 1, (p.val.1 2, p.val.1 3)))))
    (p delta tau : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    (∑ y, projection c d (transport L (response T e mu)) y ^ 2) ≤
      p ^ 2 * delta ^ 2 * tau ^ 2 / denominator V := by
  rw [transport_response_energy_eq L hn c d hcd]
  have hc := PairedFiberEnergy.restrictedCross_le T e
    (fun h : BoundaryPair L c d => h.val.1) (fun h => h.val.2)
    (allowed L d) mu hinfoL hinfoR p delta tau hp hd ht hmu hcolumn htrace
  calc
    _ ≤ (denominator V)⁻¹ * (p ^ 2 * delta ^ 2 * tau ^ 2) :=
      mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (denominator_pos hn).le)
    _ = _ := by rw [div_eq_mul_inv, _root_.mul_comm]

end SignedResponse

section ActualOrdinary
open AESConcrete.WordCrossZero

/-- Exact signed energy on the literal restricted actual paired domain. -/
theorem wordMix_energy_eq_restrictedPair (c d : Fin 4) (hcd : c ≠ d)
    (f : AES.WordState → ℝ) :
    (∑ y, projection c d (fun z => f (wordMixAddEquiv.symm z)) y ^ 2) =
      (denominator AES.Word)⁻¹ *
        ∑ p : PairedWordMixFiber.D c d, f p.val.val.1 * f p.val.val.2 :=
  transport_energy_eq_restrictedPair wordMixAddEquiv SupportProfile.word_card_gt_one
    c d hcd f

/-- The exact ordinary wordMix identity; density transport uses the inverse
of the same forward physical map appearing in the paired-fiber constraints. -/
theorem wordMix_response_energy_eq (c d : Fin 4) (hcd : c ≠ d)
    (T : Fin 4 → AES.Word → AES.Word → ℝ) (e : Fin 4 → Equiv.Perm AES.Word)
    (mu : AES.Word → ℝ) :
    (∑ y, projection c d
      (fun z => response T e mu (wordMixAddEquiv.symm z)) y ^ 2) =
      (denominator AES.Word)⁻¹ * PairedFiberEnergy.restrictedCross T e
        (fun p : PairedWordMixFiber.H c d => p.val.1) (fun p => p.val.2)
        (allowed wordMixAddEquiv d) mu :=
  transport_response_energy_eq wordMixAddEquiv SupportProfile.word_card_gt_one
    c d hcd T e mu

/-- Per-pattern activity-average bound. No output-nine or 12-pattern statement. -/
theorem wordMix_response_energy_le (c d : Fin 4) (hcd : c ≠ d)
    (T : Fin 4 → AES.Word → AES.Word → ℝ) (e : Fin 4 → Equiv.Perm AES.Word)
    (mu : AES.Word → ℝ) (p delta tau : ℝ)
    (hp : 0 ≤ p) (hd : 0 ≤ delta) (ht : 0 ≤ tau)
    (hmu : ∀ x, |mu x| ≤ p)
    (hcolumn : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (htrace : ∀ i, (∑ y, ∑ x, T i y x ^ 2) ≤ tau) :
    (∑ y, projection c d
      (fun z => response T e mu (wordMixAddEquiv.symm z)) y ^ 2) ≤
      p ^ 2 * delta ^ 2 * tau ^ 2 / denominator AES.Word :=
  transport_response_energy_le wordMixAddEquiv SupportProfile.word_card_gt_one
    c d hcd T e mu (PairedWordMixFiber.coordsZero_bijective c d hcd)
    (PairedWordMixFiber.swappedCoordsZero_bijective c d hcd)
    p delta tau hp hd ht hmu hcolumn htrace

end ActualOrdinary
end AES8.ActivityAverageEnergy
