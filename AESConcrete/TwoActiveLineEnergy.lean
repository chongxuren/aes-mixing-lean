import AESConcrete.GraphColumnEnergy
import AESConcrete.WeightedResponse
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound

/-!
# Signed two-retained-coordinate line responses

A bijective projection of the actual curve supplies its free coordinate. The
other retained coordinate is then an explicit graph over it. Both original
retained labels remain in the output space, and both output and input sums are
transported by equivalences with exact counting measure. The amplitude is one
arbitrary signed function; it is not normalized or restricted at zero.

The MDS geometry that proves the projection bijective is a separate premise.
Constructive mathematics only; no attacks. Independent uniform retained keys,
whitening, omitted final MixColumns, ordered-distinct pairs and the fixed
10/14/16 target remain unchanged. No physical cap, inventory admission,
compilation or independent review is asserted by this source alone.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoActiveLineEnergy
open AESMixing

section ActualLabels
variable {I V : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- A two-label output has a unique label other than the chosen free label.
The original labels, rather than their enumeration, are returned. -/
theorem exists_other_label (hI : Fintype.card I = 2) (s : I) :
    ∃ t : I, t ≠ s ∧ ∀ i : I, i = s ∨ i = t := by
  classical
  let e : I ≃ Fin 2 := Fintype.equivOfCardEq (by simpa using hI)
  have hfin : ∀ a : Fin 2, ∃ b : Fin 2, b ≠ a ∧ ∀ c : Fin 2, c = a ∨ c = b :=
    by decide
  obtain ⟨b, hb, hcover⟩ := hfin (e s)
  refine ⟨e.symm b, ?_, ?_⟩
  · intro he
    apply hb
    simpa using congrArg e he
  · intro i
    rcases hcover (e i) with hi | hi
    · exact Or.inl (e.injective hi)
    · exact Or.inr (e.injective (by simpa using hi))

/-- Dependent coordinate first, free coordinate second, matching graphKernel.
The equivalence preserves the original two physical labels. -/
def pairCoordinates (s t : I) (hts : t ≠ s)
    (hcover : ∀ i : I, i = s ∨ i = t) : (I → V) ≃ V × V where
  toFun y := (y t, y s)
  invFun y := fun i => if i = t then y.1 else y.2
  left_inv y := by
    funext i
    rcases hcover i with hi | hi
    · subst i
      simp [Ne.symm hts]
    · subst i
      simp
  right_inv y := by
    apply Prod.ext
    · simp
    · simp [Ne.symm hts]

/-- Exact product split on the original pair of retained labels. -/
theorem prod_two_labels (s t : I) (hts : t ≠ s)
    (hcover : ∀ i : I, i = s ∨ i = t) (f : I → ℝ) :
    (∏ i : I, f i) = f t * f s := by
  have hu : (Finset.univ : Finset I) = {t, s} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact (hcover i).symm
  simp [hu, hts]

end ActualLabels

section Curve
variable {I V C : Type*} [Fintype I] [DecidableEq I] [Fintype C]

/-- Raw signed curve response, with no uniform or input normalization. -/
def curveResponse (T : V → V → ℝ) (curve : C → I → V) (μ : C → ℝ)
    (y : I → V) : ℝ :=
  ∑ c, μ c * ∏ i : I, T (y i) (curve c i)

variable [Fintype V]

/-- Reindex only the curve source. The free-coordinate equivalence creates
an actual graph and keeps the same signed amplitude at every source point. -/
theorem curveResponse_eq_graph (s t : I) (hts : t ≠ s)
    (hcover : ∀ i : I, i = s ∨ i = t)
    (T : V → V → ℝ) (curve : C → I → V) (μ : C → ℝ)
    (e : C ≃ V) (he : ∀ c, e c = curve c s) (y : I → V) :
    curveResponse T curve μ y =
      action (GraphColumnEnergy.graphKernel T T (fun v => curve (e.symm v) t))
        (fun v => μ (e.symm v)) (y t, y s) := by
  unfold curveResponse
  rw [← e.symm.sum_comp (fun c => μ c * ∏ i : I, T (y i) (curve c i))]
  unfold action GraphColumnEnergy.graphKernel
  apply Finset.sum_congr rfl
  intro v _
  have hs : curve (e.symm v) s = v :=
    (he (e.symm v)).symm.trans (e.apply_symm_apply v)
  rw [prod_two_labels s t hts hcover, hs]
  ring

/-- The source amplitude has exactly the same counting energy after the
bijective free-coordinate reindexing. -/
theorem reindexed_amplitude_energy (e : C ≃ V) (μ : C → ℝ) :
    (∑ v : V, μ (e.symm v) ^ 2) = ∑ c : C, μ c ^ 2 :=
  e.symm.sum_comp (fun c => μ c ^ 2)

/-- One operator-energy bound and one column-energy bound control every
signed two-coordinate curve with a bijective retained projection. -/
theorem curve_energy_of_equiv (hI : Fintype.card I = 2) (s : I)
    (T : V → V → ℝ) (curve : C → I → V) (μ : C → ℝ)
    (e : C ≃ V) (he : ∀ c, e c = curve c s)
    (ρ κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ f : V → ℝ, (∑ y, action T f y ^ 2) ≤ ρ ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ κ) :
    (∑ y : I → V, curveResponse T curve μ y ^ 2) ≤
      ρ ^ 2 * κ * ∑ c : C, μ c ^ 2 := by
  obtain ⟨t, hts, hcover⟩ := exists_other_label hI s
  let G := GraphColumnEnergy.graphKernel T T (fun v => curve (e.symm v) t)
  let ν : V → ℝ := fun v => μ (e.symm v)
  have hout : (∑ y : I → V, curveResponse T curve μ y ^ 2) =
      ∑ y : V × V, action G ν y ^ 2 := by
    simp_rw [curveResponse_eq_graph s t hts hcover T curve μ e he]
    exact (pairCoordinates (V := V) s t hts hcover).sum_comp
      (fun y => action G ν y ^ 2)
  have hsqrt : (Real.sqrt κ) ^ 2 = κ := Real.sq_sqrt hκ
  have hcolumn' : ∀ v : V, (∑ y, T y v ^ 2) ≤ (Real.sqrt κ) ^ 2 := by
    intro v
    simpa only [hsqrt] using hcolumn v
  have hb := GraphColumnEnergy.graphKernel_energy T T
    (fun v => curve (e.symm v) t) ρ (Real.sqrt κ) hT hcolumn' ν
  rw [hsqrt, reindexed_amplitude_energy e μ] at hb
  rw [hout]
  exact hb

/-- A bijectivity proof of the retained projection supplies its equivalence.
No coordinate of the curve is asserted to be uniform or independent. -/
theorem curve_energy_of_bijective (hI : Fintype.card I = 2) (s : I)
    (T : V → V → ℝ) (curve : C → I → V) (μ : C → ℝ)
    (hprojection : Function.Bijective (fun c : C => curve c s))
    (ρ κ : ℝ) (hκ : 0 ≤ κ)
    (hT : ∀ f : V → ℝ, (∑ y, action T f y ^ 2) ≤ ρ ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ κ) :
    (∑ y : I → V, curveResponse T curve μ y ^ 2) ≤
      ρ ^ 2 * κ * ∑ c : C, μ c ^ 2 :=
  curve_energy_of_equiv hI s T curve μ
    (Equiv.ofBijective (fun c : C => curve c s) hprojection) (fun _ => rfl)
    ρ κ hκ hT hcolumn

end Curve

section ZeroRestriction
variable {S Y V : Type*} [Fintype S] [Zero V] [DecidableEq V]

/-- A zero-indicator response is exactly the subtype sum on that zero locus.
The original amplitude and residual product are evaluated without change. -/
theorem zeroResponse_eq_subtype (h : S → ℝ) (K : Y → S → ℝ)
    (c : S → V) (y : Y) :
    WeightedResponse.zeroResponse h K c y =
      ∑ x : {x : S // c x = 0}, h x.val * K y x.val := by
  classical
  unfold WeightedResponse.zeroResponse
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The same exact restriction already in the raw curve-response interface.
There is no source-fiber factor or additional zero-point exclusion. -/
theorem zeroResponse_eq_curve {I : Type*} [Fintype I]
    (T : V → V → ℝ) (curve : S → I → V) (h : S → ℝ)
    (c : S → V) (y : I → V) :
    WeightedResponse.zeroResponse h
      (fun y x => ∏ i : I, T (y i) (curve x i)) c y =
      curveResponse T (fun x : {x : S // c x = 0} => curve x.val)
        (fun x => h x.val) y := by
  classical
  exact zeroResponse_eq_subtype h _ c y

end ZeroRestriction

section ActualWord
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]

/-- Actual ordinary AES-word residual resources, with all physical retained
labels and the arbitrary signed curve amplitude preserved. -/
theorem word_curve_energy_of_bijective (hI : Fintype.card I = 2) (s : I)
    (curve : C → I → AES.Word) (μ : C → ℝ)
    (hprojection : Function.Bijective (fun c : C => curve c s)) :
    (∑ y : I → AES.Word,
      curveResponse (residualMatrix AES.wordSuperboxKernel 0) curve μ y ^ 2) ≤
      ((21 / 131072 : ℝ) ^ 2 * (2 / (15 * 4294967296))) * ∑ c : C, μ c ^ 2 :=
  curve_energy_of_bijective hI s (residualMatrix AES.wordSuperboxKernel 0) curve μ
    hprojection (21 / 131072) (2 / (15 * 4294967296)) (by norm_num)
    SharpDampedWordNorm.word_superbox_residual_energy
    (fun v => (AllColumnBound.actual_word_residual_column_energy_lt v).le)

end ActualWord
end AESConcrete.TwoActiveLineEnergy
