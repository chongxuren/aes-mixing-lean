import AES8.Reductions.Return.PaperAESOverlapLarge

/-!
# All-orientation normalized AES information-set overlap

Frozen paper f902bb94, `eq:aesasm-overlap-large`. This leaf joins the
actual all-eight-orientation AES resources to the physical affine MDS
information-set theorem. Both outside indicator maps remain normalized
inside the literal operator. Complexification preserves the signed-real
proof by splitting real and imaginary parts.

The coefficient is first retained as the exact normalized collision
product. Rewriting it into the paper's factored real half powers is a
separate scalar obligation. Incidence factors, the physical state graph
join and the other overlap-menu branches are separate components.
No target norm, desired membership or input-distribution premise is used.
Constructive validation only; no attacks, numerical searches or paper edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESOverlapBound
open AESMixing AESConcrete PaperMDSGram PaperMDSOverlap PaperPhysicalOverlap
open PaperFiberKernel PaperKernelBounds PaperAESOverlapResources PaperAESOverlapLarge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

/-- Exactly the displayed nonnegative half-exponent coefficient. -/
def paperCoefficient (m s t a b : ℕ) : ℝ :=
  nu ^ (s + t - m) *
    Real.rpow delta ((m : ℝ) - ((s + t + a + b : ℕ) : ℝ) / 2) *
    Real.rpow (total / (q : ℝ)) (((a + b : ℕ) : ℝ) / 2)

/-- Scalar factoring of the normalized collision product. No operator is
identified or bounded by this algebraic identity. -/
theorem coefficient_eq_paperCoefficient (m s t a b : ℕ)
    (hs : s ≤ m) (ht : t ≤ m) (ha : a ≤ m - s) (hb : b ≤ m - t) :
    coefficient m s t a b = paperCoefficient m s t a b := by
  have hL : ((m - s - a : ℕ) : ℝ) = (m : ℝ) - (s : ℝ) - (a : ℝ) := by
    rw [Nat.cast_sub ha, Nat.cast_sub hs]
  have hR : ((m - t - b : ℕ) : ℝ) = (m : ℝ) - (t : ℝ) - (b : ℝ) := by
    rw [Nat.cast_sub hb, Nat.cast_sub ht]
  have hexp : (m : ℝ) - ((s + t + a + b : ℕ) : ℝ) / 2 =
      (((m - s - a + (m - t - b) : ℕ) : ℝ) / 2) := by
    simp only [Nat.cast_add, hL, hR]
    ring
  have hratio : 0 ≤ total / (q : ℝ) :=
    div_nonneg total_nonneg (Nat.cast_nonneg q)
  have hproduct : 0 ≤
      delta ^ (m - s - a) * total ^ a *
        (delta ^ (m - t - b) * total ^ b) / (q : ℝ) ^ (a + b) := by
    exact div_nonneg (mul_nonneg
      (mul_nonneg (pow_nonneg delta_nonneg _) (pow_nonneg total_nonneg _))
      (mul_nonneg (pow_nonneg delta_nonneg _) (pow_nonneg total_nonneg _)))
      (pow_nonneg (Nat.cast_nonneg q) _)
  have hdeltaSquare :
      Real.rpow delta (((m - s - a + (m - t - b) : ℕ) : ℝ) / 2) ^ (2 : ℕ) =
        delta ^ (m - s - a + (m - t - b)) := by
    calc
      _ = Real.rpow delta ((m - s - a + (m - t - b) : ℕ) : ℝ) :=
        PaperWholeGraphReturn.rpow_half_square delta _ delta_nonneg
      _ = _ := Real.rpow_natCast _ _
  have hratioSquare :
      Real.rpow (total / (q : ℝ)) (((a + b : ℕ) : ℝ) / 2) ^ (2 : ℕ) =
        (total / (q : ℝ)) ^ (a + b) := by
    calc
      _ = Real.rpow (total / (q : ℝ)) ((a + b : ℕ) : ℝ) :=
        PaperWholeGraphReturn.rpow_half_square _ _ hratio
      _ = _ := Real.rpow_natCast _ _
  have hfactor :
      Real.sqrt (delta ^ (m - s - a) * total ^ a *
        (delta ^ (m - t - b) * total ^ b) / (q : ℝ) ^ (a + b)) =
      Real.rpow delta (((m - s - a + (m - t - b) : ℕ) : ℝ) / 2) *
        Real.rpow (total / (q : ℝ)) (((a + b : ℕ) : ℝ) / 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg
      (Real.rpow_nonneg delta_nonneg _) (Real.rpow_nonneg hratio _))).mp
    rw [Real.sq_sqrt hproduct, mul_pow]
    change _ =
      Real.rpow delta (((m - s - a + (m - t - b) : ℕ) : ℝ) / 2) ^ (2 : ℕ) *
      Real.rpow (total / (q : ℝ)) (((a + b : ℕ) : ℝ) / 2) ^ (2 : ℕ)
    rw [hdeltaSquare, hratioSquare]
    simp only [div_pow, pow_add]
    ring
  unfold coefficient paperCoefficient
  rw [hexp, hfactor]
  ring

/-- Generic complexification of an arbitrary signed-real all-input norm cap. -/
theorem complex_kernel_norm_of_real_l2 {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (T : X → Y → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hreal : ∀ f : Y → ℝ, l2 (action T f) ≤ c * l2 f) :
    ‖kernelOperator (fun x y => (T x y : ℂ))‖ ≤ c := by
  have he : ∀ f : Y → ℝ,
      (∑ x : X, action T f x ^ 2) ≤ c ^ 2 * ∑ y : Y, f y ^ 2 := by
    intro f
    have hs : (l2 (action T f)) ^ 2 ≤ (c * l2 f) ^ 2 :=
      (sq_le_sq₀ (l2_nonneg (action T f)) (mul_nonneg hc (l2_nonneg f))).mpr (hreal f)
    simpa only [mul_pow, l2_sq] using hs
  have hcomplex : ∀ f : Y → ℂ,
      (∑ x : X, ‖kernelAction (fun x y => (T x y : ℂ)) f x‖ ^ 2) ≤
        c ^ 2 * ∑ y : Y, ‖f y‖ ^ 2 :=
    PaperWholeGraphReturn.complex_energy_of_real T (c ^ 2) he
  have hh : ‖kernelOperator (fun x y => (T x y : ℂ))‖ ^ 2 ≤ c ^ 2 :=
    operator_norm_sq_le_of_energy (fun x y => (T x y : ℂ)) (c ^ 2)
      (sq_nonneg c) hcomplex
  exact (sq_le_sq₀ (norm_nonneg _) hc).mp hh

/-- Complexification commutes with the literal two-fiber matrix compression. -/
theorem compressedKernel_complexification {C D X Y : Type*}
    [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (p : C → X) (r : D → Y)
    (m n : ℕ) (B : C → D → ℝ) :
    compressedKernel (𝕜 := ℂ) p r m n (fun c d => (B c d : ℂ)) =
      fun x y => ((compressedKernel (𝕜 := ℝ) p r m n B x y : ℝ) : ℂ) := by
  funext x y
  simp only [compressedKernel, Complex.ofReal_div, Complex.ofReal_mul]
  congr 1
  unfold rawCompression
  simp only [Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]

variable {KL KR M : Type*} [Fintype KL] [DecidableEq KL]
  [Fintype KR] [DecidableEq KR] [Fintype M] [DecidableEq M]

/-- Signed-real endpoint, with each collision factor in its proved low branch. -/
theorem information_overlap_real
    (CL : AddSubgroup (KL → AES.Word)) (CR : AddSubgroup (KR → AES.Word))
    (s t : ℕ) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (offL : KL → AES.Word) (offR : KR → AES.Word)
    (middleL : M ↪ KL) (middleR : M ↪ KR)
    (hs : s ≤ Fintype.card M) (ht : t ≤ Fintype.card M)
    (hst : Fintype.card M ≤ s + t)
    (outsideL : Finset KL) (outsideR : Finset KR)
    (hdL : Disjoint outsideL (Finset.univ.map middleL))
    (hdR : Disjoint outsideR (Finset.univ.map middleR))
    (ha : s - min s outsideL.card ≤ Fintype.card M - s)
    (hb : t - min t outsideR.card ≤ Fintype.card M - t)
    (adjoint eL eR : Bool) (f : OutsideLabel CR offR outsideR → ℝ) :
    l2 (physicalOverlap CL CR s t offL offR middleL middleR outsideL outsideR
      (fun _ => PaperWordMixedGram.mixed adjoint eL eR) f) ≤
      coefficient (Fintype.card M) s t (s - min s outsideL.card)
        (t - min t outsideR.card) * l2 f := by
  let T : M → AES.Word → AES.Word → ℝ :=
    fun _ => PaperWordMixedGram.mixed adjoint eL eR
  have hcol : ∀ i : M, ∀ x : AES.Word, (∑ y : AES.Word, T i y x ^ 2) ≤ delta :=
    fun _ x => mixed_column_energy adjoint eL eR x
  have hrow : ∀ i : M, ∀ y : AES.Word, (∑ x : AES.Word, T i y x ^ 2) ≤ delta :=
    fun _ y => mixed_row_energy adjoint eL eR y
  have htotal : ∀ i : M, (∑ uv : AES.Word × AES.Word, T i uv.1 uv.2 ^ 2) ≤ total := by
    intro i
    rw [Fintype.sum_prod_type]
    exact mixed_total_energy adjoint eL eR
  have hop : ∀ i : M, ∀ g : AES.Word → ℝ,
      (∑ y : AES.Word, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x : AES.Word, g x ^ 2 :=
    fun _ g => mixed_energy adjoint eL eR g
  have h := paper_mds_overlap_l2 (V := AES.Word) (M := M)
    CL CR s t hCL hCR offL offR hs ht hst middleL middleR outsideL outsideR hdL hdR
    T nu total delta nu_nonneg total_nonneg delta_nonneg hcol hrow htotal hop f
  calc
    _ ≤ (nu ^ (s + t - Fintype.card M) * Real.sqrt
        (PaperMDSFiber.collisionBound (Fintype.card AES.Word) (Fintype.card M - s)
          (s - min s outsideL.card) total delta *
        PaperMDSFiber.collisionBound (Fintype.card AES.Word) (Fintype.card M - t)
          (t - min t outsideR.card) total delta /
        (Fintype.card AES.Word : ℝ) ^
          ((s - min s outsideL.card) + (t - min t outsideR.card)))) * l2 f := h
    _ = _ := by
      congr 1
      simp only [coefficient, PaperMDSFiber.collisionBound, if_pos ha, if_pos hb,
        WordFourierCore.word_card, q]

/-- The literal complex Hilbert operator; every complex input is permitted. -/
theorem information_overlap_norm
    (CL : AddSubgroup (KL → AES.Word)) (CR : AddSubgroup (KR → AES.Word))
    (s t : ℕ) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (offL : KL → AES.Word) (offR : KR → AES.Word)
    (middleL : M ↪ KL) (middleR : M ↪ KR)
    (hs : s ≤ Fintype.card M) (ht : t ≤ Fintype.card M)
    (hst : Fintype.card M ≤ s + t)
    (outsideL : Finset KL) (outsideR : Finset KR)
    (hdL : Disjoint outsideL (Finset.univ.map middleL))
    (hdR : Disjoint outsideR (Finset.univ.map middleR))
    (ha : s - min s outsideL.card ≤ Fintype.card M - s)
    (hb : t - min t outsideR.card ≤ Fintype.card M - t)
    (adjoint eL eR : Bool) :
    ‖overlap CL CR s t offL offR middleL middleR outsideL outsideR adjoint eL eR‖ ≤
      coefficient (Fintype.card M) s t (s - min s outsideL.card)
        (t - min t outsideR.card) := by
  let T : M → AES.Word → AES.Word → ℝ :=
    fun _ => PaperWordMixedGram.mixed adjoint eL eR
  let B : AffineCode CL offL → AffineCode CR offR → ℝ :=
    physicalMiddleKernel CL CR offL offR middleL middleR T
  let p := outsideProjection CL offL outsideL
  let r := outsideProjection CR offR outsideR
  let a : ℕ := q ^ (s - min s outsideL.card)
  let b : ℕ := q ^ (t - min t outsideR.card)
  have hreal : ∀ f : OutsideLabel CR offR outsideR → ℝ,
      l2 (action (compressedKernel p r a b B) f) ≤
        coefficient (Fintype.card M) s t (s - min s outsideL.card)
          (t - min t outsideR.card) * l2 f := by
    intro f
    have heq := physicalOverlap_eq_compressed_action CL CR s t offL offR
      middleL middleR outsideL outsideR T f
    have hbound := information_overlap_real CL CR s t hCL hCR offL offR middleL middleR
      hs ht hst outsideL outsideR hdL hdR ha hb adjoint eL eR f
    rw [heq] at hbound
    exact hbound
  have hnorm : ‖kernelOperator
      (fun x y => ((compressedKernel (𝕜 := ℝ) p r a b B x y : ℝ) : ℂ))‖ ≤
      coefficient (Fintype.card M) s t (s - min s outsideL.card)
        (t - min t outsideR.card) :=
    complex_kernel_norm_of_real_l2 (compressedKernel p r a b B) _
      (coefficient_nonneg _ _ _ _ _) hreal
  rw [← compressedKernel_complexification, compression_eq_adjoint_comp] at hnorm
  exact hnorm

/-- The factored expression in the frozen paper bounds the same normalized
operator; its half exponents are real, with no truncated subtraction. -/
theorem information_overlap_paper_norm
    (CL : AddSubgroup (KL → AES.Word)) (CR : AddSubgroup (KR → AES.Word))
    (s t : ℕ) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (offL : KL → AES.Word) (offR : KR → AES.Word)
    (middleL : M ↪ KL) (middleR : M ↪ KR)
    (hs : s ≤ Fintype.card M) (ht : t ≤ Fintype.card M)
    (hst : Fintype.card M ≤ s + t)
    (outsideL : Finset KL) (outsideR : Finset KR)
    (hdL : Disjoint outsideL (Finset.univ.map middleL))
    (hdR : Disjoint outsideR (Finset.univ.map middleR))
    (ha : s - min s outsideL.card ≤ Fintype.card M - s)
    (hb : t - min t outsideR.card ≤ Fintype.card M - t)
    (adjoint eL eR : Bool) :
    ‖overlap CL CR s t offL offR middleL middleR outsideL outsideR adjoint eL eR‖ ≤
      paperCoefficient (Fintype.card M) s t (s - min s outsideL.card)
        (t - min t outsideR.card) := by
  exact (information_overlap_norm CL CR s t hCL hCR offL offR middleL middleR hs ht hst
    outsideL outsideR hdL hdR ha hb adjoint eL eR).trans_eq
      (coefficient_eq_paperCoefficient _ _ _ _ _ hs ht ha hb)

section ReducedReturnDomain
open PaperReturnDimensions PaperGraphResponseMatrix

def middleEmbedding (I M : Type*) : M ↪ I ⊕ M :=
  ⟨Sum.inr, Sum.inr_injective⟩

theorem outside_middle_disjoint {I N : Type*} [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N] :
    Disjoint (leftPositions (I := I) (M := N))
      (Finset.univ.map (middleEmbedding I N)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hmiddle
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hmiddle
  exact not_mem_leftPositions_inr x hp

/-- For the actual reduced AES return dimensions, both low-branch fiber
conditions and both middle information-set size conditions are derived.
Only applicability of the large menu branch remains an inequality premise. -/
theorem reduced_information_overlap_norm {i j m dL dR : ℕ}
    (hi : i ≤ 4) (hj : j ≤ 4) (hm : 3 ≤ m)
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → AES.Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → AES.Word))
    (hCL : IsMDS CL (reduced (i + m) dL))
    (hCR : IsMDS CR (reduced (j + m) dR))
    (hlarge : m ≤ reduced (i + m) dL + reduced (j + m) dR)
    (offL : (Fin i ⊕ Fin m) → AES.Word) (offR : (Fin j ⊕ Fin m) → AES.Word)
    (adjoint eL eR : Bool) :
    ‖overlap CL CR (reduced (i + m) dL) (reduced (j + m) dR) offL offR
      (middleEmbedding (Fin i) (Fin m)) (middleEmbedding (Fin j) (Fin m))
      (leftPositions (I := Fin i) (M := Fin m))
      (leftPositions (I := Fin j) (M := Fin m)) adjoint eL eR‖ ≤
      paperCoefficient m (reduced (i + m) dL) (reduced (j + m) dR)
        (fiberDimension i (reduced (i + m) dL))
        (fiberDimension j (reduced (j + m) dR)) := by
  have hs : reduced (i + m) dL ≤ Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using reduced_le_middle (d := dL) hi hm
  have ht : reduced (j + m) dR ≤ Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using reduced_le_middle (d := dR) hj hm
  have ha : reduced (i + m) dL -
      min (reduced (i + m) dL) (leftPositions (I := Fin i) (M := Fin m)).card ≤
        Fintype.card (Fin m) - reduced (i + m) dL := by
    simpa only [leftPositions_card, Fintype.card_fin, fiberDimension, min_comm]
      using reduced_fiber_bound (d := dL) hi hm
  have hb : reduced (j + m) dR -
      min (reduced (j + m) dR) (leftPositions (I := Fin j) (M := Fin m)).card ≤
        Fintype.card (Fin m) - reduced (j + m) dR := by
    simpa only [leftPositions_card, Fintype.card_fin, fiberDimension, min_comm]
      using reduced_fiber_bound (d := dR) hj hm
  have h := information_overlap_paper_norm CL CR _ _ hCL hCR offL offR
    (middleEmbedding (Fin i) (Fin m)) (middleEmbedding (Fin j) (Fin m)) hs ht
    (by simpa only [Fintype.card_fin] using hlarge)
    (leftPositions (I := Fin i) (M := Fin m))
    (leftPositions (I := Fin j) (M := Fin m))
    outside_middle_disjoint outside_middle_disjoint ha hb adjoint eL eR
  calc
    _ ≤ paperCoefficient (Fintype.card (Fin m)) (reduced (i + m) dL) (reduced (j + m) dR)
        (reduced (i + m) dL -
          min (reduced (i + m) dL) (leftPositions (I := Fin i) (M := Fin m)).card)
        (reduced (j + m) dR -
          min (reduced (j + m) dR) (leftPositions (I := Fin j) (M := Fin m)).card) := h
    _ = _ := by simp only [leftPositions_card, Fintype.card_fin, fiberDimension, min_comm]

end ReducedReturnDomain

end AES8.PaperAESOverlapBound
