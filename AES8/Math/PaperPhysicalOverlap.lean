/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperMDSOverlap
import AES8.Math.PaperInformationOverlap
import AES8.Math.PaperMDSCoordinateSplit
import AES8.Math.PaperFiberTransport

/-!
# Lemma 8 on physical coordinates of two larger MDS graphs

The retained information sets are obtained from a partition of the actual
middle positions. The outside maps are coordinate restrictions into their
admissible images. Their fiber counts, including saturated outside rank,
and the encoder collision sums come from `PaperMDSOverlap`.

The kernel below is the product on the actual middle positions. The
information kernel equality is proved explicitly. No operator hypothesis
or desired overlap estimate is assumed. Numerical AES resources and their
concrete diffusion-graph MDS proof remain separate instantiations.
Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperPhysicalOverlap

open AESMixing PaperMDSGram PaperMDSFiber PaperMDSOverlap PaperMDSCoordinateSplit
  FiberIncidence PaperInformationOverlap

attribute [local instance] Classical.propDecidable

variable {M KL KR A B E V : Type*}
  [Fintype M] [Fintype KL] [Fintype KR]
  [Fintype A] [Fintype B] [Fintype E] [Fintype V]
  [DecidableEq KL] [DecidableEq KR] [DecidableEq V]
  [AddCommGroup V]

def leftMissingEmbedding (idx : A ⊕ (B ⊕ E) ≃ M) (middle : M ↪ KL) : E ↪ KL where
  toFun e := middle (idx (Sum.inr (Sum.inr e)))
  inj' := fun _ _ h => Sum.inr.inj (Sum.inr.inj (idx.injective (middle.injective h)))

def rightMissingEmbedding (idx : A ⊕ (B ⊕ E) ≃ M) (middle : M ↪ KR) : A ↪ KR where
  toFun a := middle (idx (Sum.inl a))
  inj' := fun _ _ h => Sum.inl.inj (idx.injective (middle.injective h))

@[simp] theorem leftMissingEmbedding_apply (idx : A ⊕ (B ⊕ E) ≃ M)
    (middle : M ↪ KL) (e : E) :
    leftMissingEmbedding idx middle e = middle (idx (Sum.inr (Sum.inr e))) := rfl

@[simp] theorem rightMissingEmbedding_apply (idx : A ⊕ (B ⊕ E) ≃ M)
    (middle : M ↪ KR) (a : A) :
    rightMissingEmbedding idx middle a = middle (idx (Sum.inl a)) := rfl

theorem outside_disjoint_leftMissing (idx : A ⊕ (B ⊕ E) ≃ M)
    (middle : M ↪ KL) (outside : Finset KL)
    (hd : Disjoint outside (Finset.univ.map middle)) :
    Disjoint outside (Finset.univ.map (leftMissingEmbedding idx middle)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hj
  exact (Finset.disjoint_left.mp hd) hi
    (Finset.mem_map.mpr ⟨idx (Sum.inr (Sum.inr e)), Finset.mem_univ _, rfl⟩)

theorem outside_disjoint_rightMissing (idx : A ⊕ (B ⊕ E) ≃ M)
    (middle : M ↪ KR) (outside : Finset KR)
    (hd : Disjoint outside (Finset.univ.map middle)) :
    Disjoint outside (Finset.univ.map (rightMissingEmbedding idx middle)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hj
  exact (Finset.disjoint_left.mp hd) hi
    (Finset.mem_map.mpr ⟨idx (Sum.inl a), Finset.mem_univ _, rfl⟩)

/-- The actual physical middle kernel before information parametrization. -/
def physicalMiddleKernel
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V))
    (offsetL : KL → V) (offsetR : KR → V)
    (middleL : M ↪ KL) (middleR : M ↪ KR) (T : M → V → V → ℝ)
    (y : AffineCode CL offsetL) (x : AffineCode CR offsetR) : ℝ :=
  ∏ i, T i (y.val (middleL i)) (x.val (middleR i))

/-- The paper's operator on the actual affine graph domains. Its definition
does not mention an information set or a coordinate partition. -/
def physicalOverlap
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (offsetL : KL → V) (offsetR : KR → V)
    (middleL : M ↪ KL) (middleR : M ↪ KR)
    (outsideL : Finset KL) (outsideR : Finset KR) (T : M → V → V → ℝ)
    (f : OutsideLabel CR offsetR outsideR → ℝ) : OutsideLabel CL offsetL outsideL → ℝ :=
  normalizedAdjoint (outsideProjection CL offsetL outsideL)
    (Fintype.card V ^ (s - min s outsideL.card))
    (action (physicalMiddleKernel CL CR offsetL offsetR middleL middleR T)
      (normalizedLift (outsideProjection CR offsetR outsideR)
        (Fintype.card V ^ (t - min t outsideR.card)) f))

/-- An information set lying inside the middle proves that the actual
middle projection is injective; this is not a separate graph hypothesis. -/
theorem middle_restriction_injective {I : Type*} [Fintype I]
    (C : AddSubgroup (KL → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : KL → V) (middle : M ↪ KL) (info : I ↪ M)
    (hcard : Fintype.card I = k) :
    Function.Injective (fun x : AffineCode C offset => fun i : M => x.val (middle i)) := by
  intro x y hxy
  apply (affine_restriction_bijective C k hMDS offset (info.trans middle) hcard).injective
  funext i
  exact congrFun hxy (info i)

/-- The information overlap kernel is exactly the product on the physical
middle coordinates. The information-coordinate identities follow from MDS. -/
theorem physicalMiddleKernel_eq_information
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (hMDSL : IsMDS CL s) (hMDSR : IsMDS CR t)
    (offsetL : KL → V) (offsetR : KR → V)
    (idx : A ⊕ (B ⊕ E) ≃ M) (middleL : M ↪ KL) (middleR : M ↪ KR)
    (hleft : Fintype.card A + Fintype.card B = s)
    (hright : Fintype.card B + Fintype.card E = t)
    (T : M → V → V → ℝ)
    (y : (A → V) × (B → V)) (x : (B → V) × (E → V)) :
    physicalMiddleKernel CL CR offsetL offsetR middleL middleR T
      ((pairInformationEquiv CL s hMDSL offsetL
        ((leftInfoEmbedding idx).trans middleL) hleft).symm y)
      ((pairInformationEquiv CR t hMDSR offsetR
        ((rightInfoEmbedding idx).trans middleR) hright).symm x) =
    InformationOverlap.kernel
      (pairRemaining CR t hMDSR offsetR ((rightInfoEmbedding idx).trans middleR)
        hright (rightMissingEmbedding idx middleR))
      (pairRemaining CL s hMDSL offsetL ((leftInfoEmbedding idx).trans middleL)
        hleft (leftMissingEmbedding idx middleL))
      (fun a => T (idx (Sum.inl a)))
      (fun b => T (idx (Sum.inr (Sum.inl b))))
      (fun e => T (idx (Sum.inr (Sum.inr e)))) y x := by
  unfold physicalMiddleKernel
  rw [← idx.prod_comp]
  simp only [Fintype.prod_sum_type, InformationOverlap.kernel, pairRemaining,
    leftMissingEmbedding_apply, rightMissingEmbedding_apply]
  have hyA (a : A) := pairInformationEquiv_symm_left CL s hMDSL offsetL
    ((leftInfoEmbedding idx).trans middleL) hleft y a
  have hyB (b : B) := pairInformationEquiv_symm_right CL s hMDSL offsetL
    ((leftInfoEmbedding idx).trans middleL) hleft y b
  have hxB (b : B) := pairInformationEquiv_symm_left CR t hMDSR offsetR
    ((rightInfoEmbedding idx).trans middleR) hright x b
  have hxE (e : E) := pairInformationEquiv_symm_right CR t hMDSR offsetR
    ((rightInfoEmbedding idx).trans middleR) hright x e
  simp only [Function.Embedding.trans_apply, leftInfoEmbedding_inl,
    leftInfoEmbedding_inr] at hyA hyB
  simp only [Function.Embedding.trans_apply, rightInfoEmbedding_inl,
    rightInfoEmbedding_inr] at hxB hxE
  simp only [hyA, hyB, hxB, hxE]
  ring

/-- The actual normalized `J_L^* K J_R`, with `K` the physical middle product. -/
def normalizedPhysicalOverlap
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (hMDSL : IsMDS CL s) (hMDSR : IsMDS CR t)
    (offsetL : KL → V) (offsetR : KR → V)
    (idx : A ⊕ (B ⊕ E) ≃ M) (middleL : M ↪ KL) (middleR : M ↪ KR)
    (hleft : Fintype.card A + Fintype.card B = s)
    (hright : Fintype.card B + Fintype.card E = t)
    (outsideL : Finset KL) (outsideR : Finset KR) (T : M → V → V → ℝ)
    (f : OutsideLabel CR offsetR outsideR → ℝ) : OutsideLabel CL offsetL outsideL → ℝ :=
  normalizedAdjoint
    (pairOutside CL s hMDSL offsetL ((leftInfoEmbedding idx).trans middleL) hleft outsideL)
    (Fintype.card V ^ (s - min s outsideL.card))
    (action
      (fun y x => physicalMiddleKernel CL CR offsetL offsetR middleL middleR T
        ((pairInformationEquiv CL s hMDSL offsetL
          ((leftInfoEmbedding idx).trans middleL) hleft).symm y)
        ((pairInformationEquiv CR t hMDSR offsetR
          ((rightInfoEmbedding idx).trans middleR) hright).symm x))
      (normalizedLift
        (pairOutside CR t hMDSR offsetR ((rightInfoEmbedding idx).trans middleR) hright outsideR)
        (Fintype.card V ^ (t - min t outsideR.card)) f))

/-- Exact reparametrization of the actual graph-domain overlap. -/
theorem normalizedPhysicalOverlap_eq_physicalOverlap
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (hMDSL : IsMDS CL s) (hMDSR : IsMDS CR t)
    (offsetL : KL → V) (offsetR : KR → V)
    (idx : A ⊕ (B ⊕ E) ≃ M) (middleL : M ↪ KL) (middleR : M ↪ KR)
    (hleft : Fintype.card A + Fintype.card B = s)
    (hright : Fintype.card B + Fintype.card E = t)
    (outsideL : Finset KL) (outsideR : Finset KR) (T : M → V → V → ℝ)
    (f : OutsideLabel CR offsetR outsideR → ℝ) :
    normalizedPhysicalOverlap CL CR s t hMDSL hMDSR offsetL offsetR idx
      middleL middleR hleft hright outsideL outsideR T f =
    physicalOverlap CL CR s t offsetL offsetR middleL middleR outsideL outsideR T f := by
  exact PaperFiberTransport.normalizedOverlap_reparam
    (pairInformationEquiv CL s hMDSL offsetL ((leftInfoEmbedding idx).trans middleL) hleft).symm
    (pairInformationEquiv CR t hMDSR offsetR ((rightInfoEmbedding idx).trans middleR) hright).symm
    (outsideProjection CL offsetL outsideL) (outsideProjection CR offsetR outsideR)
    (Fintype.card V ^ (s - min s outsideL.card))
    (Fintype.card V ^ (t - min t outsideR.card))
    (physicalMiddleKernel CL CR offsetL offsetR middleL middleR T) f

/-- Lemma 8 with the physical `A/B/E` partition explicit. Both collision
factors and the exact `q^(a+b)` normalizer are derived from actual graph
coordinate fibers. The input is arbitrary and signed. -/
theorem normalizedPhysicalOverlap_l2
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (hs : s ≤ Fintype.card KL) (ht : t ≤ Fintype.card KR)
    (hMDSL : IsMDS CL s) (hMDSR : IsMDS CR t)
    (offsetL : KL → V) (offsetR : KR → V)
    (idx : A ⊕ (B ⊕ E) ≃ M) (middleL : M ↪ KL) (middleR : M ↪ KR)
    (hleft : Fintype.card A + Fintype.card B = s)
    (hright : Fintype.card B + Fintype.card E = t)
    (outsideL : Finset KL) (outsideR : Finset KR)
    (hdL : Disjoint outsideL (Finset.univ.map middleL))
    (hdR : Disjoint outsideR (Finset.univ.map middleR))
    (T : M → V → V → ℝ) (nu h delta : ℝ)
    (hnu : 0 ≤ nu) (hh : 0 ≤ h) (hdelta : 0 ≤ delta)
    (hcol : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ delta)
    (htotal : ∀ i, (∑ uv : V × V, T i uv.1 uv.2 ^ 2) ≤ h)
    (hop : ∀ i g, (∑ y, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : OutsideLabel CR offsetR outsideR → ℝ) :
    l2 (normalizedPhysicalOverlap CL CR s t hMDSL hMDSR offsetL offsetR idx
      middleL middleR hleft hright outsideL outsideR T f) ≤
    (Real.sqrt
      (collisionBound (Fintype.card V) (Fintype.card E) (s - min s outsideL.card) h delta *
        collisionBound (Fintype.card V) (Fintype.card A) (t - min t outsideR.card) h delta /
        (Fintype.card V : ℝ) ^ ((s - min s outsideL.card) + (t - min t outsideR.card))) *
      nu ^ Fintype.card B) * l2 f := by
  have hL (u : OutsideLabel CL offsetL outsideL) := pair_raw_collision_bound CL s hs
    hMDSL offsetL ((leftInfoEmbedding idx).trans middleL) hleft outsideL
    (leftMissingEmbedding idx middleL) (outside_disjoint_leftMissing idx middleL outsideL hdL)
    u (fun e y => ∑ x, T (idx (Sum.inr (Sum.inr e))) y x ^ 2) h delta
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (by intro e; simpa only [Fintype.sum_prod_type] using htotal (idx (Sum.inr (Sum.inr e))))
    (fun e y => hrow (idx (Sum.inr (Sum.inr e))) y)
  have hR (u : OutsideLabel CR offsetR outsideR) := pair_raw_collision_bound CR t ht
    hMDSR offsetR ((rightInfoEmbedding idx).trans middleR) hright outsideR
    (rightMissingEmbedding idx middleR) (outside_disjoint_rightMissing idx middleR outsideR hdR)
    u (fun a x => ∑ y, T (idx (Sum.inl a)) y x ^ 2) h delta
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (by
      intro a
      rw [Finset.sum_comm]
      simpa only [Fintype.sum_prod_type] using htotal (idx (Sum.inl a)))
    (fun a x => hcol (idx (Sum.inl a)) x)
  have hb := normalized_overlap_l2
    (pairOutside CL s hMDSL offsetL ((leftInfoEmbedding idx).trans middleL) hleft outsideL)
    (pairOutside CR t hMDSR offsetR ((rightInfoEmbedding idx).trans middleR) hright outsideR)
    (Fintype.card V ^ (s - min s outsideL.card))
    (Fintype.card V ^ (t - min t outsideR.card))
    (pairRemaining CR t hMDSR offsetR ((rightInfoEmbedding idx).trans middleR)
      hright (rightMissingEmbedding idx middleR))
    (pairRemaining CL s hMDSL offsetL ((leftInfoEmbedding idx).trans middleL)
      hleft (leftMissingEmbedding idx middleL))
    (fun a => T (idx (Sum.inl a)))
    (fun b => T (idx (Sum.inr (Sum.inl b))))
    (fun e => T (idx (Sum.inr (Sum.inr e))))
    (collisionBound (Fintype.card V) (Fintype.card E) (s - min s outsideL.card) h delta)
    (collisionBound (Fintype.card V) (Fintype.card A) (t - min t outsideR.card) h delta)
    (collisionBound_nonneg _ _ _ h delta hh hdelta)
    (collisionBound_nonneg _ _ _ h delta hh hdelta) (fun _ : B => nu) (fun _ => hnu)
    hL hR (fun b g => hop (idx (Sum.inr (Sum.inl b))) g) f
  have hkernel := funext (fun y => funext (fun x =>
    physicalMiddleKernel_eq_information CL CR s t hMDSL hMDSR offsetL offsetR
      idx middleL middleR hleft hright T y x))
  unfold normalizedPhysicalOverlap
  rw [hkernel]
  -- Simplify only the scalar coefficient, avoiding a traversal through the
  -- information equivalences and their graph-domain Fintype instances.
  calc
    _ ≤ _ := hb
    _ = _ := by
      congr 1
      simp only [Nat.cast_pow, ← pow_add, Finset.prod_const, Finset.card_univ]

/-- The paper's partition is selected from the numerical dimension premises,
not supplied as a separate information-set assumption. -/
def splitNormalizedPhysicalOverlap
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (hMDSL : IsMDS CL s) (hMDSR : IsMDS CR t)
    (offsetL : KL → V) (offsetR : KR → V)
    (hs : s ≤ Fintype.card M) (ht : t ≤ Fintype.card M)
    (hst : Fintype.card M ≤ s + t) (middleL : M ↪ KL) (middleR : M ↪ KR)
    (outsideL : Finset KL) (outsideR : Finset KR) (T : M → V → V → ℝ)
    (f : OutsideLabel CR offsetR outsideR → ℝ) : OutsideLabel CL offsetL outsideL → ℝ :=
  normalizedPhysicalOverlap CL CR s t hMDSL hMDSR offsetL offsetR
    (splitCoordinates s t hs ht hst) middleL middleR
    (by simpa only [Fintype.card_sum] using leftInfo_card s t hs ht hst)
    (by simpa only [Fintype.card_sum] using rightInfo_card s t hs ht hst)
    outsideL outsideR T f

/-- Paper Lemma 8 (`lem:overlap`) on physical coordinate fibers of two larger
affine MDS graphs. Write `n = |M|`, `a = s-min(s,|outsideL|)`, and
`b = t-min(t,|outsideR|)`. The coefficient is literally
`nu^(s+t-n) * sqrt(Phi(n-s,a) Phi(n-t,b) / q^(a+b))`.

Both middle projections are injective because the constructed information
sets lie in the middle. No arbitrary rank-constrained map is silently
identified with a coordinate restriction. -/
theorem paper_information_mds_overlap_l2
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (hMDSL : IsMDS CL s) (hMDSR : IsMDS CR t)
    (offsetL : KL → V) (offsetR : KR → V)
    (hs : s ≤ Fintype.card M) (ht : t ≤ Fintype.card M)
    (hst : Fintype.card M ≤ s + t) (middleL : M ↪ KL) (middleR : M ↪ KR)
    (outsideL : Finset KL) (outsideR : Finset KR)
    (hdL : Disjoint outsideL (Finset.univ.map middleL))
    (hdR : Disjoint outsideR (Finset.univ.map middleR))
    (T : M → V → V → ℝ) (nu h delta : ℝ)
    (hnu : 0 ≤ nu) (hh : 0 ≤ h) (hdelta : 0 ≤ delta)
    (hcol : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ delta)
    (htotal : ∀ i, (∑ uv : V × V, T i uv.1 uv.2 ^ 2) ≤ h)
    (hop : ∀ i g, (∑ y, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : OutsideLabel CR offsetR outsideR → ℝ) :
    l2 (splitNormalizedPhysicalOverlap CL CR s t hMDSL hMDSR offsetL offsetR hs ht hst
      middleL middleR outsideL outsideR T f) ≤
    (nu ^ (s + t - Fintype.card M) * Real.sqrt
      (collisionBound (Fintype.card V) (Fintype.card M - s) (s - min s outsideL.card) h delta *
        collisionBound (Fintype.card V) (Fintype.card M - t) (t - min t outsideR.card) h delta /
        (Fintype.card V : ℝ) ^ ((s - min s outsideL.card) + (t - min t outsideR.card)))) * l2 f := by
  have hKL : s ≤ Fintype.card KL := hs.trans
    (Fintype.card_le_of_injective middleL middleL.injective)
  have hKR : t ≤ Fintype.card KR := ht.trans
    (Fintype.card_le_of_injective middleR middleR.injective)
  have hb := normalizedPhysicalOverlap_l2 CL CR s t hKL hKR hMDSL hMDSR offsetL offsetR
    (splitCoordinates s t hs ht hst) middleL middleR
    (by simpa only [Fintype.card_sum] using leftInfo_card s t hs ht hst)
    (by simpa only [Fintype.card_sum] using rightInfo_card s t hs ht hst)
    outsideL outsideR hdL hdR T nu h delta hnu hh hdelta hcol hrow htotal hop f
  change l2 (normalizedPhysicalOverlap CL CR s t hMDSL hMDSR offsetL offsetR
    (splitCoordinates s t hs ht hst) middleL middleR
    (by simpa only [Fintype.card_sum] using leftInfo_card s t hs ht hst)
    (by simpa only [Fintype.card_sum] using rightInfo_card s t hs ht hst)
    outsideL outsideR T f) ≤ _
  calc
    _ ≤ _ := hb
    _ = _ := by
      congr 1
      simp only [Fintype.card_fin]
      exact mul_comm _ _

/-- Lemma 8 on the direct physical graph operator, independent of all
chosen information parametrizations. Every count in the coefficient is a
derived physical-coordinate count. -/
theorem paper_mds_overlap_l2
    (CL : AddSubgroup (KL → V)) (CR : AddSubgroup (KR → V)) (s t : ℕ)
    (hMDSL : IsMDS CL s) (hMDSR : IsMDS CR t)
    (offsetL : KL → V) (offsetR : KR → V)
    (hs : s ≤ Fintype.card M) (ht : t ≤ Fintype.card M)
    (hst : Fintype.card M ≤ s + t) (middleL : M ↪ KL) (middleR : M ↪ KR)
    (outsideL : Finset KL) (outsideR : Finset KR)
    (hdL : Disjoint outsideL (Finset.univ.map middleL))
    (hdR : Disjoint outsideR (Finset.univ.map middleR))
    (T : M → V → V → ℝ) (nu h delta : ℝ)
    (hnu : 0 ≤ nu) (hh : 0 ≤ h) (hdelta : 0 ≤ delta)
    (hcol : ∀ i x, (∑ y, T i y x ^ 2) ≤ delta)
    (hrow : ∀ i y, (∑ x, T i y x ^ 2) ≤ delta)
    (htotal : ∀ i, (∑ uv : V × V, T i uv.1 uv.2 ^ 2) ≤ h)
    (hop : ∀ i g, (∑ y, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (f : OutsideLabel CR offsetR outsideR → ℝ) :
    l2 (physicalOverlap CL CR s t offsetL offsetR middleL middleR outsideL outsideR T f) ≤
    (nu ^ (s + t - Fintype.card M) * Real.sqrt
      (collisionBound (Fintype.card V) (Fintype.card M - s) (s - min s outsideL.card) h delta *
        collisionBound (Fintype.card V) (Fintype.card M - t) (t - min t outsideR.card) h delta /
        (Fintype.card V : ℝ) ^ ((s - min s outsideL.card) + (t - min t outsideR.card)))) * l2 f := by
  have heq := normalizedPhysicalOverlap_eq_physicalOverlap CL CR s t hMDSL hMDSR
    offsetL offsetR (splitCoordinates s t hs ht hst) middleL middleR
    (by simpa only [Fintype.card_sum] using leftInfo_card s t hs ht hst)
    (by simpa only [Fintype.card_sum] using rightInfo_card s t hs ht hst)
    outsideL outsideR T f
  rw [← heq]
  exact paper_information_mds_overlap_l2 CL CR s t hMDSL hMDSR offsetL offsetR hs ht hst
    middleL middleR outsideL outsideR hdL hdR T nu h delta hnu hh hdelta
    hcol hrow htotal hop f

end AES8.PaperPhysicalOverlap
