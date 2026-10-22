/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MDSFiberCollision
import AESConcrete.WordCrossZero

/-!
# Literal paired wordMix fibers and mixed information labels

The two forward outputs have their c coordinate zero and agree at every
position other than c,d. The mixed observations select one input coordinate
from the first state and the other three from the second. Two existing MDS
information maps reconstruct the second state first, then the first state.
Swapping the states gives the complementary mixed information system.

The restricted domain retains nonzero d coordinates in both outputs. Its
inclusion into the full paired domain is supplied for later nonnegative
squared-factor estimates; no signed sum is enlarged here. No local energy
cap or source-law premise is part of this geometry module.

  Constructive proofs only; no attacks, local scientific execution,
active-source edits, manuscript edits or predecessor changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.PairedWordMixFiber
open AESMixing AESMixing.AES AESConcrete.WordCrossZero

/-- The three other input names remain literal position subtypes. -/
abbrev Other (i : Fin 4) := {j : Fin 4 // j ≠ i}

private def singleMask : Fin 4 → Fin 16 := ![1, 2, 4, 8]
private def otherMask : Fin 4 → Fin 16 := ![14, 13, 11, 7]

-- These certificates enumerate only four POSITION names and their masks.
-- They never enumerate words, states, source weights, or diffusion values.
private theorem singleMask_mem : ∀ i j : Fin 4,
    maskBit (singleMask i) j = true ↔ j = i := by decide

private theorem singleMask_not_mem : ∀ i j : Fin 4,
    maskBit (singleMask i) j ≠ true ↔ j ≠ i := by decide

private theorem otherMask_mem : ∀ i j : Fin 4,
    maskBit (otherMask i) j = true ↔ j ≠ i := by decide

private theorem otherMask_not_mem : ∀ i j : Fin 4,
    maskBit (otherMask i) j ≠ true ↔ j = i := by decide

private theorem singleMask_size : ∀ i : Fin 4,
    maskSize (singleMask i) = 1 := by decide

private theorem otherMask_size : ∀ i : Fin 4,
    maskSize (otherMask i) = 3 := by decide

theorem other_card : ∀ i : Fin 4, Fintype.card (Other i) = 3 := by decide

-- The energy interface uses the literal nested order (1,(2,3)) at i=0.
-- This equivalence only enumerates three POSITION names, never word values.
private def otherZeroIndices : Fin 3 → Other 0 :=
  ![⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

private theorem otherZeroIndices_bijective : Function.Bijective otherZeroIndices := by decide

private def otherZeroIndexEquiv : Fin 3 ≃ Other 0 :=
  Equiv.ofBijective otherZeroIndices otherZeroIndices_bijective

private def otherZeroTupleEquiv (V : Type*) :
    (Other 0 → V) ≃ V × (V × V) where
  toFun f := (f (otherZeroIndexEquiv 0),
    (f (otherZeroIndexEquiv 1), f (otherZeroIndexEquiv 2)))
  invFun p j := ![p.1, p.2.1, p.2.2] (otherZeroIndexEquiv.symm j)
  left_inv f := by
    funext j
    change ![f (otherZeroIndexEquiv 0), f (otherZeroIndexEquiv 1),
      f (otherZeroIndexEquiv 2)] (otherZeroIndexEquiv.symm j) = f j
    have he (k : Fin 3) :
        ![f (otherZeroIndexEquiv 0), f (otherZeroIndexEquiv 1),
          f (otherZeroIndexEquiv 2)] k = f (otherZeroIndexEquiv k) := by
      fin_cases k <;> rfl
    rw [he, otherZeroIndexEquiv.apply_symm_apply]
  right_inv p := by
    rcases p with ⟨a, b, c⟩
    change
      (![a, b, c] (otherZeroIndexEquiv.symm (otherZeroIndexEquiv 0)),
        (![a, b, c] (otherZeroIndexEquiv.symm (otherZeroIndexEquiv 1)),
          ![a, b, c] (otherZeroIndexEquiv.symm (otherZeroIndexEquiv 2)))) =
        (a, (b, c))
    simp only [otherZeroIndexEquiv.symm_apply_apply]
    rfl

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Full literal paired fiber. The complementary a,b positions are expressed
without choosing an ordering: both forward outputs agree away from c,d. -/
abbrev Pair (L : (Fin 4 → V) →+ (Fin 4 → V)) (c d : Fin 4) :=
  {p : (Fin 4 → V) × (Fin 4 → V) //
    L p.1 c = 0 ∧ L p.2 c = 0 ∧
      ∀ j : Fin 4, j ≠ c → j ≠ d → L p.1 j = L p.2 j}

/-- The actual activity-average square restricts BOTH d coordinates to
nonzero. This domain must be retained through the signed Cauchy step. -/
abbrev RestrictedPair (L : (Fin 4 → V) →+ (Fin 4 → V)) (c d : Fin 4) :=
  {p : Pair L c d // L p.val.1 d ≠ 0 ∧ L p.val.2 d ≠ 0}

def restrictedInclusion (L : (Fin 4 → V) →+ (Fin 4 → V)) (c d : Fin 4) :
    RestrictedPair L c d → Pair L c d := Subtype.val

theorem restrictedInclusion_injective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (c d : Fin 4) :
    Function.Injective (restrictedInclusion L c d) := by
  intro x y h
  exact Subtype.ext h

/-- The zero constraints supply the omitted equality at c as well. -/
theorem outputs_eq_off_d (L : (Fin 4 → V) →+ (Fin 4 → V))
    (c d : Fin 4) (p : Pair L c d) (j : Fin 4) (hj : j ≠ d) :
    L p.val.1 j = L p.val.2 j := by
  by_cases hc : j = c
  · subst j
    exact p.property.1.trans p.property.2.1.symm
  · exact p.property.2.2 j hc hj

private def secondInfo
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (c i : Fin 4) :
    (Fin 4 → V) ≃ (InformationIndex (singleMask c) (singleMask i) → V) :=
  mdsInformationEquiv L hL (singleMask c) (singleMask i)
    (by rw [singleMask_size, singleMask_size])

private def secondTarget (c i : Fin 4) (v : Other i → V) :
    InformationIndex (singleMask c) (singleMask i) → V :=
  Sum.elim (fun _ => 0)
    (fun j => v ⟨j.val, (singleMask_not_mem i j.val).mp j.property⟩)

/-- First reconstruction: output c is zero and the other three inputs are
the literal supplied values. This is a 1-output/3-input MDS information map. -/
private def rebuildSecond
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c i : Fin 4) (v : Other i → V) : Fin 4 → V :=
  (secondInfo L hL c i).symm (secondTarget c i v)

private theorem rebuildSecond_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c i : Fin 4) (v : Other i → V) :
    L (rebuildSecond L hL c i v) c = 0 := by
  have h := congrFun ((secondInfo L hL c i).apply_symm_apply (secondTarget c i v))
    (Sum.inl ⟨c, (singleMask_mem c c).mpr rfl⟩)
  change L (rebuildSecond L hL c i v) c = 0 at h
  exact h

private theorem rebuildSecond_other
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c i : Fin 4) (v : Other i → V) (j : Other i) :
    rebuildSecond L hL c i v j.val = v j := by
  have h := congrFun ((secondInfo L hL c i).apply_symm_apply (secondTarget c i v))
    (Sum.inr ⟨j.val, (singleMask_not_mem i j.val).mpr j.property⟩)
  change rebuildSecond L hL c i v j.val = v j at h
  exact h

private theorem second_eq_of_labels
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c i : Fin 4) (x y : Fin 4 → V)
    (hc : L x c = L y c) (ho : ∀ j : Other i, x j.val = y j.val) : x = y := by
  apply (secondInfo L hL c i).injective
  funext j
  cases j with
  | inl j =>
    change L x j.val = L y j.val
    have hj : j.val = c := (singleMask_mem c j.val).mp j.property
    simpa only [hj] using hc
  | inr j =>
    change x j.val = y j.val
    exact ho ⟨j.val, (singleMask_not_mem i j.val).mp j.property⟩

private def firstInfo
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (d i : Fin 4) :
    (Fin 4 → V) ≃ (InformationIndex (otherMask d) (otherMask i) → V) :=
  mdsInformationEquiv L hL (otherMask d) (otherMask i)
    (by rw [otherMask_size, otherMask_size])

private def firstTarget (L : (Fin 4 → V) →+ (Fin 4 → V))
    (d i : Fin 4) (h : Fin 4 → V) (u : V) :
    InformationIndex (otherMask d) (otherMask i) → V :=
  Sum.elim (fun j => L h j.val) (fun _ => u)

/-- Second reconstruction: input i is supplied, while all three outputs
away from d agree with the reconstructed second state. -/
private def rebuildFirst
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (d i : Fin 4) (h : Fin 4 → V) (u : V) : Fin 4 → V :=
  (firstInfo L hL d i).symm (firstTarget L d i h u)

private theorem rebuildFirst_input
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (d i : Fin 4) (h : Fin 4 → V) (u : V) :
    rebuildFirst L hL d i h u i = u := by
  have he := congrFun ((firstInfo L hL d i).apply_symm_apply (firstTarget L d i h u))
    (Sum.inr ⟨i, (otherMask_not_mem i i).mpr rfl⟩)
  change rebuildFirst L hL d i h u i = u at he
  exact he

private theorem rebuildFirst_output
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (d i : Fin 4) (h : Fin 4 → V) (u : V) (j : Fin 4) (hj : j ≠ d) :
    L (rebuildFirst L hL d i h u) j = L h j := by
  have he := congrFun ((firstInfo L hL d i).apply_symm_apply (firstTarget L d i h u))
    (Sum.inl ⟨j, (otherMask_mem d j).mpr hj⟩)
  change L (rebuildFirst L hL d i h u) j = L h j at he
  exact he

private theorem first_eq_of_labels
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (d i : Fin 4) (x y : Fin 4 → V)
    (hi : x i = y i) (ho : ∀ j : Fin 4, j ≠ d → L x j = L y j) : x = y := by
  apply (firstInfo L hL d i).injective
  funext j
  cases j with
  | inl j =>
    change L x j.val = L y j.val
    exact ho j.val ((otherMask_mem d j.val).mp j.property)
  | inr j =>
    change x j.val = y j.val
    have hj : j.val = i := (otherMask_not_mem i j.val).mp j.property
    simpa only [hj] using hi

/-- Literal one-plus-three input coordinate labels. -/
def mixedLabels (L : (Fin 4 → V) →+ (Fin 4 → V)) (c d i : Fin 4)
    (p : Pair L c d) : V × (Other i → V) :=
  (p.val.1 i, fun j => p.val.2 j.val)

theorem mixedLabels_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c d i : Fin 4) (hcd : c ≠ d) :
    Function.Bijective (mixedLabels L c d i) := by
  constructor
  · intro p q hpq
    have hfirst : p.val.1 i = q.val.1 i := congrArg Prod.fst hpq
    have hother : ∀ j : Other i, p.val.2 j.val = q.val.2 j.val := by
      intro j
      exact congrFun (congrArg Prod.snd hpq) j
    have hsecond : p.val.2 = q.val.2 :=
      second_eq_of_labels L hL c i p.val.2 q.val.2
        (p.property.2.1.trans q.property.2.1.symm) hother
    have hg : p.val.1 = q.val.1 := by
      apply first_eq_of_labels L hL d i p.val.1 q.val.1 hfirst
      intro j hj
      calc
        L p.val.1 j = L p.val.2 j := outputs_eq_off_d L c d p j hj
        _ = L q.val.2 j := congrArg (fun x : Fin 4 → V => L x j) hsecond
        _ = L q.val.1 j := (outputs_eq_off_d L c d q j hj).symm
    exact Subtype.ext (Prod.ext hg hsecond)
  · intro p
    let h := rebuildSecond L hL c i p.2
    let g := rebuildFirst L hL d i h p.1
    have hh : L h c = 0 := rebuildSecond_zero L hL c i p.2
    have hg : L g c = 0 :=
      (rebuildFirst_output L hL d i h p.1 c hcd).trans hh
    have hpair : L g c = 0 ∧ L h c = 0 ∧
        ∀ j : Fin 4, j ≠ c → j ≠ d → L g j = L h j := by
      refine ⟨hg, hh, ?_⟩
      intro j _ hj
      exact rebuildFirst_output L hL d i h p.1 j hj
    refine ⟨⟨(g, h), hpair⟩, ?_⟩
    apply Prod.ext
    · exact rebuildFirst_input L hL d i h p.1
    · funext j
      exact rebuildSecond_other L hL c i p.2 j

def mixedEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c d i : Fin 4) (hcd : c ≠ d) : Pair L c d ≃ V × (Other i → V) :=
  Equiv.ofBijective (mixedLabels L c d i) (mixedLabels_bijective L hL c d i hcd)

@[simp] theorem mixedEquiv_apply
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c d i : Fin 4) (hcd : c ≠ d) (p : Pair L c d) :
    mixedEquiv L hL c d i hcd p = (p.val.1 i, fun j => p.val.2 j.val) := rfl

def swapPair (L : (Fin 4 → V) →+ (Fin 4 → V)) (c d : Fin 4)
    (p : Pair L c d) : Pair L c d :=
  ⟨(p.val.2, p.val.1), p.property.2.1, p.property.1,
    fun j hc hd => (p.property.2.2 j hc hd).symm⟩

def swapEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (c d : Fin 4) :
    Pair L c d ≃ Pair L c d where
  toFun := swapPair L c d
  invFun := swapPair L c d
  left_inv p := Subtype.ext (Prod.ext rfl rfl)
  right_inv p := Subtype.ext (Prod.ext rfl rfl)

/-- Complementary literal three-plus-one information system. -/
def swappedMixedEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c d i : Fin 4) (hcd : c ≠ d) : Pair L c d ≃ V × (Other i → V) :=
  (swapEquiv L c d).trans (mixedEquiv L hL c d i hcd)

@[simp] theorem swappedMixedEquiv_apply
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (c d i : Fin 4) (hcd : c ≠ d) (p : Pair L c d) :
    swappedMixedEquiv L hL c d i hcd p =
      (p.val.2 i, fun j => p.val.1 j.val) := rfl

end Generic

section ActualOrdinary

/-- Actual forward physical wordMix, with neither inverse nor Fourier map substituted. -/
abbrev boundary := wordMixAddEquiv.toAddMonoidHom
abbrev H (c d : Fin 4) := Pair boundary c d
abbrev D (c d : Fin 4) := RestrictedPair boundary c d

def equiv (c d i : Fin 4) (hcd : c ≠ d) :
    H c d ≃ AES.Word × (Other i → AES.Word) :=
  mixedEquiv boundary wordMixAddEquiv_zeroMDS c d i hcd

def swappedEquiv (c d i : Fin 4) (hcd : c ≠ d) :
    H c d ≃ AES.Word × (Other i → AES.Word) :=
  swappedMixedEquiv boundary wordMixAddEquiv_zeroMDS c d i hcd

@[simp] theorem equiv_apply (c d i : Fin 4) (hcd : c ≠ d) (p : H c d) :
    equiv c d i hcd p = (p.val.1 i, fun j => p.val.2 j.val) := rfl

@[simp] theorem swappedEquiv_apply (c d i : Fin 4) (hcd : c ≠ d) (p : H c d) :
    swappedEquiv c d i hcd p = (p.val.2 i, fun j => p.val.1 j.val) := rfl

theorem coords_bijective (c d i : Fin 4) (hcd : c ≠ d) :
    Function.Bijective (fun p : H c d => (p.val.1 i, fun j : Other i => p.val.2 j.val)) :=
  (equiv c d i hcd).bijective

theorem swappedCoords_bijective (c d i : Fin 4) (hcd : c ≠ d) :
    Function.Bijective (fun p : H c d => (p.val.2 i, fun j : Other i => p.val.1 j.val)) :=
  (swappedEquiv c d i hcd).bijective

/-- Exact nested-tuple codomain required by the distinguished-input energy API. -/
abbrev Quadruple := AES.Word × (AES.Word × (AES.Word × AES.Word))

def infoL (c d : Fin 4) (p : H c d) : Quadruple :=
  (p.val.1 0, (p.val.2 1, (p.val.2 2, p.val.2 3)))

def infoR (c d : Fin 4) (p : H c d) : Quadruple :=
  (p.val.2 0, (p.val.1 1, (p.val.1 2, p.val.1 3)))

def infoLEquiv (c d : Fin 4) (hcd : c ≠ d) : H c d ≃ Quadruple :=
  (equiv c d 0 hcd).trans
    (Equiv.prodCongr (Equiv.refl AES.Word) (otherZeroTupleEquiv AES.Word))

def infoREquiv (c d : Fin 4) (hcd : c ≠ d) : H c d ≃ Quadruple :=
  (swappedEquiv c d 0 hcd).trans
    (Equiv.prodCongr (Equiv.refl AES.Word) (otherZeroTupleEquiv AES.Word))

@[simp] theorem infoLEquiv_apply (c d : Fin 4) (hcd : c ≠ d) (p : H c d) :
    infoLEquiv c d hcd p = infoL c d p := rfl

@[simp] theorem infoREquiv_apply (c d : Fin 4) (hcd : c ≠ d) (p : H c d) :
    infoREquiv c d hcd p = infoR c d p := rfl

theorem infoL_bijective (c d : Fin 4) (hcd : c ≠ d) :
    Function.Bijective (infoL c d) :=
  (infoLEquiv c d hcd).bijective

theorem infoR_bijective (c d : Fin 4) (hcd : c ≠ d) :
    Function.Bijective (infoR c d) :=
  (infoREquiv c d hcd).bijective

theorem coordsZero_bijective (c d : Fin 4) (hcd : c ≠ d) :
    Function.Bijective
      (fun p : H c d => (p.val.1 0, (p.val.2 1, (p.val.2 2, p.val.2 3)))) :=
  infoL_bijective c d hcd

theorem swappedCoordsZero_bijective (c d : Fin 4) (hcd : c ≠ d) :
    Function.Bijective
      (fun p : H c d => (p.val.2 0, (p.val.1 1, (p.val.1 2, p.val.1 3)))) :=
  infoR_bijective c d hcd

/-- Exact full-domain sum reindexing for arbitrary signed integrands.
Restriction D must be handled separately before this full-domain identity. -/
theorem sum_mixed (c d i : Fin 4) (hcd : c ≠ d)
    (F : AES.Word → (Other i → AES.Word) → ℝ) :
    (∑ p : H c d, F (p.val.1 i) (fun j => p.val.2 j.val)) =
      ∑ x : AES.Word, ∑ v : Other i → AES.Word, F x v := by
  have h := Equiv.sum_comp (equiv c d i hcd)
    (fun p : AES.Word × (Other i → AES.Word) => F p.1 p.2)
  simpa only [equiv_apply, Fintype.sum_prod_type] using h

theorem sum_swapped (c d i : Fin 4) (hcd : c ≠ d)
    (F : AES.Word → (Other i → AES.Word) → ℝ) :
    (∑ p : H c d, F (p.val.2 i) (fun j => p.val.1 j.val)) =
      ∑ x : AES.Word, ∑ v : Other i → AES.Word, F x v := by
  have h := Equiv.sum_comp (swappedEquiv c d i hcd)
    (fun p : AES.Word × (Other i → AES.Word) => F p.1 p.2)
  simpa only [swappedEquiv_apply, Fintype.sum_prod_type] using h

end ActualOrdinary
end AES8.PairedWordMixFiber
