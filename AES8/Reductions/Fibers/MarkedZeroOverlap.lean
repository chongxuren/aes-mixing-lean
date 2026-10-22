/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MarkedZeroFiber
import AES8.Math.InformationOverlap

/-!
# Literal three-coordinate zero-fiber image overlap

The two actual attained images are expressed in different information pairs:
row labels use `(a,b)` and column labels use `(b,e)`. Rows are the left
graph's input-middle image and columns the right graph's output-middle image,
in the physical composition order `outsideLeft ← middleLeft ← middleRight`.
Their tensor kernel
is proved to be exactly `InformationOverlap.kernel`, using literal coordinate
evaluation and the MDS-derived information-image equivalences. The one
remaining coordinate on either image is reconstructed from its full pair.
The induced action and energy identities retain arbitrary signed inputs.

This is the middle-image tensor bridge only. Neither centered physical
step, outside encoder, shared activity metric, full fixed-pattern expansion,
nor the (11,11) return cap is identified by this module.
Constructive proofs only; no attacks or active-source/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace AES8.MarkedZeroOverlap
open AESMixing AESMixing.AES
open AES8.MDSFiberCollision AES8.MDSFiberIncidence AES8.MarkedZeroFiber

def singleMask : Fin 4 → Fin 16 := ![1, 2, 4, 8]

def pairMask (a b : Fin 4) : Fin 16 := maskUnion (singleMask a) (singleMask b)

-- These finite certificates concern four position names, not alphabet values.
theorem pairMask_mem : ∀ a b i : Fin 4,
    maskBit (pairMask a b) i = true ↔ i = a ∨ i = b := by decide

theorem pairMask_size : ∀ a b : Fin 4, a ≠ b → maskSize (pairMask a b) = 2 := by decide

def pairFirst (a b : Fin 4) : MaskCoordinates (pairMask a b) :=
  ⟨a, (pairMask_mem a b a).mpr (Or.inl rfl)⟩

def pairSecond (a b : Fin 4) : MaskCoordinates (pairMask a b) :=
  ⟨b, (pairMask_mem a b b).mpr (Or.inr rfl)⟩

theorem pairFirst_ne_second (a b : Fin 4) (hab : a ≠ b) :
    pairFirst a b ≠ pairSecond a b := by
  intro h
  exact hab (congrArg Subtype.val h)

theorem pair_cover (a b : Fin 4) (i : MaskCoordinates (pairMask a b)) :
    i = pairFirst a b ∨ i = pairSecond a b := by
  rcases (pairMask_mem a b i.val).mp i.property with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem pair_le {middle : Fin 16} (a b : MaskCoordinates middle) :
    MaskLE (pairMask a.val b.val) middle := by
  intro i hi
  rcases (pairMask_mem a.val b.val i).mp hi with h | h
  · simpa only [h] using a.property
  · simpa only [h] using b.property

private theorem emptyCoordinate (i : MaskCoordinates (0 : Fin 16)) : False := by
  have hz : ∀ j : Fin 4, maskBit (0 : Fin 16) j = false := by decide
  have hi := i.property
  rw [hz] at hi
  contradiction

/-- Remove only the empty output tag; input coordinate names stay literal. -/
def inputObservedEquiv (info : Fin 16) (V : Type*) :
    (ObservedIndex 0 info → V) ≃ (MaskCoordinates info → V) where
  toFun f i := f (Sum.inr i)
  invFun f i := match i with
    | Sum.inl j => False.elim (emptyCoordinate j)
    | Sum.inr j => f j
  left_inv f := by
    funext i
    cases i with
    | inl j => exact False.elim (emptyCoordinate j)
    | inr j => rfl
  right_inv f := rfl

/-- Remove only the empty input tag; output coordinate names stay literal. -/
def outputObservedEquiv (info : Fin 16) (V : Type*) :
    (ObservedIndex info 0 → V) ≃ (MaskCoordinates info → V) where
  toFun f i := f (Sum.inl i)
  invFun f i := match i with
    | Sum.inl j => f j
    | Sum.inr j => False.elim (emptyCoordinate j)
  left_inv f := by
    funext i
    cases i with
    | inl j => rfl
    | inr j => exact False.elim (emptyCoordinate j)
  right_inv f := rfl

/-- Two named positions become the two singleton information labels. -/
def pairEvalEquiv (a b : Fin 4) (hab : a ≠ b) (V : Type*) :
    (MaskCoordinates (pairMask a b) → V) ≃ ((Unit → V) × (Unit → V)) where
  toFun f := (fun _ => f (pairFirst a b), fun _ => f (pairSecond a b))
  invFun p i := if i = pairFirst a b then p.1 () else p.2 ()
  left_inv f := by
    funext i
    rcases pair_cover a b i with h | h
    · subst i
      simp
    · subst i
      simp [Ne.symm (pairFirst_ne_second a b hab)]
  right_inv p := by
    apply Prod.ext <;> funext i <;> cases i
    · simp
    · simp [Ne.symm (pairFirst_ne_second a b hab)]

def inputValue {r z middle : Fin 16} (x : InputImage r z middle)
    (i : MaskCoordinates middle) : AES.Word := x.val (Sum.inr i)

def outputValue {r z middle : Fin 16} (y : OutputImage r z middle)
    (i : MaskCoordinates middle) : AES.Word := y.val (Sum.inl i)

def inputPairEquiv (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1) (hdis : MaskDisjoint z middle)
    (a b : MaskCoordinates middle) (hab : a ≠ b) :
    InputImage r z middle ≃ ((Unit → AES.Word) × (Unit → AES.Word)) :=
  (inputInformationEquiv r z middle (pairMask a.val b.val) hr hz
    (pairMask_size a.val b.val (fun h => hab (Subtype.ext h)))
    (pair_le a b) hdis).trans
      ((inputObservedEquiv (pairMask a.val b.val) AES.Word).trans
        (pairEvalEquiv a.val b.val (fun h => hab (Subtype.ext h)) AES.Word))

def outputPairEquiv (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1) (hdis : MaskDisjoint r middle)
    (a b : MaskCoordinates middle) (hab : a ≠ b) :
    OutputImage r z middle ≃ ((Unit → AES.Word) × (Unit → AES.Word)) :=
  (outputInformationEquiv r z middle (pairMask a.val b.val) hr hz
    (pairMask_size a.val b.val (fun h => hab (Subtype.ext h)))
    (pair_le a b) hdis).trans
      ((outputObservedEquiv (pairMask a.val b.val) AES.Word).trans
        (pairEvalEquiv a.val b.val (fun h => hab (Subtype.ext h)) AES.Word))

@[simp] theorem inputPairEquiv_first (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1) (hdis : MaskDisjoint z middle)
    (a b : MaskCoordinates middle) (hab : a ≠ b) (x : InputImage r z middle) :
    (inputPairEquiv r z middle hr hz hdis a b hab x).1 () = inputValue x a := rfl

@[simp] theorem inputPairEquiv_second (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1) (hdis : MaskDisjoint z middle)
    (a b : MaskCoordinates middle) (hab : a ≠ b) (x : InputImage r z middle) :
    (inputPairEquiv r z middle hr hz hdis a b hab x).2 () = inputValue x b := rfl

@[simp] theorem outputPairEquiv_first (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1) (hdis : MaskDisjoint r middle)
    (a b : MaskCoordinates middle) (hab : a ≠ b) (y : OutputImage r z middle) :
    (outputPairEquiv r z middle hr hz hdis a b hab y).1 () = outputValue y a := rfl

@[simp] theorem outputPairEquiv_second (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1) (hdis : MaskDisjoint r middle)
    (a b : MaskCoordinates middle) (hab : a ≠ b) (y : OutputImage r z middle) :
    (outputPairEquiv r z middle hr hz hdis a b hab y).2 () = outputValue y b := rfl

structure TripleSplit (middle : Fin 16) where
  a : MaskCoordinates middle
  b : MaskCoordinates middle
  e : MaskCoordinates middle
  hab : a ≠ b
  hae : a ≠ e
  hbe : b ≠ e
  cover : ∀ i : MaskCoordinates middle, i = a ∨ i = b ∨ i = e

theorem three_named : ∀ middle : Fin 16, maskSize middle = 3 →
    ∃ a b e : Fin 4, a ≠ b ∧ a ≠ e ∧ b ≠ e ∧
      (∀ i : Fin 4, maskBit middle i = true ↔ i = a ∨ i = b ∨ i = e) := by decide

theorem three_split_exists (middle : Fin 16) (hthree : maskSize middle = 3) :
    ∃ s : TripleSplit middle, True := by
  obtain ⟨a, b, e, hab, hae, hbe, hcover⟩ := three_named middle hthree
  have ha : maskBit middle a = true := (hcover a).mpr (Or.inl rfl)
  have hb : maskBit middle b = true := (hcover b).mpr (Or.inr (Or.inl rfl))
  have he : maskBit middle e = true := (hcover e).mpr (Or.inr (Or.inr rfl))
  refine ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨e, he⟩, ?_, ?_, ?_, ?_⟩, trivial⟩
  · intro h
    exact hab (congrArg Subtype.val h)
  · intro h
    exact hae (congrArg Subtype.val h)
  · intro h
    exact hbe (congrArg Subtype.val h)
  · intro i
    rcases (hcover i.val).mp i.property with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))

def selectedSplit (middle : Fin 16) (hthree : maskSize middle = 3) : TripleSplit middle :=
  Classical.choose (three_split_exists middle hthree)

theorem prod_three {middle : Fin 16} (s : TripleSplit middle)
    (f : MaskCoordinates middle → ℝ) :
    (∏ i, f i) = f s.a * f s.b * f s.e := by
  have hu : (Finset.univ : Finset (MaskCoordinates middle)) = {s.a, s.b, s.e} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact s.cover i
  rw [hu]
  simp [s.hab, s.hae, s.hbe] <;> ring

/-- The literal coordinate tensor compressed to the two attained images. -/
def tensorKernel {rL zL rR zR middle : Fin 16}
    (K : MaskCoordinates middle → AES.Word → AES.Word → ℝ)
    (y : InputImage rL zL middle) (x : OutputImage rR zR middle) : ℝ :=
  ∏ i, K i (inputValue y i) (outputValue x i)

section Overlap
variable (rL zL rR zR middle : Fin 16)
variable (hrL : maskSize rL = 1) (hzL : maskSize zL = 1)
variable (hrR : maskSize rR = 1) (hzR : maskSize zR = 1)
variable (hdisL : MaskDisjoint zL middle) (hdisR : MaskDisjoint rR middle)
variable (s : TripleSplit middle)

-- In I_left * K * I_right^T, K's rows are the left graph's INPUT
-- observations, and its columns the right graph's OUTPUT observations.
def rowLabels : InputImage rL zL middle ≃
    ((Unit → AES.Word) × (Unit → AES.Word)) :=
  inputPairEquiv rL zL middle hrL hzL hdisL s.a s.b s.hab

def columnLabels : OutputImage rR zR middle ≃
    ((Unit → AES.Word) × (Unit → AES.Word)) :=
  outputPairEquiv rR zR middle hrR hzR hdisR s.b s.e s.hbe

-- Each reconstruction keeps the full information label; no independence
-- between its two coordinates is introduced.
def leftCode (x : (Unit → AES.Word) × (Unit → AES.Word)) (_ : Unit) : AES.Word :=
  outputValue ((columnLabels rR zR middle hrR hzR hdisR s).symm x) s.a

def rightCode (y : (Unit → AES.Word) × (Unit → AES.Word)) (_ : Unit) : AES.Word :=
  inputValue ((rowLabels rL zL middle hrL hzL hdisL s).symm y) s.e

/-- Exact equality with the already proved overlap kernel, without an
assumed code/kernel identification or any extra multiplicity factor. -/
theorem tensorKernel_eq_overlap
    (K : MaskCoordinates middle → AES.Word → AES.Word → ℝ)
    (y x : (Unit → AES.Word) × (Unit → AES.Word)) :
    tensorKernel K
      ((rowLabels rL zL middle hrL hzL hdisL s).symm y)
      ((columnLabels rR zR middle hrR hzR hdisR s).symm x) =
      AES8.InformationOverlap.kernel
        (leftCode rR zR middle hrR hzR hdisR s)
        (rightCode rL zL middle hrL hzL hdisL s)
        (fun _ => K s.a) (fun _ => K s.b) (fun _ => K s.e) y x := by
  let eX := columnLabels rR zR middle hrR hzR hdisR s
  let eY := rowLabels rL zL middle hrL hzL hdisL s
  have hYa : inputValue (eY.symm y) s.a = y.1 () :=
    congrArg (fun p : (Unit → AES.Word) × (Unit → AES.Word) => p.1 ())
      (eY.apply_symm_apply y)
  have hYb : inputValue (eY.symm y) s.b = y.2 () :=
    congrArg (fun p : (Unit → AES.Word) × (Unit → AES.Word) => p.2 ())
      (eY.apply_symm_apply y)
  have hXb : outputValue (eX.symm x) s.b = x.1 () :=
    congrArg (fun p : (Unit → AES.Word) × (Unit → AES.Word) => p.1 ())
      (eX.apply_symm_apply x)
  have hXe : outputValue (eX.symm x) s.e = x.2 () :=
    congrArg (fun p : (Unit → AES.Word) × (Unit → AES.Word) => p.2 ())
      (eX.apply_symm_apply x)
  change (∏ i, K i (inputValue (eY.symm y) i) (outputValue (eX.symm x) i)) = _
  rw [prod_three s]
  simp only [AES8.InformationOverlap.kernel, Fintype.prod_unique]
  change
    K s.a (inputValue (eY.symm y) s.a) (outputValue (eX.symm x) s.a) *
      K s.b (inputValue (eY.symm y) s.b) (outputValue (eX.symm x) s.b) *
      K s.e (inputValue (eY.symm y) s.e) (outputValue (eX.symm x) s.e) =
    K s.a (y.1 ()) (outputValue (eX.symm x) s.a) *
      K s.b (y.2 ()) (x.1 ()) *
      K s.e (inputValue (eY.symm y) s.e) (x.2 ())
  rw [hYa, hYb, hXb, hXe]

/-- Reindex the exact tensor action for any signed joint image input. -/
theorem tensor_action_eq_overlap
    (K : MaskCoordinates middle → AES.Word → AES.Word → ℝ)
    (f : OutputImage rR zR middle → ℝ)
    (y : (Unit → AES.Word) × (Unit → AES.Word)) :
    action (tensorKernel K) f
      ((rowLabels rL zL middle hrL hzL hdisL s).symm y) =
      action (AES8.InformationOverlap.kernel
        (leftCode rR zR middle hrR hzR hdisR s)
        (rightCode rL zL middle hrL hzL hdisL s)
        (fun _ => K s.a) (fun _ => K s.b) (fun _ => K s.e))
        (fun x => f ((columnLabels rR zR middle hrR hzR hdisR s).symm x)) y := by
  let eX := columnLabels rR zR middle hrR hzR hdisR s
  unfold action
  rw [← eX.symm.sum_comp (fun x : OutputImage rR zR middle =>
    tensorKernel K ((rowLabels rL zL middle hrL hzL hdisL s).symm y) x * f x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [tensorKernel_eq_overlap rL zL rR zR middle hrL hzL hrR hzR hdisL hdisR s K y x]

include hrL hzL hrR hzR hdisL hdisR in
/-- Actual ordinary zero-fiber images inherit the overlap energy bound.
The hypotheses are precisely the selected column, shared operator, and row
resources; both coordinate labels of the signed input stay correlated. -/
theorem tensor_energy
    (K : MaskCoordinates middle → AES.Word → AES.Word → ℝ)
    (delta nu : ℝ) (hd : 0 ≤ delta)
    (hA : ∀ x, (∑ y, K s.a y x ^ 2) ≤ delta)
    (hB : ∀ g, (∑ y, action (K s.b) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hE : ∀ y, (∑ x, K s.e y x ^ 2) ≤ delta)
    (f : OutputImage rR zR middle → ℝ) :
    (∑ y : InputImage rL zL middle, action (tensorKernel K) f y ^ 2) ≤
      delta ^ 2 * nu ^ 2 * ∑ x : OutputImage rR zR middle, f x ^ 2 := by
  let eX := columnLabels rR zR middle hrR hzR hdisR s
  let eY := rowLabels rL zL middle hrL hzL hdisL s
  rw [← eY.symm.sum_comp (fun y : InputImage rL zL middle =>
    action (tensorKernel K) f y ^ 2)]
  change (∑ y, action (tensorKernel K) f
    ((rowLabels rL zL middle hrL hzL hdisL s).symm y) ^ 2) ≤ _
  simp_rw [tensor_action_eq_overlap rL zL rR zR middle hrL hzL hrR hzR hdisL hdisR s K f]
  have hb := AES8.InformationOverlap.information_overlap_energy
    (leftCode rR zR middle hrR hzR hdisR s)
    (rightCode rL zL middle hrL hzL hdisL s)
    (fun _ : Unit => K s.a) (fun _ : Unit => K s.b) (fun _ : Unit => K s.e)
    delta hd (fun _ : Unit => nu) (fun _ x => hA x) (fun _ g => hB g)
    (fun _ y => hE y) (fun x => f (eX.symm x))
  simp only [Fintype.card_unique, Fintype.prod_unique] at hb
  rw [eX.symm.sum_comp (fun x => f x ^ 2)] at hb
  exact hb

end Overlap
end AES8.MarkedZeroOverlap
