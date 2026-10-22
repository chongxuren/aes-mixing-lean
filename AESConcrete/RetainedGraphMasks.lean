import AESConcrete.ActivityMinorCounting
import AESConcrete.GeneralMDSGraphSupport

/-!
# Physical free masks inside a full-active retained output

coordinate bookkeeping only. The finite mask lemmas enumerate the sixteen
subsets of four physical labels; they never enumerate AES words. There are no
energy inequalities, analytic estimates, AES caps or inventory changes. No
singleton source is imported.

Independent retained uniform keys, whitening, omitted final MixColumns,
ordered-distinct pairs and fixed 10/14/16 remain unchanged.
-/

noncomputable section

namespace AESConcrete.RetainedGraphMasks
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ActivityMinor (selectedRetained selectedZeros)
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Inclusion of actual physical coordinate labels. -/
def Submask (m r : Fin 16) : Prop :=
  ∀ i : Fin 4, maskBit m i = true → maskBit r i = true

instance (m r : Fin 16) : Decidable (Submask m r) := by
  unfold Submask
  infer_instance

-- These small exact finite statements concern masks and four labels only.
-- No classical predicate instance is installed here: the finite deciders use
-- the ordinary computable Boolean-mask predicates.
private theorem exists_submask_of_size : ∀ (r : Fin 16) (b : Fin 5),
    b.val ≤ maskSize r → ∃ m : Fin 16, maskSize m = b.val ∧ Submask m r := by
  decide

private theorem mask_retainedOutside_card : ∀ (r m : Fin 16), Submask m r →
    Fintype.card {i : OtherCoordinates m // maskBit r i.val = true} =
      maskSize r - maskSize m := by
  decide

private theorem mask_omittedOutside_card : ∀ (r m : Fin 16), Submask m r →
    Fintype.card {i : OtherCoordinates m // maskBit r i.val ≠ true} =
      4 - maskSize r := by
  decide

private theorem empty_mask_bit : ∀ (r : Fin 16), maskSize r = 0 →
    ∀ i : Fin 4, maskBit r i ≠ true := by
  decide

/-- Full active count means that no output coordinate is pinned to zero. -/
theorem fullActive_selectedZeros_empty (d : Fin 5) (p : SelectedSupport d 4) :
    ∀ i : Fin 4, ¬ selectedZeros d 4 p i := by
  have hz : maskSize p.val.val.2 = 0 := by
    have hp := p.property
    omega
  intro i
  exact empty_mask_bit p.val.val.2 hz i

/-- Any requested number b≤d of free physical labels can be retained labels. -/
theorem exists_retained_freeMask (d b : Fin 5) (hbd : b ≤ d)
    (p : SelectedSupport d 4) :
    ∃ m : Fin 16, maskSize m = b.val ∧ Submask m p.val.val.1 := by
  apply exists_submask_of_size p.val.val.1 b
  rw [p.val.property.2]
  exact hbd

/-- A fixed mask choice for a given actual output support. It depends on no
source amplitude, codeword, channel or analytic parameter. -/
def freeMask (d b : Fin 5) (hbd : b ≤ d) (p : SelectedSupport d 4) : Fin 16 :=
  Classical.choose (exists_retained_freeMask d b hbd p)

theorem freeMask_spec (d b : Fin 5) (hbd : b ≤ d) (p : SelectedSupport d 4) :
    maskSize (freeMask d b hbd p) = b.val ∧
      Submask (freeMask d b hbd p) p.val.val.1 :=
  Classical.choose_spec (exists_retained_freeMask d b hbd p)

theorem freeMask_size (d b : Fin 5) (hbd : b ≤ d) (p : SelectedSupport d 4) :
    maskSize (freeMask d b hbd p) = b.val := (freeMask_spec d b hbd p).1

theorem freeMask_retained (d b : Fin 5) (hbd : b ≤ d)
    (p : SelectedSupport d 4) :
    ∀ i : Fin 4, maskBit (freeMask d b hbd p) i = true → selectedRetained d 4 p i :=
  (freeMask_spec d b hbd p).2

theorem freeCoordinates_card (d b : Fin 5) (hbd : b ≤ d) (p : SelectedSupport d 4) :
    Fintype.card (MaskCoordinates (freeMask d b hbd p)) = b.val :=
  (maskCoordinates_card _).trans (freeMask_size d b hbd p)

/-- Retained residual labels outside the chosen free information set. -/
abbrev DependentRetained (d : Fin 5) (p : SelectedSupport d 4) (m : Fin 16) :=
  {i : OtherCoordinates m // selectedRetained d 4 p i.val}

/-- Omitted output labels, all outside the free set when the set is retained. -/
abbrev DependentOmitted (d : Fin 5) (p : SelectedSupport d 4) (m : Fin 16) :=
  {i : OtherCoordinates m // ¬ selectedRetained d 4 p i.val}

-- Expose the actual Boolean predicates to instance synthesis. The subtype
-- aliases are reducible, but selectedRetained itself is an ordinary definition.
instance dependentRetainedFintype (d : Fin 5) (p : SelectedSupport d 4) (m : Fin 16) :
    Fintype (DependentRetained d p m) := by
  change Fintype {i : OtherCoordinates m // maskBit p.val.val.1 i.val = true}
  infer_instance

instance dependentOmittedFintype (d : Fin 5) (p : SelectedSupport d 4) (m : Fin 16) :
    Fintype (DependentOmitted d p m) := by
  change Fintype {i : OtherCoordinates m // maskBit p.val.val.1 i.val ≠ true}
  infer_instance

theorem dependentRetained_card (d : Fin 5) (p : SelectedSupport d 4)
    (m : Fin 16) (hm : Submask m p.val.val.1) :
    Fintype.card (DependentRetained d p m) = d.val - maskSize m := by
  have hc := mask_retainedOutside_card p.val.val.1 m hm
  rw [p.val.property.2] at hc
  simpa only [← Nat.card_eq_fintype_card, DependentRetained, selectedRetained] using hc

theorem dependentOmitted_card (d : Fin 5) (p : SelectedSupport d 4)
    (m : Fin 16) (hm : Submask m p.val.val.1) :
    Fintype.card (DependentOmitted d p m) = 4 - d.val := by
  have hc := mask_omittedOutside_card p.val.val.1 m hm
  rw [p.val.property.2] at hc
  simpa only [← Nat.card_eq_fintype_card, DependentOmitted, selectedRetained] using hc

theorem freeMask_dependentRetained_card (d b : Fin 5) (hbd : b ≤ d)
    (p : SelectedSupport d 4) :
    Fintype.card (DependentRetained d p (freeMask d b hbd p)) = d.val - b.val := by
  have hc := dependentRetained_card d p (freeMask d b hbd p) (freeMask_spec d b hbd p).2
  rw [freeMask_size] at hc
  exact hc

theorem freeMask_dependentOmitted_card (d b : Fin 5) (hbd : b ≤ d)
    (p : SelectedSupport d 4) :
    Fintype.card (DependentOmitted d p (freeMask d b hbd p)) = 4 - d.val :=
  dependentOmitted_card d p (freeMask d b hbd p) (freeMask_spec d b hbd p).2

theorem freeMask_dependentCoordinates_card (d b : Fin 5) (hbd : b ≤ d)
    (p : SelectedSupport d 4) :
    Fintype.card (OtherCoordinates (freeMask d b hbd p)) = 4 - b.val := by
  rw [GeneralMDSGraphSupport.otherCoordinates_card, freeMask_size]

/-- The two dependent subtypes account for all labels outside the free mask. -/
theorem freeMask_dependent_partition (d b : Fin 5) (hbd : b ≤ d)
    (p : SelectedSupport d 4) :
    Fintype.card (DependentRetained d p (freeMask d b hbd p)) +
      Fintype.card (DependentOmitted d p (freeMask d b hbd p)) =
        Fintype.card (OtherCoordinates (freeMask d b hbd p)) := by
  rw [freeMask_dependentRetained_card, freeMask_dependentOmitted_card,
    freeMask_dependentCoordinates_card]
  have hd := d.isLt
  change b.val ≤ d.val at hbd
  omega

theorem omitted_not_free (d b : Fin 5) (hbd : b ≤ d) (p : SelectedSupport d 4)
    (i : Fin 4) (hi : ¬ selectedRetained d 4 p i) :
    maskBit (freeMask d b hbd p) i ≠ true := by
  intro hm
  exact hi (freeMask_retained d b hbd p i hm)

end AESConcrete.RetainedGraphMasks
