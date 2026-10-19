import AESMixing.MDSInterpolation
import AESMixing.MDSGraphCount

/-!
# MDS zero-event mass for independent source laws

Prescribing k output zeros and retaining the complementary input coordinates
is an exact MDS information set. The frozen additive information-set theorem
therefore gives one source vector per complementary tuple. Capping the k
selected source factors by p, while retaining every remaining source weight,
bounds the unnormalized event mass by p^k. No event probability is divided out.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ZeroEventMDS
open AESMixing
open AESMixing.AES (maskBit maskSize)

local instance (c : Fin 16) : DecidableEq (ComplementCoordinates c) :=
  inferInstanceAs (DecidableEq {i : Fin 4 // maskBit c i ≠ true})

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The prescribed output coordinates are zero; every other output is free. -/
def outputZero (L : (Fin 4 → V) →+ (Fin 4 → V)) (r : Fin 16) (x : Fin 4 → V) : Prop :=
  ∀ i : Fin 4, maskBit r i = true → L x i = 0

instance (L : (Fin 4 → V) →+ (Fin 4 → V)) (r : Fin 16) :
    DecidablePred (outputZero L r) := by
  intro x
  unfold outputZero
  infer_instance

/-- Original independent source mass, restricted without normalization. -/
def eventMass (L : (Fin 4 → V) →+ (Fin 4 → V)) (r : Fin 16)
    (f : Fin 4 → V → ℝ) : ℝ :=
  ∑ x : Fin 4 → V, if outputZero L r x then ∏ i, f i (x i) else 0

/-- Selected outputs and complementary inputs determine the full source. -/
def informationEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c) :
    (Fin 4 → V) ≃ (MaskCoordinates r → V) × (ComplementCoordinates c → V) :=
  Equiv.ofBijective (mdsInformation L r c) (mds_information_bijective L hL r c hsize)

theorem informationEquiv_symm_output
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c)
    (v : (MaskCoordinates r → V) × (ComplementCoordinates c → V))
    (i : MaskCoordinates r) :
    L ((informationEquiv L hL r c hsize).symm v) i.val = v.1 i := by
  have h := congrFun (congrArg Prod.fst
    ((informationEquiv L hL r c hsize).apply_symm_apply v)) i
  exact h

theorem informationEquiv_symm_complement
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c)
    (v : (MaskCoordinates r → V) × (ComplementCoordinates c → V))
    (i : ComplementCoordinates c) :
    (informationEquiv L hL r c hsize).symm v i.val = v.2 i := by
  have h := congrFun (congrArg Prod.snd
    ((informationEquiv L hL r c hsize).apply_symm_apply v)) i
  exact h

theorem outputZero_iff_information
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c) (x : Fin 4 → V) :
    outputZero L r x ↔ (informationEquiv L hL r c hsize x).1 = 0 := by
  constructor
  · intro h
    funext i
    exact h i.val i.property
  · intro h i hi
    exact congrFun h (⟨i,hi⟩ : MaskCoordinates r)

theorem outputZero_information_symm
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c)
    (v : (MaskCoordinates r → V) × (ComplementCoordinates c → V)) :
    outputZero L r ((informationEquiv L hL r c hsize).symm v) ↔ v.1 = 0 := by
  rw [outputZero_iff_information L hL r c hsize,
    (informationEquiv L hL r c hsize).apply_symm_apply]

/-- Exact section sum, retaining all source probabilities in their original form. -/
theorem eventMass_eq_sections
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c) (f : Fin 4 → V → ℝ) :
    eventMass L r f = ∑ v : ComplementCoordinates c → V,
      ∏ i : Fin 4, f i ((informationEquiv L hL r c hsize).symm (0,v) i) := by
  let e := informationEquiv L hL r c hsize
  have he := Equiv.sum_comp e.symm
    (fun x : Fin 4 → V => if outputZero L r x then ∏ i, f i (x i) else 0)
  have hz (v : (MaskCoordinates r → V) × (ComplementCoordinates c → V)) :
      outputZero L r (e.symm v) ↔ v.1=0 := outputZero_information_symm L hL r c hsize v
  calc
    _ = ∑ v : (MaskCoordinates r → V) × (ComplementCoordinates c → V),
        if outputZero L r (e.symm v) then ∏ i, f i (e.symm v i) else 0 := he.symm
    _ = ∑ u : MaskCoordinates r → V, ∑ v : ComplementCoordinates c → V,
        if u=0 then ∏ i, f i (e.symm (u,v) i) else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [hz]
    _ = ∑ v : ComplementCoordinates c → V, ∏ i, f i (e.symm (0,v) i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Cap only the selected factors; every complementary factor is retained. -/
theorem source_product_le (c : Fin 16) (f : Fin 4 → V → ℝ) (p : ℝ)
    (hf : ∀ i x, 0 ≤ f i x)
    (hcap : ∀ i, maskBit c i=true → ∀ x, f i x ≤ p) (x : Fin 4 → V) :
    (∏ i, f i (x i)) ≤ p ^ maskSize c *
      ∏ i : ComplementCoordinates c, f i.val (x i.val) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin 4 => maskBit c i=true)]
  have hc : (∏ i : MaskCoordinates c, f i.val (x i.val)) ≤ p ^ maskSize c := by
    calc
      _ ≤ ∏ _i : MaskCoordinates c, p := Finset.prod_le_prod
        (fun i _ => hf i.val (x i.val)) (fun i _ => hcap i.val i.property (x i.val))
      _ = p ^ maskSize c := by
        simp only [Finset.prod_const, Finset.card_univ, maskCoordinates_card]
  exact mul_le_mul_of_nonneg_right hc
    (Finset.prod_nonneg (fun i _ => hf i.val (x i.val)))

/-- The MDS zero-event cap, with unnormalized mass and no output independence. -/
theorem eventMass_le
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c)
    (f : Fin 4 → V → ℝ) (p : ℝ) (_hp : 0 ≤ p)
    (hf : ∀ i x, 0 ≤ f i x) (hmass : ∀ i, (∑ x, f i x) = 1)
    (hcap : ∀ i, maskBit c i=true → ∀ x, f i x ≤ p) :
    eventMass L r f ≤ p ^ maskSize r := by
  rw [eventMass_eq_sections L hL r c hsize]
  calc
    _ ≤ ∑ v : ComplementCoordinates c → V,
        p ^ maskSize c * ∏ i : ComplementCoordinates c, f i.val (v i) := by
      apply Finset.sum_le_sum
      intro v _
      have h := source_product_le c f p hf hcap
        ((informationEquiv L hL r c hsize).symm (0,v))
      simpa only [informationEquiv_symm_complement] using h
    _ = p ^ maskSize c * ∑ v : ComplementCoordinates c → V,
        ∏ i : ComplementCoordinates c, f i.val (v i) := by rw [Finset.mul_sum]
    _ = p ^ maskSize c := by
      rw [← Fintype.prod_sum
        (fun (i : ComplementCoordinates c) (v : V) => f i.val v)]
      simp only [hmass, Finset.prod_const_one, mul_one]
    _ = p ^ maskSize r := by rw [hsize]

/-- Four or more prescribed graph zeros force the entire source to zero. -/
theorem outputZero_inputZero_eq_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hsize : 4 ≤ maskSize r+maskSize z) (x : Fin 4 → V)
    (ho : outputZero L r x) (hi : ∀ i, maskBit z i=true → x i=0) : x=0 :=
  mds_graph_zero_high L hL r z hsize x ⟨ho,hi⟩

end AESPaper.ZeroEventMDS
