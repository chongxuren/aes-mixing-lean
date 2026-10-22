import AES8.Reductions.Source.PaperAESSourceMDS
import AES8.Math.PaperMDSOverlap
import AES8.Math.PaperMDSShortening
import AES8.Math.WordActivityFrame
import AESConcrete.WordCrossZero
import AESConcrete.WordFourierCore

/-!
# The physical marked word diffusion graph

The original code is the graph of `wordMixAddEquiv` over the word alphabet.
Zero constraints, the marked image, its dimension and its MDS information
sets are constructed from that graph. No byte-code correspondence is assumed.
Constructive proof development only; no attacks or numerical searches.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperWordGraphCode
open AESMixing PaperMDSGram PaperMDSFiber PaperMDSOverlap
open AESConcrete.WordCrossZero AESConcrete.WordFourierCore
attribute [local instance] Classical.propDecidable

section GenericShortening
variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The actual ambient codewords whose prescribed coordinates are zero. -/
def zeroShortening (C : AddSubgroup (K → V)) (Z : Finset K) :
    AddSubgroup (K → V) where
  carrier := {x | x ∈ C ∧ ∀ i ∈ Z, x i = 0}
  zero_mem' := ⟨C.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, hz⟩ ⟨hy, hw⟩
    exact ⟨C.add_mem hx hy, by intro i hi; simp [hz i hi, hw i hi]⟩
  neg_mem' := by
    rintro x ⟨hx, hz⟩
    exact ⟨C.neg_mem hx, by intro i hi; simp [hz i hi]⟩

def zeroShorteningEquiv (C : AddSubgroup (K → V)) (Z : Finset K) :
    zeroShortening C Z ≃ Fiber C Z (0 : K → V) where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def markedHom (C : AddSubgroup (K → V)) (Z M : Finset K) :
    zeroShortening C Z →+ (M → V) where
  toFun x i := x.val i.val
  map_zero' := rfl
  map_add' _ _ := rfl

def markedImage (C : AddSubgroup (K → V)) (Z M : Finset K) :
    AddSubgroup (M → V) := (markedHom C Z M).range

/-- Zero coordinates and selected marked coordinates keep their distinct
physical positions. -/
def selectedEmbedding {A : Type*} (Z M : Finset K) (hd : Disjoint Z M)
    (p : A → M) (hp : Function.Injective p) : Z ⊕ A ↪ K where
  toFun := Sum.elim Subtype.val (fun a => (p a).val)
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext h)
      | inr y =>
        change x.val = (p y).val at h
        exact False.elim (Finset.disjoint_left.mp hd x.property (by rw [h]; exact (p y).property))
    | inr x =>
      cases y with
      | inl y =>
        change (p x).val = y.val at h
        exact False.elim (Finset.disjoint_left.mp hd y.property (by rw [← h]; exact (p x).property))
      | inr y => exact congrArg Sum.inr (hp (Subtype.ext h))

/-- Fixing the zero coordinates and exactly the remaining number of selected
coordinates gives a bijection, inherited from the original information set. -/
theorem selected_projection_bijective {A : Type*} [Fintype A]
    (C : AddSubgroup (K → V)) (k : ℕ) (hC : IsMDS C k)
    (Z M : Finset K) (hd : Disjoint Z M) (p : A → M)
    (hp : Function.Injective p) (hcard : Z.card + Fintype.card A = k) :
    Function.Bijective (fun x : zeroShortening C Z => fun a => x.val (p a).val) := by
  have hb := restriction_bijective_of_card C k hC (selectedEmbedding Z M hd p hp)
    (by simpa only [Fintype.card_sum, Fintype.card_coe] using hcard)
  constructor
  · intro x y hxy
    apply Subtype.ext
    have he : (⟨x.val, x.property.1⟩ : C) = ⟨y.val, y.property.1⟩ := by
      apply hb.injective
      funext a
      cases a with
      | inl a => exact (x.property.2 a.val a.property).trans (y.property.2 a.val a.property).symm
      | inr a => exact congrFun hxy a
    exact congrArg (fun c : C => c.val) he
  · intro v
    obtain ⟨x, hx⟩ := hb.surjective (Sum.elim (fun _ => 0) v)
    refine ⟨⟨x.val, x.property, ?_⟩, ?_⟩
    · intro i hi
      exact congrFun hx (Sum.inl ⟨i, hi⟩)
    · funext a
      exact congrFun hx (Sum.inr a)

/-- Every information set of the restricted marked image is derived from
one original information set. -/
theorem markedImage_isMDS (C : AddSubgroup (K → V)) (k d : ℕ)
    (hC : IsMDS C k) (Z M : Finset K) (hd : Disjoint Z M)
    (hcard : Z.card + d = k) : IsMDS (markedImage C Z M) d := by
  intro p hp
  have hc : Fintype.card {i : M // p i} = d := by
    simpa only [Nat.card_eq_fintype_card] using hp
  have hb := selected_projection_bijective C k hC Z M hd
    (fun a : {i : M // p i} => a.val) Subtype.val_injective (by omega)
  constructor
  · intro x y hxy
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb'⟩ := y.property
    have hab : a = b := by
      apply hb.injective
      funext i
      change markedHom C Z M a i.val = markedHom C Z M b i.val
      rw [ha, hb']
      exact congrFun hxy i
    exact Subtype.ext (ha.symm.trans ((congrArg (markedHom C Z M) hab).trans hb'))
  · intro v
    obtain ⟨x, hx⟩ := hb.surjective v
    exact ⟨(markedHom C Z M).rangeRestrict x, hx⟩

theorem markedHom_injective (C : AddSubgroup (K → V)) (k d : ℕ)
    (hC : IsMDS C k) (Z M : Finset K) (hd : Disjoint Z M)
    (hcard : Z.card + d = k) (hlarge : d ≤ M.card) :
    Function.Injective (markedHom C Z M) := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show d ≤ (Finset.univ : Finset M).card by simpa using hlarge)
  have hb := selected_projection_bijective C k hC Z M hd
    (fun a : S => a.val) Subtype.val_injective
    (by simpa only [Fintype.card_coe, hS] using hcard)
  intro x y hxy
  apply hb.injective
  funext i
  exact congrFun hxy i.val

def markedSourceEquiv (C : AddSubgroup (K → V)) (k d : ℕ)
    (hC : IsMDS C k) (Z M : Finset K) (hd : Disjoint Z M)
    (hcard : Z.card + d = k) (hlarge : d ≤ M.card) :
    zeroShortening C Z ≃ markedImage C Z M :=
  Equiv.ofBijective (markedHom C Z M).rangeRestrict
    ⟨fun _ _ h => markedHom_injective C k d hC Z M hd hcard hlarge
      (congrArg Subtype.val h), (markedHom C Z M).rangeRestrict_surjective⟩

theorem markedImage_card (C : AddSubgroup (K → V)) (k d : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (Z M : Finset K) (hd : Disjoint Z M)
    (hcard : Z.card + d = k) (hlarge : d ≤ M.card) :
    Fintype.card (markedImage C Z M) = Fintype.card V ^ d := by
  rw [← Fintype.card_congr (markedSourceEquiv C k d hC Z M hd hcard hlarge),
    Fintype.card_congr (zeroShorteningEquiv C Z),
    prescribed_card C k hk hC Z (by omega) 0]
  congr 1
  omega

theorem zeroShortening_eq_zero (C : AddSubgroup (K → V)) (k : ℕ)
    (hC : IsMDS C k) (Z : Finset K) (hZ : k ≤ Z.card)
    (x : zeroShortening C Z) : x.val = 0 := by
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hZ
  have hb := (hC (fun i => i ∈ S) (by simpa using hcard)).injective
  have he : (⟨x.val, x.property.1⟩ : C) = 0 := by
    apply hb
    funext i
    exact x.property.2 i.val (hS i.property)
  exact congrArg Subtype.val he

theorem markedImage_eq_bot (C : AddSubgroup (K → V)) (k : ℕ)
    (hC : IsMDS C k) (Z M : Finset K) (hZ : k ≤ Z.card) :
    markedImage C Z M = ⊥ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change markedHom C Z M x = 0
    funext i
    exact congrFun (zeroShortening_eq_zero C k hC Z hZ x) i.val
  · intro hz
    have he : z = 0 := hz
    subst z
    exact (markedImage C Z M).zero_mem

theorem markedImage_eq_top (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (Z M : Finset K) (hd : Disjoint Z M) (hsmall : Z.card + M.card ≤ k) :
    markedImage C Z M = ⊤ := by
  ext z
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨x, hx⟩ := PaperMDSShortening.shortRestriction_surjective C k hk hC
      0 Z M hd 0 hsmall z
    refine ⟨⟨x.val, ?_, x.property.2⟩, ?_⟩
    · simpa using x.property.1
    · exact hx

/-- An injective physical marked restriction has one preimage per marked
codeword, including all zero constraints in the original graph sum. -/
theorem raw_indicator_fiber (C : AddSubgroup (K → V)) (Z M : Finset K)
    (hinj : Function.Injective (markedHom C Z M)) (z : M → V) :
    (∑ c : C, if (∀ i ∈ Z, c.val i = 0) ∧ (fun i : M => c.val i.val) = z
      then (1 : ℝ) else 0) = if z ∈ markedImage C Z M then 1 else 0 := by
  by_cases hz : z ∈ markedImage C Z M
  · have hz' := hz
    obtain ⟨a, ha⟩ := hz
    let c₀ : C := ⟨a.val, a.property.1⟩
    have hc₀ : (∀ i ∈ Z, c₀.val i = 0) ∧ (fun i : M => c₀.val i.val) = z :=
      ⟨a.property.2, ha⟩
    rw [if_pos hz']
    calc
      (∑ c : C, if (∀ i ∈ Z, c.val i = 0) ∧ (fun i : M => c.val i.val) = z
        then (1 : ℝ) else 0) =
          if (∀ i ∈ Z, c₀.val i = 0) ∧ (fun i : M => c₀.val i.val) = z then (1 : ℝ) else 0 := by
        apply Finset.sum_eq_single c₀
        · intro c _ hne
          split_ifs with hc
          · have he : c = c₀ := by
              apply Subtype.ext
              exact congrArg (fun v : zeroShortening C Z => v.val) (hinj (show markedHom C Z M
                ⟨c.val, c.property, hc.1⟩ = markedHom C Z M a from hc.2.trans ha.symm))
            exact False.elim (hne he)
          · rfl
        · simp
      _ = 1 := if_pos hc₀
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro c _
    split_ifs with hc
    · exact False.elim (hz ⟨⟨c.val, c.property, hc.1⟩, hc.2⟩)
    · rfl

def rawFiberEquiv (C : AddSubgroup (K → V)) (Z M : Finset K) (z : M → V) :
    {c : C // (∀ i ∈ Z, c.val i = 0) ∧ (fun i : M => c.val i.val) = z} ≃
      {c : Fiber C Z (0 : K → V) // observe C Z M 0 c = z} where
  toFun c := ⟨⟨c.val, c.property.1⟩, c.property.2⟩
  invFun c := ⟨c.val.val, c.val.property, c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem raw_indicator_full (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (Z M : Finset K) (hd : Disjoint Z M) (hsmall : Z.card + M.card ≤ k)
    (z : M → V) :
    (∑ c : C, if (∀ i ∈ Z, c.val i = 0) ∧ (fun i : M => c.val i.val) = z
      then (1 : ℝ) else 0) = (Fintype.card V : ℝ) ^ (k - (Z.card + M.card)) := by
  calc
    (∑ c : C, if (∀ i ∈ Z, c.val i = 0) ∧ (fun i : M => c.val i.val) = z then (1 : ℝ) else 0) =
        (Fintype.card {c : C // (∀ i ∈ Z, c.val i = 0) ∧ (fun i : M => c.val i.val) = z} : ℝ) := by
      convert real_indicator_card
        (fun c : C => (∀ i ∈ Z, c.val i = 0) ∧ (fun i : M => c.val i.val) = z) using 1
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> rfl
    _ = _ := by
      rw [Fintype.card_congr (rawFiberEquiv C Z M z),
        projection_fiber_card C k hk hC Z M hd hsmall 0 z, Nat.cast_pow]

def relabelHom {J : Type*} (C : AddSubgroup (K → V)) (e : K ≃ J) :
    C →+ (J → V) where
  toFun c j := c.val (e.symm j)
  map_zero' := rfl
  map_add' _ _ := rfl

def relabelCode {J : Type*} (C : AddSubgroup (K → V)) (e : K ≃ J) :
    AddSubgroup (J → V) := (relabelHom C e).range

theorem relabel_mem_iff {J : Type*} (C : AddSubgroup (K → V)) (e : K ≃ J)
    (z : J → V) : z ∈ relabelCode C e ↔ (fun i => z (e i)) ∈ C := by
  constructor
  · rintro ⟨c, hc⟩
    have he : (fun i => z (e i)) = c.val := by
      funext i
      have h := congrFun hc (e i)
      change c.val (e.symm (e i)) = z (e i) at h
      simpa only [e.symm_apply_apply] using h.symm
    rw [he]
    exact c.property
  · intro hz
    refine ⟨⟨fun i => z (e i), hz⟩, ?_⟩
    funext j
    simp [relabelHom]

theorem relabel_isMDS {J : Type*} [Fintype J] [DecidableEq J]
    (C : AddSubgroup (K → V)) (e : K ≃ J) (d : ℕ) (hC : IsMDS C d) :
    IsMDS (relabelCode C e) d := by
  intro p hp
  have hb := restriction_bijective_of_card C d hC
    (⟨fun a : {j : J // p j} => e.symm a.val,
      fun _ _ h => Subtype.ext (e.symm.injective h)⟩ : {j : J // p j} ↪ K)
    (by simpa only [Nat.card_eq_fintype_card] using hp)
  constructor
  · intro x y hxy
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb'⟩ := y.property
    have hab : a = b := by
      apply hb.injective
      funext j
      change relabelHom C e a j.val = relabelHom C e b j.val
      rw [ha, hb']
      exact congrFun hxy j
    exact Subtype.ext (ha.symm.trans ((congrArg (relabelHom C e) hab).trans hb'))
  · intro v
    obtain ⟨c, hc⟩ := hb.surjective v
    exact ⟨(relabelHom C e).rangeRestrict c, hc⟩

end GenericShortening

abbrev Position := Fin 4 ⊕ Fin 4
abbrev wordGraph : AddSubgroup (Position → AES.Word) :=
  PaperRestrictedDiffusion.graph wordMixAddEquiv.toAddMonoidHom

theorem wordGraph_isMDS : IsMDS wordGraph 4 :=
  PaperAESSource.graph_isMDS_of_zeroMDS _ wordMixAddEquiv_zeroMDS

def zeroPositions (M U : Finset Position) : Finset Position := (M ∪ U)ᶜ
def markedCode (M U : Finset Position) : AddSubgroup (M → AES.Word) :=
  markedImage wordGraph (zeroPositions M U) M

theorem zero_marked_disjoint (M U : Finset Position) :
    Disjoint (zeroPositions M U) M := by
  exact Finset.disjoint_left.mpr (by intro i hi hj; exact (Finset.mem_compl.mp hi) (Finset.mem_union_left U hj))

/-- The preliminary signed dimension is expressed in integers, before any
proper-branch natural dimension is introduced. -/
theorem signed_dimension (M U : Finset Position) (hd : Disjoint M U) :
    (4 : ℤ) - (zeroPositions M U).card = (M.card : ℤ) + U.card - 4 := by
  have hc : (zeroPositions M U).card + (M.card + U.card) = 8 := by
    rw [← Finset.card_union_of_disjoint hd]
    simpa only [zeroPositions, Finset.card_compl, Fintype.card_sum, Fintype.card_fin]
      using Finset.card_compl_add_card (M ∪ U)
  omega

theorem activity_count (M U : Finset Position) (hd : Disjoint M U)
    (d : ℕ) (hdim : (zeroPositions M U).card + d = 4) :
    (U.card : ℤ) = (d : ℤ) + 4 - M.card := by
  have h := signed_dimension M U hd
  omega

theorem activity_count_real (M U : Finset Position) (hd : Disjoint M U)
    (d : ℕ) (hdim : (zeroPositions M U).card + d = 4) :
    (U.card : ℝ) = (d : ℝ) + 4 - M.card := by
  have hz := activity_count M U hd d hdim
  have hn : U.card + M.card = d + 4 := by omega
  have hr : (U.card : ℝ) + M.card = (d : ℝ) + 4 := by exact_mod_cast hn
  linarith

theorem markedCode_isMDS (M U : Finset Position) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) : IsMDS (markedCode M U) d :=
  markedImage_isMDS wordGraph 4 d wordGraph_isMDS (zeroPositions M U) M
    (zero_marked_disjoint M U) hdim

theorem markedCode_card (M U : Finset Position) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hlarge : d ≤ M.card) :
    Fintype.card (markedCode M U) = Fintype.card AES.Word ^ d := by
  exact markedImage_card wordGraph 4 d (by simp) wordGraph_isMDS
    (zeroPositions M U) M (zero_marked_disjoint M U) hdim hlarge

theorem zero_frame_product (Z : Finset Position) (x : Position → AES.Word) :
    (∏ i : Z, WordActivityFrame.wordFrame 0 false (x i.val)) =
      if ∀ i ∈ Z, x i = 0 then 1 else 0 := by
  by_cases hz : ∀ i ∈ Z, x i = 0
  · rw [if_pos hz]
    apply Finset.prod_eq_one
    intro i _
    simp [WordActivityFrame.wordFrame, identityKernel, hz i.val i.property]
  · rw [if_neg hz]
    push_neg at hz
    obtain ⟨i, hi, hx⟩ := hz
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨i, hi⟩ : Z))
    simp [WordActivityFrame.wordFrame, identityKernel, hx]

def graphContraction (M U : Finset Position) (z : M → AES.Word) : ℝ :=
  ∑ c : wordGraph,
    (if (fun i : M => c.val i.val) = z then 1 else 0) *
      (∏ i : U, WordActivityFrame.wordFrame 0 true (c.val i.val)) *
      ∏ i : zeroPositions M U, WordActivityFrame.wordFrame 0 false (c.val i.val)

theorem graphContraction_factor (M U : Finset Position) (z : M → AES.Word) :
    graphContraction M U z = WordActivityFrame.xi AES.Word ^ U.card *
      ∑ c : wordGraph, if (∀ i ∈ zeroPositions M U, c.val i = 0) ∧
        (fun i : M => c.val i.val) = z then 1 else 0 := by
  rw [graphContraction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [zero_frame_product]
  have hu : (∏ i : U, WordActivityFrame.wordFrame 0 true (c.val i.val)) =
      WordActivityFrame.xi AES.Word ^ U.card := by simp [WordActivityFrame.wordFrame]
  rw [hu]
  by_cases hZ : ∀ i ∈ zeroPositions M U, c.val i = 0 <;>
    by_cases hM : (fun i : M => c.val i.val) = z <;> simp [hZ, hM]

theorem frame_scalar_rpow (a : ℕ) :
    WordActivityFrame.xi AES.Word ^ a =
      Real.rpow (4294967296 : ℝ) (-(a : ℝ) / 2) := by
  have hc : (Fintype.card AES.Word : ℝ) = 4294967296 := by rw [word_card]; norm_num
  rw [WordActivityFrame.xi, WordActivityFrame.q, hc, Real.sqrt_eq_rpow,
    one_div, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4294967296),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 4294967296)]
  congr 1
  ring

/-- Literal contraction of the actual word graph against its zero and
uniform frame vectors. The coefficient and unique preimage are derived. -/
theorem graphContraction_eq (M U : Finset Position) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hlarge : d ≤ M.card)
    (z : M → AES.Word) :
    graphContraction M U z =
      Real.rpow (4294967296 : ℝ) (-(U.card : ℝ) / 2) *
        if z ∈ markedCode M U then 1 else 0 := by
  have hb := raw_indicator_fiber wordGraph (zeroPositions M U) M
    (markedHom_injective wordGraph 4 d wordGraph_isMDS (zeroPositions M U) M
      (zero_marked_disjoint M U) hdim hlarge) z
  rw [graphContraction]
  simp_rw [zero_frame_product]
  have hu (c : wordGraph) :
      (∏ i : U, WordActivityFrame.wordFrame 0 true (c.val i.val)) =
        WordActivityFrame.xi AES.Word ^ U.card := by
    simp [WordActivityFrame.wordFrame]
  simp_rw [hu]
  rw [← frame_scalar_rpow]
  change _ = WordActivityFrame.xi AES.Word ^ U.card *
    (if z ∈ markedImage wordGraph (zeroPositions M U) M then 1 else 0)
  rw [← hb, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hZ : ∀ i ∈ zeroPositions M U, c.val i = 0 <;>
    by_cases hM : (fun i : M => c.val i.val) = z <;> simp [hZ, hM]

theorem markedCode_zero_branch (M U : Finset Position)
    (hZ : 4 ≤ (zeroPositions M U).card) : markedCode M U = ⊥ :=
  markedImage_eq_bot wordGraph 4 wordGraph_isMDS (zeroPositions M U) M hZ

theorem markedCode_full_branch (M U : Finset Position)
    (hfull : (zeroPositions M U).card + M.card ≤ 4) : markedCode M U = ⊤ :=
  markedImage_eq_top wordGraph 4 (by simp) wordGraph_isMDS
    (zeroPositions M U) M (zero_marked_disjoint M U) hfull

theorem graphContraction_zero_branch (M U : Finset Position)
    (hZ : 4 ≤ (zeroPositions M U).card) (z : M → AES.Word) :
    graphContraction M U z = WordActivityFrame.xi AES.Word ^ U.card *
      if z = 0 then 1 else 0 := by
  rw [graphContraction_factor]
  have hinj : Function.Injective (markedHom wordGraph (zeroPositions M U) M) := by
    intro x y _
    apply Subtype.ext
    exact (zeroShortening_eq_zero wordGraph 4 wordGraph_isMDS _ hZ x).trans
      (zeroShortening_eq_zero wordGraph 4 wordGraph_isMDS _ hZ y).symm
  rw [raw_indicator_fiber wordGraph (zeroPositions M U) M hinj z,
    ← markedCode, markedCode_zero_branch M U hZ]
  simp only [AddSubgroup.mem_bot]

theorem graphContraction_full_branch (M U : Finset Position)
    (hfull : (zeroPositions M U).card + M.card ≤ 4) (z : M → AES.Word) :
    graphContraction M U z = WordActivityFrame.xi AES.Word ^ U.card *
      (Fintype.card AES.Word : ℝ) ^ (4 - ((zeroPositions M U).card + M.card)) := by
  rw [graphContraction_factor, raw_indicator_full wordGraph 4 (by simp)
    wordGraph_isMDS (zeroPositions M U) M (zero_marked_disjoint M U) hfull z]

/-- The displayed graph coefficient follows from the actual activity count,
with no truncated subtraction in the exponent. -/
theorem graphContraction_eq_graphCoefficient (M U : Finset Position)
    (hd : Disjoint M U) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hlarge : d ≤ M.card)
    (z : M → AES.Word) :
    graphContraction M U z =
      Real.rpow (4294967296 : ℝ) (((M.card : ℝ) - 4 - (d : ℝ)) / 2) *
        if z ∈ markedCode M U then 1 else 0 := by
  rw [graphContraction_eq M U d hdim hlarge z, activity_count_real M U hd d hdim]
  congr 2
  ring

end AES8.PaperWordGraphCode
