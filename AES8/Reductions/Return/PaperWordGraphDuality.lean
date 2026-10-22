import AES8.Reductions.Return.PaperWordGraphCode
import AESConcrete.WordFourierClosure
import AESConcrete.WordFourierVariants
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact raw marked-word graph duality

The graph coefficient is normalized from the actual MDS cardinality. The
two graph choices are independent, with the Fourier factors transported
through the actual global word residual projection. These are kernel
identities for arbitrary real input; no norm or return cap is a premise.
Constructive proof development only; no attacks or numerical searches.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperWordGraphDuality
open AESMixing PaperMDSGram PaperMDSFiber PaperWordGraphCode
open AESConcrete.WordFourierCore
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option autoImplicit false

abbrev Word := AES.Word
def q : ℝ := 4294967296
def graphCoefficient (i m d : ℕ) : ℝ :=
  Real.rpow q (((i : ℝ) + (m : ℝ) - 4 - (d : ℝ)) / 2)
def rawGraphMatrix {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → Word))
    (c : ℝ) (y : Fin i → Word) (x : Fin m → Word) : ℝ :=
  c * if Sum.elim y x ∈ C then 1 else 0
def K {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) (d : ℕ) :=
  rawGraphMatrix C (graphCoefficient i m d)
def F (n : ℕ) := coordinateKernel (fun _ : Fin n => wordFourier)
def P (n : ℕ) := coordinateKernel (fun _ : Fin n => residualProjection (0 : Word))
abbrev dual {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) :=
  (AESConcrete.WordFourierCore.wordPairing.product (Fin i ⊕ Fin m)).annihilator C
def transpose {A B : Type*} (T : A → B → ℝ) (b : B) (a : A) : ℝ := T a b
def unitMatrix {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → Word))
    (y : Fin i → Word) (x : Fin m → Word) : ℝ :=
  unitSubgroupIndicator C (Sum.elim y x)

theorem unitIndicator_instances {X : Type*} [AddCommGroup X]
    (C : AddSubgroup X) (f g : Fintype C) (x : X) :
    @unitSubgroupIndicator X _ C f x = @unitSubgroupIndicator X _ C g x := by
  have h : f = g := Subsingleton.elim _ _
  cases h
  rfl

theorem compose_assoc {A B C D : Type*} [Fintype B] [Fintype C]
    (T : A → B → ℝ) (U : B → C → ℝ) (V : C → D → ℝ) :
    kernelCompose (kernelCompose T U) V = kernelCompose T (kernelCompose U V) := by
  funext a d
  simp only [kernelCompose, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem compose_identity_left {A B : Type*} [Fintype A] [DecidableEq A]
    (T : A → B → ℝ) : kernelCompose identityKernel T = T := by
  funext a b
  simp [kernelCompose, identityKernel]

theorem compose_identity_right {A B : Type*} [Fintype B] [DecidableEq B]
    (T : A → B → ℝ) : kernelCompose T identityKernel = T := by
  funext a b
  simp [kernelCompose, identityKernel]

theorem compose_transpose {A B C : Type*} [Fintype B]
    (T : A → B → ℝ) (U : B → C → ℝ) :
    transpose (kernelCompose T U) = kernelCompose (transpose U) (transpose T) := by
  funext c a
  exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

theorem word_right_fourier (T : Word → Word → ℝ) :
    kernelCompose T wordFourier = kernelCompose wordFourier (wordConjugate T) := by
  rw [wordConjugate, fourierConjugate]
  change _ = kernelCompose wordFourier (kernelCompose wordFourier (kernelCompose T wordFourier))
  rw [← compose_assoc, wordFourier_comp_self, compose_identity_left]

theorem F_symmetric (n : ℕ) : transpose (F n) = F n := by
  funext y x
  change (∏ i : Fin n, wordFourier (x i) (y i)) = ∏ i : Fin n, wordFourier (y i) (x i)
  exact Finset.prod_congr rfl (fun i _ => wordFourier_symmetric (x i) (y i))

theorem F_comp_self (n : ℕ) : kernelCompose (F n) (F n) = identityKernel := by
  apply kernel_action_ext
  intro f
  have he := pairingFourier_twice (AESConcrete.WordFourierCore.wordPairing.product (Fin n))
    (fun x => by funext i; exact word_add_self (x i)) f
  simpa only [productPairing_fourier, F, wordFourier, kernelCompose_action,
    identityKernel_action] using he

theorem F_energy (n : ℕ) (f : (Fin n → Word) → ℝ) :
    (∑ y, action (F n) f y ^ 2) = ∑ x, f x ^ 2 := by
  simpa only [productPairing_fourier, F, wordFourier] using
    pairingFourier_energy (AESConcrete.WordFourierCore.wordPairing.product (Fin n))
      (fun x => by funext i; exact word_add_self (x i)) f

theorem mds_card {I : Type*} [Fintype I] [DecidableEq I]
    (C : AddSubgroup (I → Word)) (d : ℕ) (hd : d ≤ Fintype.card I)
    (hC : IsMDS C d) : Fintype.card C = Fintype.card Word ^ d := by
  let e : C ≃ Fiber C ∅ (0 : I → Word) :=
    { toFun := fun c => ⟨c, by simp⟩
      invFun := fun c => c.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, prescribed_card C d hd hC ∅ (by simp) 0]
  simp

theorem sqrt_word_pow (d : ℕ) :
    Real.sqrt ((Fintype.card Word ^ d : ℕ) : ℝ) = Real.rpow q ((d : ℝ) / 2) := by
  have hc : (Fintype.card Word : ℝ) = q := by rw [word_card]; norm_num [q]
  rw [Nat.cast_pow, hc, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast_mul (by norm_num [q] : (0 : ℝ) ≤ q)]
  congr 1
  ring

/-- The coefficient multiplying the unit indicator is independent of the
MDS dimension. This is the exact source of the absence of an extra norm. -/
theorem K_eq_unit {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) (d : ℕ)
    (hd : d ≤ i + m) (hC : IsMDS C d) :
    K C d = fun y x => Real.rpow q (((i : ℝ) + (m : ℝ) - 4) / 2) *
      unitMatrix C y x := by
  have hc := mds_card C d (by simpa using hd) hC
  have hq : 0 < q := by norm_num [q]
  have hs : graphCoefficient i m d =
      Real.rpow q (((i : ℝ) + (m : ℝ) - 4) / 2) /
        Real.sqrt (Fintype.card C) := by
    rw [hc, sqrt_word_pow]
    change q ^ (((i : ℝ) + (m : ℝ) - 4 - (d : ℝ)) / 2) =
      q ^ (((i : ℝ) + (m : ℝ) - 4) / 2) / q ^ ((d : ℝ) / 2)
    rw [← Real.rpow_sub hq]
    congr 1
    ring
  funext y x
  by_cases hm : Sum.elim y x ∈ C <;>
    simp [K, rawGraphMatrix, unitMatrix, unitSubgroupIndicator, hm, hs, div_eq_mul_inv]

def physicalCode {i m : ℕ} (M U : Finset PaperWordGraphCode.Position)
    (e : M ≃ Fin i ⊕ Fin m) : AddSubgroup ((Fin i ⊕ Fin m) → Word) :=
  relabelCode (markedCode M U) e

theorem physicalCode_isMDS {i m : ℕ} (M U : Finset PaperWordGraphCode.Position)
    (e : M ≃ Fin i ⊕ Fin m) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) : IsMDS (physicalCode M U e) d :=
  relabel_isMDS (markedCode M U) e d (markedCode_isMDS M U d hdim)

/-- Every arbitrary split of the marked physical positions produces exactly
the raw matrix used by the graph-return estimates. -/
theorem physical_graph_matrix {i m : ℕ} (M U : Finset PaperWordGraphCode.Position)
    (hd : Disjoint M U) (e : M ≃ Fin i ⊕ Fin m) (d : ℕ)
    (hdim : (zeroPositions M U).card + d = 4) (hlarge : d ≤ M.card)
    (y : Fin i → Word) (x : Fin m → Word) :
    graphContraction M U (fun a => Sum.elim y x (e a)) = K (physicalCode M U e) d y x := by
  have hc : M.card = i + m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  simpa only [K, rawGraphMatrix, graphCoefficient, q, physicalCode, relabel_mem_iff,
    hc, Nat.cast_add] using
      graphContraction_eq_graphCoefficient M U hd d hdim hlarge (fun a => Sum.elim y x (e a))

theorem unit_dual_conjugate {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) :
    kernelCompose (kernelCompose (F i) (unitMatrix C)) (F m) = unitMatrix (dual C) := by
  funext y x
  have h := congrFun (pairingFourier_subgroup
    (AESConcrete.WordFourierCore.wordPairing.product (Fin i ⊕ Fin m)) C) (Sum.elim y x)
  rw [productPairing_fourier] at h
  unfold action at h
  rw [← (Equiv.sumArrowEquivProdArrow (Fin i) (Fin m) Word).symm.sum_comp
    (fun z => coordinateKernel (fun _ : Fin i ⊕ Fin m => pairingFourier AESConcrete.WordFourierCore.wordPairing)
      (Sum.elim y x) z * unitSubgroupIndicator C z), Fintype.sum_prod_type] at h
  simp only [coordinateKernel, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at h
  convert h using 1
  · simp only [kernelCompose, F, coordinateKernel, unitMatrix, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have hs : (∏ j : Fin m, wordFourier (b j) (x j)) =
        ∏ j : Fin m, wordFourier (x j) (b j) :=
      Finset.prod_congr rfl (fun j _ => wordFourier_symmetric _ _)
    rw [hs]
    change ((∏ k : Fin i, wordFourier (y k) (a k)) * unitSubgroupIndicator C (Sum.elim a b)) *
        (∏ j : Fin m, wordFourier (x j) (b j)) =
      ((∏ k : Fin i, wordFourier (y k) (a k)) *
        (∏ j : Fin m, wordFourier (x j) (b j))) * unitSubgroupIndicator C (Sum.elim a b)
    ring
  · unfold unitMatrix
    exact unitIndicator_instances (dual C) _ _ (Sum.elim y x)

theorem unit_dual_transport {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) :
    kernelCompose (F i) (unitMatrix C) = kernelCompose (unitMatrix (dual C)) (F m) := by
  rw [← unit_dual_conjugate C, compose_assoc, F_comp_self, compose_identity_right]

/-- Paper Lemma `lem:aesasm-dual`, as an exact rectangular kernel identity. -/
theorem raw_dual_transport {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) (d : ℕ)
    (hd : d ≤ i + m) (hC : IsMDS C d) :
    kernelCompose (F i) (K C d) = kernelCompose (K (dual C) (i + m - d)) (F m) := by
  have hD : IsMDS (dual C) (i + m - d) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      annihilator_isMDS AESConcrete.WordFourierCore.wordPairing C d (by simpa using hd) hC
  rw [K_eq_unit C d hd hC, K_eq_unit (dual C) (i + m - d) (by omega) hD]
  funext y x
  have h := congrFun (congrFun (unit_dual_transport C) y) x
  simp only [kernelCompose] at h ⊢
  calc
    _ = Real.rpow q (((i : ℝ) + (m : ℝ) - 4) / 2) *
        (∑ z, F i y z * unitMatrix C z x) := by rw [Finset.mul_sum]; congr 1; funext z; ring
    _ = _ := by rw [h, Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring

/-- Fourier commutes with the actual global word residual projection. -/
theorem word_residual_fourier_commutes :
    kernelCompose wordFourier (residualProjection (0 : Word)) =
      kernelCompose (residualProjection (0 : Word)) wordFourier := by
  apply kernel_action_ext
  intro f
  have ha := congrArg (fun T => action T f) word_activity_fourier_commutes
  simp only [kernelCompose_action] at ha
  simp only [kernelCompose_action, residualProjection, kernel_action_sub, action_sub,
    identityKernel_action]
  rw [ha]

theorem residual_fourier_commutes (n : ℕ) :
    kernelCompose (F n) (P n) = kernelCompose (P n) (F n) := by
  simp only [F, P, coordinateKernel_compose, word_residual_fourier_commutes]

theorem residual_zero_column (y : Word) : residualProjection (0 : Word) y 0 = 0 := by
  have h := degreePiece_symmetric (0 : Word) true y 0
  simpa only [degreePiece, if_true, residualProjection_zero_row] using h

theorem residual_row_sum (y : Word) : (∑ x : Word, residualProjection (0 : Word) y x) = 0 := by
  have h := congrFun (residualProjection_action (0 : Word) (fun _ => (1 : ℝ))) y
  have hc : (Fintype.card Word : ℝ) = 4294967296 := by rw [word_card]; norm_num
  have hm : nonzeroMean (0 : Word) (fun _ => (1 : ℝ)) = 1 := by
    unfold nonzeroMean
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    change ((Fintype.card Word : ℝ) - 1) / ((Fintype.card Word : ℝ) - 1) = 1
    rw [hc]
    norm_num
  simpa [action, wordResidual, wordAverage, hm] using h

theorem residual_tensor_zero {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (y : I → Word) :
    action (coordinateKernel (fun _ : I => residualProjection (0 : Word)))
      (fun x => if x = 0 then 1 else 0) y = 0 := by
  simp only [action, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  obtain ⟨i⟩ := ‹Nonempty I›
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact residual_zero_column (y i)

theorem residual_tensor_constant {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (y : I → Word) :
    action (coordinateKernel (fun _ : I => residualProjection (0 : Word)))
      (fun _ => (1 : ℝ)) y = 0 := by
  simp only [action, mul_one, coordinateKernel]
  rw [← Fintype.prod_sum]
  obtain ⟨i⟩ := ‹Nonempty I›
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact residual_row_sum (y i)

/-- Too many zero constraints leave only the zero marked point, which the
positive residual tensor removes. -/
theorem marked_zero_projected (M U : Finset PaperWordGraphCode.Position)
    (hM : M.Nonempty) (hZ : 4 ≤ (zeroPositions M U).card) (y : M → Word) :
    action (coordinateKernel (fun _ : M => residualProjection (0 : Word)))
      (fun z => if z ∈ markedCode M U then 1 else 0) y = 0 := by
  letI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  rw [markedCode_zero_branch M U hZ]
  simpa only [AddSubgroup.mem_bot] using residual_tensor_zero y

/-- A saturated marked image is full; the same positive residual tensor
removes its constant raw indicator. -/
theorem marked_full_projected (M U : Finset PaperWordGraphCode.Position)
    (hM : M.Nonempty) (hfull : (zeroPositions M U).card + M.card ≤ 4)
    (y : M → Word) :
    action (coordinateKernel (fun _ : M => residualProjection (0 : Word)))
      (fun z => if z ∈ markedCode M U then 1 else 0) y = 0 := by
  letI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  rw [markedCode_full_branch M U hfull]
  simpa using residual_tensor_constant y

theorem physical_zero_projected (M U : Finset PaperWordGraphCode.Position)
    (hM : M.Nonempty) (hZ : 4 ≤ (zeroPositions M U).card) (y : M → Word) :
    action (coordinateKernel (fun _ : M => residualProjection (0 : Word)))
      (graphContraction M U) y = 0 := by
  letI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  simp_rw [action, graphContraction_zero_branch M U hZ]
  calc
    _ = WordActivityFrame.xi Word ^ U.card *
        action (coordinateKernel (fun _ : M => residualProjection (0 : Word)))
          (fun z => if z = 0 then 1 else 0) y := by
      simp only [action, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = 0 := by rw [residual_tensor_zero, mul_zero]

theorem physical_full_projected (M U : Finset PaperWordGraphCode.Position)
    (hM : M.Nonempty) (hfull : (zeroPositions M U).card + M.card ≤ 4)
    (y : M → Word) :
    action (coordinateKernel (fun _ : M => residualProjection (0 : Word)))
      (graphContraction M U) y = 0 := by
  letI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  simp_rw [action, graphContraction_full_branch M U hfull]
  calc
    _ = (WordActivityFrame.xi Word ^ U.card *
        (Fintype.card Word : ℝ) ^ (4 - ((zeroPositions M U).card + M.card))) *
        action (coordinateKernel (fun _ : M => residualProjection (0 : Word)))
          (fun _ => 1) y := by
      simp only [action, mul_one, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = 0 := by rw [residual_tensor_constant, mul_zero]

def bitF (n : ℕ) (e : Bool) := if e then F n else identityKernel
def chosenK {i m : ℕ} (C : AddSubgroup ((Fin i ⊕ Fin m) → Word))
    (d : ℕ) (e : Bool) := if e then K (dual C) (i + m - d) else K C d

/-- The outside residual is transported to the permitted simultaneous
Fourier orientation, with the remaining outside factor an isometry. -/
theorem outside_variant_transport (n : ℕ) (adjoint e : Bool) :
    kernelCompose (coordinateKernel (fun _ : Fin n =>
      AESConcrete.WordFourierVariants.baseResidual adjoint)) (bitF n e) =
      kernelCompose (bitF n e) (coordinateKernel (fun _ : Fin n =>
        AESConcrete.WordFourierVariants.variant adjoint e)) := by
  cases e
  · simp only [bitF, AESConcrete.WordFourierVariants.variant, Bool.false_eq_true,
      if_false, compose_identity_left, compose_identity_right]
  · simp only [bitF, F, AESConcrete.WordFourierVariants.variant, if_true,
      coordinateKernel_compose, word_right_fourier]

theorem bitF_symmetric (n : ℕ) (e : Bool) : transpose (bitF n e) = bitF n e := by
  cases e
  · funext x y; simp [transpose, bitF, identityKernel, eq_comm]
  · exact F_symmetric n

theorem bitF_energy (n : ℕ) (e : Bool) (f : (Fin n → Word) → ℝ) :
    (∑ y, action (bitF n e) f y ^ 2) = ∑ x, f x ^ 2 := by
  cases e
  · simp [bitF, identityKernel_action]
  · exact F_energy n f

theorem chosen_transport {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) (d : ℕ)
    (hd : d ≤ i + m) (hC : IsMDS C d) (e : Bool) :
    kernelCompose (bitF i e) (K C d) = kernelCompose (chosenK C d e) (bitF m e) := by
  cases e
  · simp only [bitF, chosenK, Bool.false_eq_true, if_false,
      compose_identity_left, compose_identity_right]
  · exact raw_dual_transport C d hd hC

theorem chosen_transport_transpose {i m : ℕ}
    (C : AddSubgroup ((Fin i ⊕ Fin m) → Word)) (d : ℕ)
    (hd : d ≤ i + m) (hC : IsMDS C d) (e : Bool) :
    kernelCompose (transpose (K C d)) (bitF i e) =
      kernelCompose (bitF m e) (transpose (chosenK C d e)) := by
  have h := congrArg transpose (chosen_transport C d hd hC e)
  simpa only [compose_transpose, bitF_symmetric] using h

/-- Each graph chooses its representation independently. The two choices
produce exactly the middle map `F^eL R F^eR`; all outside factors are
Fourier isometries by `bitF_energy`. -/
theorem two_graph_duality {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → Word)) (s t : ℕ)
    (hs : s ≤ i + m) (ht : t ≤ j + m) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (R : (Fin m → Word) → (Fin m → Word) → ℝ) (eL eR : Bool) :
    kernelCompose (kernelCompose (bitF i eL)
      (kernelCompose (K CL s) (kernelCompose R (transpose (K CR t))))) (bitF j eR) =
      kernelCompose (chosenK CL s eL)
        (kernelCompose (kernelCompose (kernelCompose (bitF m eL) R) (bitF m eR))
          (transpose (chosenK CR t eR))) := by
  calc
    _ = kernelCompose (kernelCompose (bitF i eL) (K CL s))
        (kernelCompose R (kernelCompose (transpose (K CR t)) (bitF j eR))) := by
      simp only [compose_assoc]
    _ = kernelCompose (kernelCompose (chosenK CL s eL) (bitF m eL))
        (kernelCompose R (kernelCompose (bitF m eR) (transpose (chosenK CR t eR)))) := by
      rw [chosen_transport CL s hs hCL eL, chosen_transport_transpose CR t ht hCR eR]
    _ = _ := by simp only [compose_assoc]

theorem bitF_residual_commutes (n : ℕ) (e : Bool) :
    kernelCompose (bitF n e) (P n) = kernelCompose (P n) (bitF n e) := by
  cases e
  · simp only [bitF, Bool.false_eq_true, if_false,
      compose_identity_left, compose_identity_right]
  · exact residual_fourier_commutes n

theorem projected_middle_duality (m : ℕ)
    (R : (Fin m → Word) → (Fin m → Word) → ℝ) (eL eR : Bool) :
    kernelCompose (kernelCompose (bitF m eL)
      (kernelCompose (P m) (kernelCompose R (P m)))) (bitF m eR) =
      kernelCompose (P m)
        (kernelCompose (kernelCompose (kernelCompose (bitF m eL) R) (bitF m eR)) (P m)) := by
  calc
    _ = kernelCompose (kernelCompose (bitF m eL) (P m))
        (kernelCompose R (kernelCompose (P m) (bitF m eR))) := by
      simp only [compose_assoc]
    _ = kernelCompose (kernelCompose (P m) (bitF m eL))
        (kernelCompose R (kernelCompose (bitF m eR) (P m))) := by
      rw [bitF_residual_commutes m eL, ← bitF_residual_commutes m eR]
    _ = _ := by simp only [compose_assoc]

/-- The residual projections in the physical middle remain literally the
same kernels under either independent dual choice. -/
theorem two_graph_projected_duality {i j m : ℕ}
    (CL : AddSubgroup ((Fin i ⊕ Fin m) → Word))
    (CR : AddSubgroup ((Fin j ⊕ Fin m) → Word)) (s t : ℕ)
    (hs : s ≤ i + m) (ht : t ≤ j + m) (hCL : IsMDS CL s) (hCR : IsMDS CR t)
    (R : (Fin m → Word) → (Fin m → Word) → ℝ) (eL eR : Bool) :
    kernelCompose (kernelCompose (bitF i eL)
      (kernelCompose (K CL s)
        (kernelCompose (kernelCompose (P m) (kernelCompose R (P m))) (transpose (K CR t)))))
      (bitF j eR) =
      kernelCompose (chosenK CL s eL)
        (kernelCompose (kernelCompose (P m)
          (kernelCompose (kernelCompose (kernelCompose (bitF m eL) R) (bitF m eR)) (P m)))
          (transpose (chosenK CR t eR))) := by
  rw [two_graph_duality CL CR s t hs ht hCL hCR, projected_middle_duality]

/-- The two-graph identity instantiated by the literal physical word graphs.
Both MDS premises of the generic identity are discharged by the actual
shortening construction; the coordinate split is the only relabeling. -/
theorem physical_two_graph_projected_duality {i j m : ℕ}
    (ML UL MR UR : Finset PaperWordGraphCode.Position)
    (eLeft : ML ≃ Fin i ⊕ Fin m) (eRight : MR ≃ Fin j ⊕ Fin m)
    (s t : ℕ) (hLeft : (zeroPositions ML UL).card + s = 4)
    (hRight : (zeroPositions MR UR).card + t = 4)
    (hs : s ≤ ML.card) (ht : t ≤ MR.card)
    (R : (Fin m → Word) → (Fin m → Word) → ℝ) (eL eR : Bool) :
    kernelCompose (kernelCompose (bitF i eL)
      (kernelCompose (K (physicalCode ML UL eLeft) s)
        (kernelCompose (kernelCompose (P m) (kernelCompose R (P m)))
          (transpose (K (physicalCode MR UR eRight) t))))) (bitF j eR) =
      kernelCompose (chosenK (physicalCode ML UL eLeft) s eL)
        (kernelCompose (kernelCompose (P m)
          (kernelCompose (kernelCompose (kernelCompose (bitF m eL) R) (bitF m eR)) (P m)))
          (transpose (chosenK (physicalCode MR UR eRight) t eR))) := by
  have hLc : ML.card = i + m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr eLeft
  have hRc : MR.card = j + m := by
    simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr eRight
  exact two_graph_projected_duality (physicalCode ML UL eLeft) (physicalCode MR UR eRight)
    s t (by omega) (by omega) (physicalCode_isMDS ML UL eLeft s hLeft)
      (physicalCode_isMDS MR UR eRight t hRight) R eL eR

/-- The paper's fixed smaller-dimension choice is positive, fits in the
middle, and leaves only the low collision-sum branch. -/
theorem reduced_dimensions (i m d : ℕ) (hi : i ≤ 4) (hm : 3 ≤ m)
    (hd0 : 0 < d) (hdn : d < i + m) :
    let s := min d (i + m - d)
    0 < s ∧ s ≤ m ∧ 2 * s ≤ i + m ∧ s - min i s ≤ m - s := by
  dsimp
  have hl := min_le_left d (i + m - d)
  have hr := min_le_right d (i + m - d)
  have hp : 0 < min d (i + m - d) := by omega
  have htwo : 2 * min d (i + m - d) ≤ i + m := by omega
  constructor
  · exact hp
  constructor
  · omega
  constructor
  · exact htwo
  by_cases h : i ≤ min d (i + m - d)
  · have hmin : min i (min d (i + m - d)) = i := Nat.min_eq_left h
    rw [hmin]
    omega
  · have hmin : min i (min d (i + m - d)) = min d (i + m - d) := Nat.min_eq_right (by omega)
    rw [hmin, Nat.sub_self]
    exact Nat.zero_le _

end AES8.PaperWordGraphDuality
