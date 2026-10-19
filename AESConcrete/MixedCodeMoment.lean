import AESMixing.SubgroupCodeBound
import AESConcrete.ByteGramResources

/-!
# Normalized code moments with independently fixed kernels on each leg

Two physical information sets give two bijective projections of the same
source. Their dependence is retained: Cauchy--Schwarz uses separate product
square sums. Every leg has its own fixed kernel. The subgroup dual branch
uses per-leg Fourier conjugation, with exact normalized-indicator transport.
Actual byte wrappers discharge moment and diagonal premises; construction
of a marked AES code and its physical information sets remains separate.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.MixedCodeMoment
open AESMixing

section Projections
variable {C V I J : Type*} [Fintype C] [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq I]

theorem projection_square_sum (e : C ≃ (I → V)) (g : I → V → V → ℝ) :
    (∑ cd : C × C, (∏ i, g i (e cd.1 i) (e cd.2 i))^2) =
      ∏ i : I, ∑ ab : V × V, g i ab.1 ab.2^2 := by
  calc
    _ = ∑ ab : I → V × V, (∏ i, g i (ab i).1 (ab i).2)^2 :=
      Equiv.sum_comp (AESMixing.pairProjection e)
        (fun ab => (∏ i, g i (ab i).1 (ab i).2)^2)
    _ = _ := product_column_energy (fun i (ab : V × V) => g i ab.1 ab.2)

theorem projection_square_sum_le (e : C ≃ (I → V)) (g : I → V → V → ℝ)
    (s : ℝ) (hg : ∀ i, (∑ ab : V × V, g i ab.1 ab.2^2) ≤ s) :
    (∑ cd : C × C, (∏ i, g i (e cd.1 i) (e cd.2 i))^2) ≤ s^Fintype.card I := by
  rw [projection_square_sum]
  calc
    _ ≤ ∏ _ : I, s := Finset.prod_le_prod
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (fun i _ => hg i)
    _ = _ := by simp

/-- Both projections describe the same source; no joint independence is used. -/
theorem two_projection_cauchy (e f : C ≃ (I → V))
    (g h : I → V → V → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hg : ∀ i, (∑ ab : V × V, g i ab.1 ab.2^2) ≤ s)
    (hh : ∀ i, (∑ ab : V × V, h i ab.1 ab.2^2) ≤ s) :
    (∑ cd : C × C,
      |(∏ i, g i (e cd.1 i) (e cd.2 i)) * (∏ i, h i (f cd.1 i) (f cd.2 i))|) ≤
      s^Fintype.card I := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun cd : C × C => |∏ i, g i (e cd.1 i) (e cd.2 i)|)
    (fun cd : C × C => |∏ i, h i (f cd.1 i) (f cd.2 i)|)
  simp_rw [sq_abs, ← abs_mul] at hc
  have hb :
      (∑ cd : C × C, (∏ i, g i (e cd.1 i) (e cd.2 i))^2) *
        (∑ cd : C × C, (∏ i, h i (f cd.1 i) (f cd.2 i))^2) ≤
        s^Fintype.card I * s^Fintype.card I :=
    mul_le_mul (projection_square_sum_le e g s hg) (projection_square_sum_le f h s hh)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (pow_nonneg hs _)
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (pow_nonneg hs _)).mp
  simpa only [pow_two] using hc.trans hb

theorem low_dimension_moment (e f : C ≃ (I → V)) (rest : C → J → V)
    (g h : I → V → V → ℝ) (k : J → V → V → ℝ) (s delta : ℝ)
    (hs : 0 ≤ s) (hd : 0 ≤ delta)
    (hg : ∀ i, (∑ ab : V × V, g i ab.1 ab.2^2) ≤ s)
    (hh : ∀ i, (∑ ab : V × V, h i ab.1 ab.2^2) ≤ s)
    (hk : ∀ j a b, |k j a b| ≤ delta) :
    |∑ cd : C × C,
      (∏ i, g i (e cd.1 i) (e cd.2 i)) *
      (∏ i, h i (f cd.1 i) (f cd.2 i)) *
      (∏ j, k j (rest cd.1 j) (rest cd.2 j))| ≤
      s^Fintype.card I * delta^Fintype.card J := by
  have hr (cd : C × C) : |∏ j, k j (rest cd.1 j) (rest cd.2 j)| ≤ delta^Fintype.card J := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _ : J, delta := Finset.prod_le_prod
        (fun _ _ => abs_nonneg _) (fun j _ => hk j _ _)
      _ = _ := by simp
  calc
    _ ≤ ∑ cd : C × C,
        |(∏ i, g i (e cd.1 i) (e cd.2 i)) *
          (∏ i, h i (f cd.1 i) (f cd.2 i)) *
          (∏ j, k j (rest cd.1 j) (rest cd.2 j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ cd : C × C,
        |(∏ i, g i (e cd.1 i) (e cd.2 i)) *
          (∏ i, h i (f cd.1 i) (f cd.2 i))| * delta^Fintype.card J := by
      apply Finset.sum_le_sum
      intro cd _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hr cd) (abs_nonneg _)
    _ = (∑ cd : C × C,
        |(∏ i, g i (e cd.1 i) (e cd.2 i)) *
          (∏ i, h i (f cd.1 i) (f cd.2 i))|) * delta^Fintype.card J :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (two_projection_cauchy e f g h s hs hg hh)
      (pow_nonneg hd _)

end Projections

section Response
variable {C K I J V : Type*} [Fintype C] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype V]

def responseKernel (T : K → V → V → ℝ) (coord : C → K → V)
    (y : K → V) (c : C) : ℝ := ∏ k, T k (y k) (coord c k)

/-- Unit-source normalization, never a probability normalization. -/
def normalizedResponse (T : K → V → V → ℝ) (coord : C → K → V) (y : K → V) : ℝ :=
  (∑ c : C, responseKernel T coord y c) / Real.sqrt (Fintype.card C)

theorem responseKernel_gram (T : K → V → V → ℝ) (coord : C → K → V) (c d : C) :
    gram (responseKernel T coord) c d = ∏ k, gram (T k) (coord c k) (coord d k) :=
  product_gram T (coord c) (coord d)

theorem rawResponse_energy (T : K → V → V → ℝ) (coord : C → K → V) :
    (∑ y : K → V, (∑ c : C, responseKernel T coord y c)^2) =
      ∑ cd : C × C, ∏ k, gram (T k) (coord cd.1 k) (coord cd.2 k) := by
  have h := gram_quadratic (responseKernel T coord) (fun _ => 1)
  simpa only [mul_one, one_mul, responseKernel_gram, Fintype.sum_prod_type] using h

/-- Explicit physical leg split into two information sets and the remainder. -/
theorem normalizedResponse_energy_le (T : K → V → V → ℝ) (coord : C → K → V)
    (idx : CodePosition I J ≃ K) (e f : C ≃ (I → V)) (rest : C → J → V)
    (hcoord : ∀ c p, coord c (idx p) = codeCoordinates e f rest c p)
    (s delta : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ delta)
    (hmoment : ∀ k, (∑ ab : V × V, gram (T k) ab.1 ab.2^2) ≤ s)
    (hdiag : ∀ k a, gram (T k) a a ≤ delta) :
    (∑ y : K → V, normalizedResponse T coord y^2) ≤
      (s / (Fintype.card V : ℝ))^Fintype.card I * delta^Fintype.card J := by
  have hp (c d : C) : (∏ k : K, gram (T k) (coord c k) (coord d k)) =
      (∏ i : I, gram (T (idx (Sum.inl i))) (e c i) (e d i)) *
      (∏ i : I, gram (T (idx (Sum.inr (Sum.inl i)))) (f c i) (f d i)) *
      (∏ j : J, gram (T (idx (Sum.inr (Sum.inr j)))) (rest c j) (rest d j)) := by
    rw [← Equiv.prod_comp idx (fun k => gram (T k) (coord c k) (coord d k))]
    simp only [hcoord, Fintype.prod_sum_type, codeCoordinates, Sum.elim_inl, Sum.elim_inr]
    ring
  have hraw := low_dimension_moment e f rest
    (fun i => gram (T (idx (Sum.inl i))))
    (fun i => gram (T (idx (Sum.inr (Sum.inl i)))))
    (fun j => gram (T (idx (Sum.inr (Sum.inr j))))) s delta hs hd
    (fun i => hmoment _) (fun i => hmoment _)
    (fun j => gram_entry_bound _ delta hd (hdiag _))
  have hb : (∑ y : K → V, (∑ c : C, responseKernel T coord y c)^2) ≤
      s^Fintype.card I * delta^Fintype.card J := by
    rw [rawResponse_energy]
    simp_rw [hp]
    exact (le_abs_self _).trans hraw
  have hcard : (Fintype.card C : ℝ) = (Fintype.card V : ℝ)^Fintype.card I := by
    rw [Fintype.card_congr e, Fintype.card_fun, Nat.cast_pow]
  unfold normalizedResponse
  simp_rw [div_pow]
  rw [← Finset.sum_div, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ (s^Fintype.card I * delta^Fintype.card J) / Fintype.card C :=
      div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
    _ = _ := by rw [hcard]; ring

/-- Bijections are required of the actual two physical coordinate restrictions. -/
theorem normalizedResponse_energy_le_of_bijective
    (T : K → V → V → ℝ) (coord : C → K → V) (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : I => coord c (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : C => fun i : I => coord c (idx (Sum.inr (Sum.inl i)))))
    (s delta : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ delta)
    (hmoment : ∀ k, (∑ ab : V × V, gram (T k) ab.1 ab.2^2) ≤ s)
    (hdiag : ∀ k a, gram (T k) a a ≤ delta) :
    (∑ y : K → V, normalizedResponse T coord y^2) ≤
      (s / (Fintype.card V : ℝ))^Fintype.card I * delta^Fintype.card J := by
  let e := Equiv.ofBijective (fun c : C => fun i : I => coord c (idx (Sum.inl i))) he
  let f := Equiv.ofBijective (fun c : C => fun i : I => coord c (idx (Sum.inr (Sum.inl i)))) hf
  let rest := fun c : C => fun j : J => coord c (idx (Sum.inr (Sum.inr j)))
  apply normalizedResponse_energy_le T coord idx e f rest _ s delta hs hd hmoment hdiag
  intro c p
  rcases p with i | (i | j) <;> rfl

end Response

section Subgroups
variable {K I J V : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [AddCommGroup V] [Fintype V]
attribute [local instance] Classical.propDecidable

theorem subgroup_response (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) [Fintype C] :
    action (coordinateKernel T) (unitSubgroupIndicator C) =
      normalizedResponse T (fun c : C => c.val) := by
  funext y
  exact subgroup_action_formula (coordinateKernel T) C y

theorem subgroup_energy_le (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) [Fintype C]
    (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inr (Sum.inl i)))))
    (s delta : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ delta)
    (hmoment : ∀ k, (∑ ab : V × V, gram (T k) ab.1 ab.2^2) ≤ s)
    (hdiag : ∀ k a, gram (T k) a a ≤ delta) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y^2) ≤
      (s / (Fintype.card V : ℝ))^Fintype.card I * delta^Fintype.card J := by
  rw [subgroup_response]
  exact normalizedResponse_energy_le_of_bijective T (fun c : C => c.val) idx he hf
    s delta hs hd hmoment hdiag

/-- Independently fixed kernels survive product Fourier conjugation leg by leg. -/
theorem coordinate_fourierConjugate (B : CharacterPairing V) (T : K → V → V → ℝ) :
    fourierConjugate (B.product K) (coordinateKernel T) =
      coordinateKernel (fun k => fourierConjugate B (T k)) := by
  unfold fourierConjugate
  rw [productPairing_fourier, coordinateKernel_compose, coordinateKernel_compose]

theorem code_dual_energy (B : CharacterPairing V) (hchar : ∀ x : V, x+x = 0)
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) [Fintype C] :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y^2) =
      ∑ y : K → V, action (coordinateKernel (fun k => fourierConjugate B (T k)))
        (unitSubgroupIndicator ((B.product K).annihilator C)) y^2 := by
  have hp : ∀ x : K → V, x+x = 0 := by
    intro x
    funext k
    exact hchar (x k)
  have h := fourierConjugate_energy (B.product K) hp (coordinateKernel T) (unitSubgroupIndicator C)
  rw [pairingFourier_subgroup, coordinate_fourierConjugate] at h
  exact h.symm

theorem subgroup_energy_dual_le (B : CharacterPairing V) (hchar : ∀ x : V, x+x = 0)
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) [Fintype C]
    (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : (B.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : (B.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inr (Sum.inl i)))))
    (s delta : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ delta)
    (hmoment : ∀ k, (∑ ab : V × V, gram (T k) ab.1 ab.2^2) ≤ s)
    (hdiag : ∀ k a, gram (fourierConjugate B (T k)) a a ≤ delta) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y^2) ≤
      (s / (Fintype.card V : ℝ))^Fintype.card I * delta^Fintype.card J := by
  rw [code_dual_energy B hchar]
  apply subgroup_energy_le _ _ idx he hf s delta hs hd _ hdiag
  intro k
  rw [fourierConjugate_gram_moment B hchar]
  exact hmoment k

end Subgroups

section ActualByte
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteGramCore (Byte)
open AESConcrete.ByteGramFourier
open AESConcrete.ByteGramDiagonal (residualGram actual_gram_diagonal)

def byteMoment : ℝ := 571447 / 2^27
def byteDelta : ℝ := 8383 / 2088960

def fourierOrientation : Orientation → Orientation
  | .ordinary => .fourier
  | .transposed => .fourierTransposed
  | .fourier => .ordinary
  | .fourierTransposed => .transposed

def adjointOrientation : Orientation → Orientation
  | .ordinary => .transposed
  | .transposed => .ordinary
  | .fourier => .fourierTransposed
  | .fourierTransposed => .fourier

theorem actual_channel_adjoint (o : Orientation) (y x : Byte) :
    channel (adjointOrientation o) y x = channel o x y := by
  cases o <;> rfl

/-- An input adjoint is another actual permitted residual orientation. -/
theorem actual_residual_adjoint (o : Orientation) :
    (fun y x => residualMatrix (channel o) 0 x y) =
      residualMatrix (channel (adjointOrientation o)) 0 := by
  funext y x
  simp only [residualMatrix, actual_channel_adjoint]
  rw [activityMatrix_symmetric (0 : Byte) x y]

theorem byteConjugate_twice (T : Byte → Byte → ℝ) : byteConjugate (byteConjugate T) = T := by
  apply kernel_action_ext
  intro f
  simp only [byteConjugate, kernelCompose_action, byteFourier_twice]

theorem actual_channel_conjugate (o : Orientation) :
    byteConjugate (channel o) = channel (fourierOrientation o) := by
  cases o
  · exact squared_walsh_conjugate.symm
  · change byteConjugate (fun y x => aesByteChannel x y) = fun y x => aesSquaredWalshChannel x y
    rw [byteConjugate_transpose, ← squared_walsh_conjugate]
  · change byteConjugate aesSquaredWalshChannel = aesByteChannel
    rw [squared_walsh_conjugate, byteConjugate_twice]
  · change byteConjugate (fun y x => aesSquaredWalshChannel x y) = fun y x => aesByteChannel x y
    rw [byteConjugate_transpose, squared_walsh_conjugate, byteConjugate_twice]

theorem actual_residual_conjugate (o : Orientation) :
    fourierConjugate bytePairing (residualMatrix (channel o) 0) =
      residualMatrix (channel (fourierOrientation o)) 0 := by
  rw [← byteConjugate_pairing]
  change byteConjugate (channel o - activityMatrix 0) =
    channel (fourierOrientation o) - activityMatrix 0
  rw [byteConjugate_sub, actual_channel_conjugate, activity_fourier_fixed]

theorem actual_residual_moment (o : Orientation) :
    (∑ ab : Byte × Byte, gram (residualMatrix (channel o) 0) ab.1 ab.2^2) = byteMoment := by
  change (∑ ab : Byte × Byte, residualGram (channel o) ab.1 ab.2^2) = byteMoment
  rw [Fintype.sum_prod_type]
  exact ByteGramResources.actual_gram_square_moment o

theorem actual_residual_diagonal_le (o : Orientation) (a : Byte) :
    gram (residualMatrix (channel o) 0) a a ≤ byteDelta := by
  change residualGram (channel o) a a ≤ byteDelta
  rw [actual_gram_diagonal]
  split_ifs <;> norm_num [byteDelta]

variable {K I J : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- Actual byte resources; only the two physical information-set bijections remain. -/
theorem actual_normalizedResponse_energy_le {C : Type*} [Fintype C]
    (o : K → Orientation) (coord : C → K → Byte) (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : I => coord c (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : C => fun i : I => coord c (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → Byte, normalizedResponse (fun k => residualMatrix (channel (o k)) 0) coord y^2) ≤
      (byteMoment / 256)^Fintype.card I * byteDelta^Fintype.card J := by
  have h := normalizedResponse_energy_le_of_bijective
    (fun k => residualMatrix (channel (o k)) 0) coord idx he hf byteMoment byteDelta
    (by norm_num [byteMoment]) (by norm_num [byteDelta])
    (fun k => le_of_eq (actual_residual_moment (o k))) (fun k => actual_residual_diagonal_le (o k))
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using h

theorem actual_subgroup_energy_le (o : K → Orientation)
    (C : AddSubgroup (K → Byte)) [Fintype C] (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → Byte, action (coordinateKernel (fun k => residualMatrix (channel (o k)) 0))
      (unitSubgroupIndicator C) y^2) ≤
      (byteMoment / 256)^Fintype.card I * byteDelta^Fintype.card J := by
  rw [subgroup_response]
  exact actual_normalizedResponse_energy_le o (fun c : C => c.val) idx he hf

theorem actual_subgroup_energy_dual_le (o : K → Orientation)
    (C : AddSubgroup (K → Byte)) [Fintype C] (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : (bytePairing.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : (bytePairing.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → Byte, action (coordinateKernel (fun k => residualMatrix (channel (o k)) 0))
      (unitSubgroupIndicator C) y^2) ≤
      (byteMoment / 256)^Fintype.card I * byteDelta^Fintype.card J := by
  have h := subgroup_energy_dual_le bytePairing BinaryWord.add_self
    (fun k => residualMatrix (channel (o k)) 0) C idx he hf byteMoment byteDelta
    (by norm_num [byteMoment]) (by norm_num [byteDelta])
    (fun k => le_of_eq (actual_residual_moment (o k)))
    (fun k a => by rw [actual_residual_conjugate]; exact actual_residual_diagonal_le _ a)
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using h

/-- The min(d,ell-d) form: the chosen two physical information sets must
be supplied on the primal code or on its actual trace-character annihilator. -/
theorem actual_subgroup_energy_min (o : K → Orientation)
    (C : AddSubgroup (K → Byte)) [Fintype C] (idx : CodePosition I J ≃ K)
    (d ell : ℕ) (hlen : Fintype.card K = ell)
    (hI : Fintype.card I = min d (ell-d))
    (hinfo :
      (Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inl i))) ∧
        Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inr (Sum.inl i))))) ∨
      (Function.Bijective (fun c : (bytePairing.product K).annihilator C =>
          fun i : I => c.val (idx (Sum.inl i))) ∧
        Function.Bijective (fun c : (bytePairing.product K).annihilator C =>
          fun i : I => c.val (idx (Sum.inr (Sum.inl i)))))) :
    (∑ y : K → Byte, action (coordinateKernel (fun k => residualMatrix (channel (o k)) 0))
      (unitSubgroupIndicator C) y^2) ≤
      (byteMoment / 256)^min d (ell-d) * byteDelta^(ell-2*min d (ell-d)) := by
  have hc := Fintype.card_congr idx
  simp only [CodePosition, Fintype.card_sum] at hc
  have hJ : Fintype.card J = ell-2*min d (ell-d) := by omega
  have hb :
      (∑ y : K → Byte, action (coordinateKernel (fun k => residualMatrix (channel (o k)) 0))
        (unitSubgroupIndicator C) y^2) ≤
        (byteMoment / 256)^Fintype.card I * byteDelta^Fintype.card J := by
    rcases hinfo with ⟨he,hf⟩ | ⟨he,hf⟩
    · exact actual_subgroup_energy_le o C idx he hf
    · exact actual_subgroup_energy_dual_le o C idx he hf
  simpa only [hI, hJ] using hb

end ActualByte
end AESConcrete.MixedCodeMoment
