import AES8.Math.PaperThinHolderAffine

/-!
# Information-pair estimates for a physical affine plane

This is the Cauchy--Schwarz ingredient of frozen `lem:line-plane` in
`paper-merged` commit `f902bb94fc826983181b1712d7b57cf9cbe22f4d`.
The plane pair bijections are derived from the MDS property in physical
coordinates. The raw row and total bounds are proved from the local second
moments, without assuming a kernel-sum cap. Fourth moments and normalized
fiber operators belong to the endpoint module. Constructive checking only.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperThinPlane

open PaperMDSGram PaperMDSFiber PaperThinHolder

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The two physical coordinates of an affine two-dimensional shortened
fiber are an information pair. They must be distinct and unfixed. -/
theorem affine_coordinatePair_bijective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 2 = k) (i j : K)
    (hi : i ∉ fixed) (hj : j ∉ fixed) (hij : i ≠ j) :
    Function.Bijective (fun x : AffineFiber C offset fixed target =>
      (x.val i, x.val j)) := by
  have hd : Disjoint fixed ({i, j} : Finset K) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hi ha
    · exact hj (Finset.mem_singleton.mp hb ▸ ha)
  have hs : fixed.card + ({i, j} : Finset K).card = k := by
    simpa only [Finset.card_pair hij] using hdim
  have hp := affine_projection_bijective C k hk hC offset fixed {i, j} hd hs target
  constructor
  · intro x y hxy
    apply hp.injective
    funext a
    rcases Finset.mem_insert.mp a.property with hai | haj
    · simpa only [hai] using congrArg Prod.fst hxy
    · have haj' := Finset.mem_singleton.mp haj
      simpa only [haj'] using congrArg Prod.snd hxy
  · intro ab
    obtain ⟨x, hx⟩ := hp.surjective
      (fun a => if a.val = i then ab.1 else ab.2)
    refine ⟨x, Prod.ext ?_ ?_⟩
    · simpa using congrFun hx ⟨i, Finset.mem_insert_self i {j}⟩
    · simpa [Ne.symm hij] using
        congrFun hx ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩

def affinePlanePairEquiv (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 2 = k) (i j : K)
    (hi : i ∉ fixed) (hj : j ∉ fixed) (hij : i ≠ j) :
    AffineFiber C offset fixed target ≃ (V × V) :=
  Equiv.ofBijective _
    (affine_coordinatePair_bijective C k hk hC offset fixed target hdim i j hi hj hij)

/-- The information-pair sum factors exactly, including for arbitrary affine
translates and prescribed labels. In particular there is no alphabet factor. -/
theorem affine_plane_pair_sum (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 2 = k) (i j : K)
    (hi : i ∉ fixed) (hj : j ∉ fixed) (hij : i ≠ j) (f g : V → ℝ) :
    (∑ x : AffineFiber C offset fixed target, f (x.val i) * g (x.val j)) =
      (∑ a, f a) * ∑ b, g b := by
  have he := (affinePlanePairEquiv C k hk hC offset fixed target hdim i j
    hi hj hij).sum_comp (fun ab : V × V => f ab.1 * g ab.2)
  change (∑ x : AffineFiber C offset fixed target, f (x.val i) * g (x.val j)) =
    ∑ ab : V × V, f ab.1 * g ab.2 at he
  rw [he, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

section Analytic

variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]

/-- A nonnegative row energy, defined from the actual local entries. -/
def rowEnergy (f : A → A → ℝ) (a : A) : ℝ := ∑ b, f a b ^ 2

theorem rowEnergy_nonneg (f : A → A → ℝ) (a : A) : 0 ≤ rowEnergy f a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Exact square-energy factorization along one information pair. -/
theorem pair_square_sum (e : Y ≃ (A × A)) (f g : A → ℝ) :
    (∑ y, (f (e y).1 * g (e y).2) ^ 2) =
      (∑ a, f a ^ 2) * ∑ b, g b ^ 2 := by
  rw [e.sum_comp (fun ab : A × A => (f ab.1 * g ab.2) ^ 2),
    Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_pow, Finset.mul_sum]

/-- Cauchy--Schwarz on the plane's two information pairs gives the raw
four-coordinate row cap `H²`. The equivalences select physical projections
in the affine theorem below. -/
theorem plane_row (e d : Y ≃ (A × A)) (f : Fin 4 → A → ℝ)
    (H : ℝ) (hH : 0 ≤ H) (hrow : ∀ j, (∑ a, f j a ^ 2) ≤ H) :
    (∑ y, f 0 (e y).1 * f 1 (e y).2 * f 2 (d y).1 * f 3 (d y).2) ≤ H ^ 2 := by
  have hpair (a b : Fin 4) (q : Y ≃ (A × A)) :
      (∑ y, (f a (q y).1 * f b (q y).2) ^ 2) ≤ H ^ 2 := by
    rw [pair_square_sum]
    exact (mul_le_mul (hrow a) (hrow b)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hH).trans_eq (pow_two H).symm
  have hb := common_second (fun y => f 0 (e y).1 * f 1 (e y).2)
    (fun y => f 2 (d y).1 * f 3 (d y).2) (H ^ 2) (sq_nonneg H)
    (hpair 0 1 e) (hpair 2 3 d)
  simpa only [← mul_assoc] using hb

/-- One line coordinate sums one row energy and the other factor is capped
by `H`. This is the grouped-pair square energy needed for the total bound. -/
theorem line_plane_pair_energy (e : X ≃ A) (p : X → A)
    (q : Y ≃ (A × A)) (f g : A → A → ℝ)
    (H T : ℝ) (hH : 0 ≤ H)
    (hg : ∀ a, rowEnergy g a ≤ H)
    (hf : (∑ a, rowEnergy f a) ≤ T) :
    (∑ x, ∑ y, (f (e x) (q y).1 * g (p x) (q y).2) ^ 2) ≤ H * T := by
  have he : (∑ x, rowEnergy f (e x)) = ∑ a, rowEnergy f a := e.sum_comp _
  calc
    (∑ x, ∑ y, (f (e x) (q y).1 * g (p x) (q y).2) ^ 2) =
        ∑ x, rowEnergy f (e x) * rowEnergy g (p x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact pair_square_sum q (f (e x)) (g (p x))
    _ ≤ ∑ x, rowEnergy f (e x) * H := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hg (p x)) (rowEnergy_nonneg f (e x))
    _ = H * ∑ a, rowEnergy f a := by rw [← Finset.sum_mul, he, mul_comm]
    _ ≤ H * T := mul_le_mul_of_nonneg_left hf hH

/-- The total raw kernel sum on a line and a plane is at most `H*T`.
This proof applies Cauchy--Schwarz to the whole product type, using the
line coordinate bijections and both plane information pairs exactly. -/
theorem line_plane_total (e : Fin 4 → X ≃ A) (q d : Y ≃ (A × A))
    (f : Fin 4 → A → A → ℝ) (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hrow : ∀ j a, rowEnergy (f j) a ≤ H)
    (htotal : ∀ j, (∑ a, rowEnergy (f j) a) ≤ T) :
    (∑ x, ∑ y,
      f 0 (e 0 x) (q y).1 * f 1 (e 1 x) (q y).2 *
      f 2 (e 2 x) (d y).1 * f 3 (e 3 x) (d y).2) ≤ H * T := by
  have h01 := line_plane_pair_energy (e 0) (fun x => e 1 x) q
    (f 0) (f 1) H T hH (hrow 1) (htotal 0)
  have h23 := line_plane_pair_energy (e 2) (fun x => e 3 x) d
    (f 2) (f 3) H T hH (hrow 3) (htotal 2)
  have hb := common_second
    (fun z : X × Y => f 0 (e 0 z.1) (q z.2).1 * f 1 (e 1 z.1) (q z.2).2)
    (fun z : X × Y => f 2 (e 2 z.1) (d z.2).1 * f 3 (e 3 z.1) (d z.2).2)
    (H * T) (mul_nonneg hH hT)
    (by simpa only [Fintype.sum_prod_type] using h01)
    (by simpa only [Fintype.sum_prod_type] using h23)
  simpa only [Fintype.sum_prod_type, ← mul_assoc] using hb

end Analytic

/-- Row bound on the actual affine plane, in the four physical coordinates.
Only the two disjoint coordinate pairs need distinctness. -/
theorem affine_plane_row (D : AddSubgroup (K → V)) (l : ℕ)
    (hl : l ≤ Fintype.card K) (hD : IsMDS D l)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 2 = l) (i : Fin 4 → K)
    (hi : ∀ j, i j ∉ fixed) (h01 : i 0 ≠ i 1) (h23 : i 2 ≠ i 3)
    (f : Fin 4 → V → V → ℝ) (u : K → V)
    (H : ℝ) (hH : 0 ≤ H)
    (hrow : ∀ j, rowEnergy (f j) (u (i j)) ≤ H) :
    (∑ v : AffineFiber D offset fixed target,
      f 0 (u (i 0)) (v.val (i 0)) * f 1 (u (i 1)) (v.val (i 1)) *
      f 2 (u (i 2)) (v.val (i 2)) * f 3 (u (i 3)) (v.val (i 3))) ≤ H ^ 2 := by
  exact plane_row
    (affinePlanePairEquiv D l hl hD offset fixed target hdim (i 0) (i 1)
      (hi 0) (hi 1) h01)
    (affinePlanePairEquiv D l hl hD offset fixed target hdim (i 2) (i 3)
      (hi 2) (hi 3) h23)
    (fun j a => f j (u (i j)) a) H hH hrow

/-- Total bound on two actual affine shortened fibers of dimensions one
and two. All line coordinates and plane information pairs come from MDS. -/
theorem affine_line_plane_total (C D : AddSubgroup (K → V)) (k l : ℕ)
    (hk : k ≤ Fintype.card K) (hl : l ≤ Fintype.card K)
    (hC : IsMDS C k) (hD : IsMDS D l)
    (offC offD : K → V) (s t : Finset K) (u v : K → V)
    (hs : s.card + 1 = k) (ht : t.card + 2 = l)
    (i : Fin 4 → K) (his : ∀ j, i j ∉ s) (hit : ∀ j, i j ∉ t)
    (h01 : i 0 ≠ i 1) (h23 : i 2 ≠ i 3)
    (f : Fin 4 → V → V → ℝ) (H T : ℝ) (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hrow : ∀ j a, rowEnergy (f j) a ≤ H)
    (htotal : ∀ j, (∑ a, rowEnergy (f j) a) ≤ T) :
    (∑ x : AffineFiber C offC s u, ∑ y : AffineFiber D offD t v,
      f 0 (x.val (i 0)) (y.val (i 0)) * f 1 (x.val (i 1)) (y.val (i 1)) *
      f 2 (x.val (i 2)) (y.val (i 2)) * f 3 (x.val (i 3)) (y.val (i 3))) ≤ H * T := by
  exact line_plane_total
    (fun j => affineCoordinateEquiv C k hk hC offC s u hs (i j) (his j))
    (affinePlanePairEquiv D l hl hD offD t v ht (i 0) (i 1)
      (hit 0) (hit 1) h01)
    (affinePlanePairEquiv D l hl hD offD t v ht (i 2) (i 3)
      (hit 2) (hit 3) h23)
    f H T hH hT hrow htotal

end AES8.PaperThinPlane
