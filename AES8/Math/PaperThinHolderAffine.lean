import AES8.Math.PaperThinHolder
import AES8.Math.PaperMDSFiberAffine

/-!
# Physical affine-fiber transport for the thin-code moments

Information projections are derived from MDS, including on prescribed fibers
of arbitrary affine translates. Singleton projections give line coordinates;
the product of two such equivalences gives the coordinate-pair map on two
independent lines. These transport raw moments, with no alphabet multiplier.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperThinHolder
open PaperMDSGram PaperMDSFiber
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Exact physical information-set bijection on an affine prescribed fiber. -/
theorem affine_projection_bijective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (offset : K → V) (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (heq : fixed.card + observed.card = k) (target : K → V) :
    Function.Bijective (fun x : AffineFiber C offset fixed target =>
      fun i : observed => x.val i.val) := by
  let e := affineFiberEquiv C offset fixed target
  have hr := projection_bijective C k hk hMDS fixed observed hd heq (target - offset)
  constructor
  · intro x y hxy
    apply e.injective
    apply hr.injective
    funext i
    change x.val i.val - offset i.val = y.val i.val - offset i.val
    exact congrArg (fun v : V => v - offset i.val) (congrFun hxy i)
  · intro u
    obtain ⟨c, hc⟩ := hr.surjective (fun i => u i - offset i.val)
    refine ⟨e.symm c, ?_⟩
    funext i
    change c.val.val i.val + offset i.val = u i
    exact eq_sub_iff_add_eq.mp (congrFun hc i)

/-- On a one-dimensional shortened fiber, each remaining coordinate is a
bijection. The coordinate being outside `fixed` is essential. -/
theorem affine_coordinate_bijective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 1 = k) (i : K) (hi : i ∉ fixed) :
    Function.Bijective (fun x : AffineFiber C offset fixed target => x.val i) := by
  have hd : Disjoint fixed ({i} : Finset K) := by
    simpa only [Finset.disjoint_singleton_right] using hi
  have hr := affine_projection_bijective C k hk hMDS offset fixed {i} hd
    (by simpa using hdim) target
  constructor
  · intro x y hxy
    apply hr.injective
    funext j
    have hj : j.val = i := Finset.mem_singleton.mp j.property
    simpa only [hj] using hxy
  · intro v
    obtain ⟨x, hx⟩ := hr.surjective (fun _ => v)
    exact ⟨x, congrFun hx ⟨i, Finset.mem_singleton_self i⟩⟩

def affineCoordinateEquiv (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 1 = k) (i : K) (hi : i ∉ fixed) :
    AffineFiber C offset fixed target ≃ V :=
  Equiv.ofBijective _ (affine_coordinate_bijective C k hk hMDS offset fixed target hdim i hi)

/-- Rows/columns on actual affine lines have exactly the local moments. -/
theorem affine_coordinate_sum (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 1 = k) (i : K) (hi : i ∉ fixed) (f : V → ℝ) :
    (∑ x : AffineFiber C offset fixed target, f (x.val i)) = ∑ v, f v :=
  (affineCoordinateEquiv C k hk hMDS offset fixed target hdim i hi).sum_comp f

/-- The two varying parameters are independent. This is an equivalence with
V × V, not a same-line two-coordinate projection. -/
def affinePairEquiv (C D : AddSubgroup (K → V)) (k l : ℕ)
    (hk : k ≤ Fintype.card K) (hl : l ≤ Fintype.card K)
    (hC : IsMDS C k) (hD : IsMDS D l)
    (offC offD : K → V) (s t : Finset K) (u v : K → V)
    (hs : s.card + 1 = k) (ht : t.card + 1 = l)
    (i : K) (his : i ∉ s) (hit : i ∉ t) :
    (AffineFiber C offC s u × AffineFiber D offD t v) ≃ (V × V) :=
  Equiv.prodCongr (affineCoordinateEquiv C k hk hC offC s u hs i his)
    (affineCoordinateEquiv D l hl hD offD t v ht i hit)

/-- Total local moments on line × line (including a shortened plane fiber)
are transported exactly. No factor |V| or |V|² is introduced. -/
theorem affine_pair_sum (C D : AddSubgroup (K → V)) (k l : ℕ)
    (hk : k ≤ Fintype.card K) (hl : l ≤ Fintype.card K)
    (hC : IsMDS C k) (hD : IsMDS D l)
    (offC offD : K → V) (s t : Finset K) (u v : K → V)
    (hs : s.card + 1 = k) (ht : t.card + 1 = l)
    (i : K) (his : i ∉ s) (hit : i ∉ t) (f : V → V → ℝ) :
    (∑ x : AffineFiber C offC s u, ∑ y : AffineFiber D offD t v,
      f (x.val i) (y.val i)) = ∑ a, ∑ b, f a b := by
  have he := (affinePairEquiv C D k l hk hl hC hD offC offD s t u v
    hs ht i his hit).sum_comp (fun z : V × V => f z.1 z.2)
  change (∑ z : AffineFiber C offC s u × AffineFiber D offD t v,
    f (z.1.val i) (z.2.val i)) = ∑ z : V × V, f z.1 z.2 at he
  simpa only [Fintype.sum_prod_type] using he

/-- Four-coordinate total thin bound on two physical one-dimensional fibers.
This includes line × one-dimensional outside fiber of a plane. -/
theorem affine_pair_four (C D : AddSubgroup (K → V)) (k l : ℕ)
    (hk : k ≤ Fintype.card K) (hl : l ≤ Fintype.card K)
    (hC : IsMDS C k) (hD : IsMDS D l)
    (offC offD : K → V) (s t : Finset K) (u v : K → V)
    (hs : s.card + 1 = k) (ht : t.card + 1 = l)
    (i : Fin 4 → K) (his : ∀ j, i j ∉ s) (hit : ∀ j, i j ∉ t)
    (f : Fin 4 → V → V → ℝ) (H p : ℝ) (hH : 0 ≤ H)
    (h4 : ∀ j, (∑ a, ∑ b, f j a b ^ 4) ≤ p ^ 2 * H) :
    (∑ x : AffineFiber C offC s u, ∑ y : AffineFiber D offD t v,
      f 0 (x.val (i 0)) (y.val (i 0)) * f 1 (x.val (i 1)) (y.val (i 1)) *
      f 2 (x.val (i 2)) (y.val (i 2)) * f 3 (x.val (i 3)) (y.val (i 3)))
      ≤ H * p ^ 2 := by
  have hb := four_transport
    (fun j => affinePairEquiv C D k l hk hl hC hD offC offD s t u v
      hs ht (i j) (his j) (hit j))
    (fun j z => f j z.1 z.2) H p hH
    (by intro j; simpa only [Fintype.sum_prod_type] using h4 j)
  change (∑ z : AffineFiber C offC s u × AffineFiber D offD t v,
    f 0 (z.1.val (i 0)) (z.2.val (i 0)) * f 1 (z.1.val (i 1)) (z.2.val (i 1)) *
    f 2 (z.1.val (i 2)) (z.2.val (i 2)) * f 3 (z.1.val (i 3)) (z.2.val (i 3)))
      ≤ H * p ^ 2 at hb
  simpa only [Fintype.sum_prod_type] using hb

/-- Physical affine-coordinate three-factor bound: specialize the local maps
by fixing the other endpoint to obtain either a row or a column estimate. -/
theorem affine_coordinate_three (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 1 = k) (i : Fin 3 → K) (hi : ∀ j, i j ∉ fixed)
    (f : Fin 3 → V → ℝ) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p)
    (h2 : ∀ j, (∑ a, f j a ^ 2) ≤ H)
    (h4 : ∀ j, (∑ a, f j a ^ 4) ≤ p ^ 2 * H) :
    (∑ x : AffineFiber C offset fixed target, f 0 (x.val (i 0)) * f 1 (x.val (i 1)) * f 2 (x.val (i 2)))
      ≤ H * p := by
  exact three_transport
    (fun j => affineCoordinateEquiv C k hk hC offset fixed target hdim (i j) (hi j))
    f H p hH hp
    (by intro j; exact h2 j) h4

/-- Physical affine-coordinate four-factor bound: specialize the local maps
by fixing the other endpoint to obtain either a row or a column estimate. -/
theorem affine_coordinate_four (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (target : K → V)
    (hdim : fixed.card + 1 = k) (i : Fin 4 → K) (hi : ∀ j, i j ∉ fixed)
    (f : Fin 4 → V → ℝ) (H p : ℝ) (hH : 0 ≤ H)
    (h4 : ∀ j, (∑ a, f j a ^ 4) ≤ p ^ 2 * H) :
    (∑ x : AffineFiber C offset fixed target, f 0 (x.val (i 0)) * f 1 (x.val (i 1)) * f 2 (x.val (i 2)) * f 3 (x.val (i 3)))
      ≤ H * p ^ 2 := by
  exact four_transport
    (fun j => affineCoordinateEquiv C k hk hC offset fixed target hdim (i j) (hi j))
    f H p hH h4

/-- Three-coordinate total thin bound on two physical one-dimensional fibers.
This includes line × one-dimensional outside fiber of a plane. -/
theorem affine_pair_three (C D : AddSubgroup (K → V)) (k l : ℕ)
    (hk : k ≤ Fintype.card K) (hl : l ≤ Fintype.card K)
    (hC : IsMDS C k) (hD : IsMDS D l)
    (offC offD : K → V) (s t : Finset K) (u v : K → V)
    (hs : s.card + 1 = k) (ht : t.card + 1 = l)
    (i : Fin 3 → K) (his : ∀ j, i j ∉ s) (hit : ∀ j, i j ∉ t)
    (f : Fin 3 → V → V → ℝ) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p)
    (h2 : ∀ j, (∑ a, ∑ b, f j a b ^ 2) ≤ H)
    (h4 : ∀ j, (∑ a, ∑ b, f j a b ^ 4) ≤ p ^ 2 * H) :
    (∑ x : AffineFiber C offC s u, ∑ y : AffineFiber D offD t v,
      f 0 (x.val (i 0)) (y.val (i 0)) * f 1 (x.val (i 1)) (y.val (i 1)) *
      f 2 (x.val (i 2)) (y.val (i 2)))
      ≤ H * p := by
  have hb := three_transport
    (fun j => affinePairEquiv C D k l hk hl hC hD offC offD s t u v
      hs ht (i j) (his j) (hit j))
    (fun j z => f j z.1 z.2) H p hH hp
    (by intro j; simpa only [Fintype.sum_prod_type] using h2 j)
    (by intro j; simpa only [Fintype.sum_prod_type] using h4 j)
  change (∑ z : AffineFiber C offC s u × AffineFiber D offD t v,
    f 0 (z.1.val (i 0)) (z.2.val (i 0)) * f 1 (z.1.val (i 1)) (z.2.val (i 1)) *
    f 2 (z.1.val (i 2)) (z.2.val (i 2))) ≤ H * p at hb
  simpa only [Fintype.sum_prod_type] using hb
end AES8.PaperThinHolder
