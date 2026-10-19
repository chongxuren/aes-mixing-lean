import AESMixing.ProductDifference
import AESMixing.TupleKeys

/-! Deterministic linear relabelings of difference laws. The input and
output formulas let the physical AES layers be grouped at the law level. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def lawRelabel {V : Type*} (e : Equiv.Perm V) (f : V → ℝ) : V → ℝ :=
  fun y => f (e.symm y)

theorem lawRelabel_injective {V : Type*} (e : Equiv.Perm V) :
    Function.Injective (lawRelabel e) := by
  intro f g h
  funext x
  have hh := congrFun h (e x)
  simpa only [lawRelabel, e.symm_apply_apply] using hh

theorem lawRelabel_trans {V : Type*} (e d : Equiv.Perm V) (f : V → ℝ) :
    lawRelabel e (lawRelabel d f) = lawRelabel (d.trans e) f := rfl

theorem lawRelabel_differencePoint {V : Type*} [DecidableEq V]
    (e : Equiv.Perm V) (a : V) :
    lawRelabel e (differencePoint a) = differencePoint (e a) := by
  funext b
  unfold lawRelabel differencePoint
  simp only [← e.apply_eq_iff_eq_symm_apply]

theorem tv_lawRelabel {V : Type*} [Fintype V]
    (e : Equiv.Perm V) (p q : V → ℝ) :
    tv (lawRelabel e p) (lawRelabel e q) = tv p q :=
  tv_relabel e.symm p q

theorem lawRelabel_uniformExcept {V : Type*} [Fintype V] [DecidableEq V]
    (e : Equiv.Perm V) (z : V) (hz : e z = z) :
    lawRelabel e (uniformExcept z) = uniformExcept z := by
  funext y
  have he : e.symm y = z ↔ y = z := by
    constructor
    · intro h
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, hz] using hh
    · rintro rfl
      exact e.symm_apply_eq.mpr hz.symm
  simp only [lawRelabel, uniformExcept, he]

theorem tv_lawRelabel_uniformExcept {V : Type*} [Fintype V] [DecidableEq V]
    (e : Equiv.Perm V) (z : V) (hz : e z = z) (p : V → ℝ) :
    tv (lawRelabel e p) (uniformExcept z) = tv p (uniformExcept z) := by
  calc
    tv (lawRelabel e p) (uniformExcept z) =
        tv (lawRelabel e p) (lawRelabel e (uniformExcept z)) := by
      rw [lawRelabel_uniformExcept e z hz]
    _ = tv p (uniformExcept z) := tv_lawRelabel e p _

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

theorem differenceChannel_linearInput (s : Equiv.Perm V) (L : V ≃+ V) (b a : V) :
    differenceChannel (L.toEquiv.trans s) b a = differenceChannel s b (L a) := by
  have hd (x : V) : difference (L.toEquiv.trans s) a x = difference s (L a) (L x) := by
    simp only [difference, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      map_add]
  unfold differenceChannel
  simp_rw [hd]
  exact congrArg (fun t : ℝ => t / Fintype.card V)
    (Equiv.sum_comp L.toEquiv (fun x => if difference s (L a) x = b then (1 : ℝ) else 0))

theorem difference_action_linearOutput (s : Equiv.Perm V) (L : V ≃+ V) (f : V → ℝ) :
    action (differenceChannel (s.trans L.toEquiv)) f =
      lawRelabel L.toEquiv (action (differenceChannel s) f) := by
  funext y
  simp only [action, differenceChannel_linearOutput, lawRelabel]
  rfl

theorem difference_channel_commuting (s : Equiv.Perm V) (L : V ≃+ V)
    (h : ∀ x, s (L x) = L (s x)) (b a : V) :
    differenceChannel s b (L a) = differenceChannel s (L.symm b) a := by
  have he : L.toEquiv.trans s = s.trans L.toEquiv := Equiv.ext h
  rw [← differenceChannel_linearInput, he, differenceChannel_linearOutput]

theorem difference_action_commuting (s : Equiv.Perm V) (L : V ≃+ V)
    (h : ∀ x, s (L x) = L (s x)) (f : V → ℝ) :
    action (differenceChannel s) (lawRelabel L.toEquiv f) =
      lawRelabel L.toEquiv (action (differenceChannel s) f) := by
  funext y
  have ht := Equiv.sum_comp L.toEquiv
    (fun x => differenceChannel s y x * f (L.symm x))
  simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, L.symm_apply_apply,
    difference_channel_commuting s L h] at ht
  exact ht.symm

end AESMixing
