import AES8.Math.PaperFieldTrace
import Mathlib.GroupTheory.Index

/-! Exact fibers of x ↦ x²+x over any finite field of characteristic two.
This connects the absolute trace to inversion difference counts. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperArtinSchreier
open PaperFieldTrace
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] [Algebra (ZMod 2) F]

def map : F →+ F where
  toFun x := x^2+x
  map_zero' := by simp
  map_add' x y := by rw [add_pow_char]; ring

theorem kernel_iff (x : F) : map x = 0 ↔ x = 0 ∨ x = 1 := by
  change x^2+x = 0 ↔ _
  rw [show x^2+x = x*(x+1) by ring, mul_eq_zero]
  simp [CharTwo.add_eq_zero]

theorem kernel_card : Nat.card (map (F := F)).ker = 2 := by
  have h : ((map (F := F)).ker : Set F) = {0,1} := by
    ext x
    change map x = 0 ↔ x = 0 ∨ x = 1
    exact kernel_iff x
  change Nat.card ((map (F := F)).ker : Set F) = 2
  rw [Nat.card_coe_set_eq, h, Set.ncard_pair zero_ne_one]

def traceHom : F →+ ZMod 2 := (Algebra.trace (ZMod 2) F).toAddMonoidHom

theorem trace_surjective : Function.Surjective (traceHom (F := F)) := by
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  obtain ⟨w,hw⟩ := trace_nonzero (F := F)
  have hw1 : trace w = 1 := (hcases (trace w)).resolve_left hw
  intro z
  rcases hcases z with rfl | rfl
  · exact ⟨0, trace_zero⟩
  · exact ⟨w, hw1⟩

theorem range_eq_trace_kernel : (map (F := F)).range = (traceHom (F := F)).ker := by
  have hs : (map (F := F)).range ≤ (traceHom (F := F)).ker := by
    rintro x ⟨y,rfl⟩
    exact trace_artin_schreier y
  have hm := (map (F := F)).ker.card_mul_index
  rw [AddSubgroup.index_ker, kernel_card] at hm
  have ht := (traceHom (F := F)).ker.card_mul_index
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr trace_surjective] at ht
  have ht' : Nat.card (traceHom (F := F)).ker * 2 = Nat.card F := by
    simpa using ht
  have hc : Nat.card (traceHom (F := F)).ker ≤ Nat.card (map (F := F)).range := by omega
  apply SetLike.ext'
  apply Set.eq_of_subset_of_ncard_le hs
  simpa only [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] using hc

theorem has_root_iff (c : F) : (∃ x : F, x^2+x=c) ↔ trace c=0 := by
  change c ∈ (map (F := F)).range ↔ c ∈ (traceHom (F := F)).ker
  rw [range_eq_trace_kernel]

theorem fiber_card (c : F) :
    (Finset.univ.filter (fun x : F => x^2+x=c)).card =
      if trace c=0 then 2 else 0 := by
  classical
  by_cases hc : trace c=0
  · rw [if_pos hc]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range (map (F := F))
      ((has_root_iff c).mpr hc) (show (0 : F) ∈ Set.range (map (F := F)) from ⟨0,by simp [map]⟩)
    change (Finset.univ.filter (fun x : F => map x=c)).card = 2
    rw [he]
    have hk := kernel_card (F := F)
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, AddMonoidHom.mem_ker] using hk
  · rw [if_neg hc]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hc ((has_root_iff c).mp ⟨x,(Finset.mem_filter.mp hx).2⟩)

end AES8.PaperArtinSchreier
