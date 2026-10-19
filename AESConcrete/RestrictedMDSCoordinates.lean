import AESConcrete.ShortenedLineResponse

/-!
# Mixed information sets for restricted AES sources

The first zero mask is always on outputs; the second is on inputs. A
shortened source can be parametrized by disjoint free input sets, or by a
mixed set of output and input coordinates. Comparing those two actual
parametrizations proves that each fixed-input section maps bijectively to
the marked outputs. No probability or operator bound is assumed here.

Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
namespace AESConcrete.RestrictedMDSCoordinates
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)

/-- Two bijective parametrizations with the same first coordinate induce
bijective maps on every section. -/
theorem section_bijective {C S U Y : Type*}
    (e : C ≃ S × U) (f : C ≃ S × Y)
    (hfirst : ∀ c, (f c).1 = (e c).1) (s : S) :
    Function.Bijective (fun u => (f (e.symm (s,u))).2) := by
  constructor
  · intro u v h
    have he : f (e.symm (s,u)) = f (e.symm (s,v)) := by
      apply Prod.ext
      · simp only [hfirst, Equiv.apply_symm_apply]
      · exact h
    have hc := f.injective he
    have hp := congrArg e hc
    simpa only [Equiv.apply_symm_apply, Prod.mk.injEq, true_and] using hp
  · intro y
    let c := f.symm (s,y)
    have hs : (e c).1 = s := by
      rw [← hfirst]
      exact congrArg Prod.fst (f.apply_symm_apply (s,y))
    refine ⟨(e c).2, ?_⟩
    have he : e.symm (s, (e c).2) = c := by
      apply e.injective
      rw [Equiv.apply_symm_apply, ← hs]
    change (f (e.symm (s, (e c).2))).2 = y
    rw [he]
    exact congrArg Prod.snd (f.apply_symm_apply (s,y))

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def inputSplit (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z s u : Fin 16)
    (c : ShortenedGraph L r z) :
    (MaskCoordinates s → V) × (MaskCoordinates u → V) :=
  (fun i => c.val i.val, fun i => c.val i.val)

theorem inputSplit_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4) :
    Function.Bijective (inputSplit L r z s u) := by
  have htotal : maskSize r + maskSize z + maskSize 0 + maskSize (maskUnion s u) = 4 := by
    rw [maskUnion_size s u hsu, show maskSize (0 : Fin 16) = 0 by decide]
    omega
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro c d h
    apply shortened_projection_injective L hL r z 0 (maskUnion s u)
      (mask_disjoint_empty r) hzu htotal
    apply Prod.ext
    · funext i
      exact (empty_mask_coordinate i).elim
    · funext i
      have hi := i.property
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact congrFun (congrArg Prod.fst h) ⟨i.val, hi⟩
      · exact congrFun (congrArg Prod.snd h) ⟨i.val, hi⟩
  · change Fintype.card {x : Fin 4 → V // graphZeroConditions L r z x} = _
    rw [mds_graph_zero_count L hL, Fintype.card_prod]
    simp only [Fintype.card_fun, maskCoordinates_card]
    rw [← pow_add]
    congr 1
    omega

def inputSplitEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4) :
    ShortenedGraph L r z ≃ (MaskCoordinates s → V) × (MaskCoordinates u → V) :=
  Equiv.ofBijective (inputSplit L r z s u)
    (inputSplit_bijective L hL r z s u hsu hzu hsize)

def mixedSplitEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z out s : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z s)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize s = 4) :
    ShortenedGraph L r z ≃ (MaskCoordinates s → V) × (MaskCoordinates out → V) :=
  (Equiv.ofBijective (shortenedProjection L r z out s)
    (shortened_projection_bijective L hL r z out s hr hz hsize)).trans
      (Equiv.prodComm _ _)

theorem output_section_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z s)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (a : MaskCoordinates s → V) :
    Function.Bijective (fun b : MaskCoordinates u → V =>
      fun i : MaskCoordinates out =>
        L ((inputSplitEquiv L hL r z s u hsu hzu hsize).symm (a,b)).val i.val) := by
  exact section_bijective (inputSplitEquiv L hL r z s u hsu hzu hsize)
    (mixedSplitEquiv L hL r z out s hr hz hobs) (fun _ => rfl) a

theorem output_projection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z out : Fin 16)
    (hr : MaskDisjoint r out)
    (hsize : maskSize r + maskSize z + maskSize out = 4) :
    Function.Bijective (fun c : ShortenedGraph L r z =>
      fun i : MaskCoordinates out => L c.val i.val) := by
  have hs : maskSize r + maskSize z + maskSize out + maskSize 0 = 4 := by
    simpa only [show maskSize (0 : Fin 16) = 0 by decide, add_zero] using hsize
  have hb := shortened_projection_bijective L hL r z out 0 hr (mask_disjoint_empty z) hs
  constructor
  · intro c d h
    apply hb.1
    apply Prod.ext h
    funext i
    exact (empty_mask_coordinate i).elim
  · intro y
    obtain ⟨c,hc⟩ := hb.2 (y,fun _ => 0)
    exact ⟨c,congrArg Prod.fst hc⟩

theorem input_projection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z inp : Fin 16)
    (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize inp = 4) :
    Function.Bijective (fun c : ShortenedGraph L r z =>
      fun i : MaskCoordinates inp => c.val i.val) := by
  have hs : maskSize r + maskSize z + maskSize 0 + maskSize inp = 4 := by
    simpa only [show maskSize (0 : Fin 16) = 0 by decide, add_zero] using hsize
  have hb := shortened_projection_bijective L hL r z 0 inp (mask_disjoint_empty r) hz hs
  constructor
  · intro c d h
    apply hb.1
    apply Prod.ext
    · funext i
      exact (empty_mask_coordinate i).elim
    · exact h
  · intro y
    obtain ⟨c,hc⟩ := hb.2 ((fun _ => 0),y)
    exact ⟨c,congrArg Prod.snd hc⟩

end Generic

def actualInputEquiv (inverse : Bool) (r z inp : Fin 16)
    (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize inp = 4) :
    ShortenedGraph (byteDiffusionHom inverse) r z ≃ (MaskCoordinates inp → BinaryWord 8) :=
  Equiv.ofBijective (fun c => fun i => c.val i.val)
    (input_projection_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z inp hz hsize)

theorem actualInputEquiv_apply (inverse : Bool) (r z inp : Fin 16)
    (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize inp = 4)
    (c : ShortenedGraph (byteDiffusionHom inverse) r z) (i : MaskCoordinates inp) :
    actualInputEquiv inverse r z inp hz hsize c i = c.val i.val := rfl

/-- Actual forward and inverse AES diffusion; no MDS premise is exported. -/
theorem actual_output_projection_bijective (inverse : Bool) (r z out : Fin 16)
    (hr : MaskDisjoint r out)
    (hsize : maskSize r + maskSize z + maskSize out = 4) :
    Function.Bijective (fun c : ShortenedGraph (byteDiffusionHom inverse) r z =>
      fun i : MaskCoordinates out => byteDiffusionOrientation inverse c.val i.val) := by
  simpa only [ShortenedLineResponse.byteDiffusionHom_apply] using
    output_projection_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z out hr hsize

theorem actual_output_section_bijective (inverse : Bool) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z s)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (a : MaskCoordinates s → BinaryWord 8) :
    Function.Bijective (fun b : MaskCoordinates u → BinaryWord 8 =>
      fun i : MaskCoordinates out => byteDiffusionOrientation inverse
        ((inputSplitEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z s u hsu hzu hsize).symm (a,b)).val i.val) := by
  simpa only [ShortenedLineResponse.byteDiffusionHom_apply] using
    output_section_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      r z s u out hsu hzu hsize hr hz hobs a

end AESConcrete.RestrictedMDSCoordinates
