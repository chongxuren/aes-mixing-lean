import AESConcrete.ResidualIncidenceAggregation

/-!
# Direct nonnegative restricted-incidence bounds

Keep the actual nonzero restrictions inside the incidence kernel: it is
nonnegative and entrywise dominated by the initial shortened graph. Schur
bounds its genuine row/column masses before the two legitimate residual
contractions. Arbitrary joint real functions are allowed; no product-input or
coordinate-independence premise occurs.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered distinct pairs and 10/14/16 stay fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DirectIncidenceCoefficient
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport multiplicity
  freeCount supportFactor selected_supportFactor selectedSupport_card)
open AESConcrete.ResidualIncidenceAggregation (selected_orthogonal
  selected_action_sum constant_comparison_energy refined_inner diffusionTransfer)
open AESConcrete.RefinedWordProjection (refinedKernel refinedKernel_symmetric)

set_option maxRecDepth 100000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem restricted_nonnegative
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (s : Finset GraphPosition) (out inp : Fin 16)
    (y : MaskCoordinates out → V) (w : MaskCoordinates inp → V) :
    0 ≤ restrictedGraphIncidence L r z s out inp y w := by
  unfold restrictedGraphIncidence
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> norm_num

/-- The signed expansion is not used: deleting graph points only decreases
the actual nonnegative incidence entries. -/
theorem restricted_le_shortened
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (s : Finset GraphPosition) (out inp : Fin 16)
    (y : MaskCoordinates out → V) (w : MaskCoordinates inp → V) :
    restrictedGraphIncidence L r z s out inp y w ≤
      incidenceMultiplicity (shortenedOutput L r z out)
        (shortenedInput L r z inp) y w := by
  classical
  have hbase : incidenceMultiplicity (shortenedOutput L r z out)
      (shortenedInput L r z inp) y w =
      ∑ x : Fin 4 → V,
        (if graphZeroConditions L r z x then (1 : ℝ) else 0) *
          (if restrictCoordinates out (L x) = y ∧ restrictCoordinates inp x = w
            then 1 else 0) := by
    symm
    exact shortened_graph_weight L r z _
  rw [hbase]
  unfold restrictedGraphIncidence
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> simp_all

/-- Direct Schur for the genuine restricted kernel, before projection. -/
theorem restricted_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (s : Finset GraphPosition) (out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : (MaskCoordinates inp → V) → ℝ) :
    (∑ y, action (restrictedGraphIncidence L r z s out inp) f y ^ 2) ≤
      ((Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize out)) *
        (Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize inp))) *
          ∑ x, f x ^ 2 := by
  apply rectangular_schur_energy _ _ _ (by positivity)
    (restricted_nonnegative L r z s out inp) ?_ ?_ f
  · intro y
    calc
      (∑ w, restrictedGraphIncidence L r z s out inp y w) ≤
          ∑ w, incidenceMultiplicity (shortenedOutput L r z out)
            (shortenedInput L r z inp) y w :=
        Finset.sum_le_sum (fun w _ => restricted_le_shortened L r z s out inp y w)
      _ = (Fintype.card {x : ShortenedGraph L r z //
          shortenedOutput L r z out x = y} : ℝ) :=
        incidenceMultiplicity_row _ _ y
      _ ≤ _ := by exact_mod_cast shortened_output_fiber_bound L hL r z out hr y
  · intro w
    calc
      (∑ y, restrictedGraphIncidence L r z s out inp y w) ≤
          ∑ y, incidenceMultiplicity (shortenedOutput L r z out)
            (shortenedInput L r z inp) y w :=
        Finset.sum_le_sum (fun y _ => restricted_le_shortened L r z s out inp y w)
      _ = (Fintype.card {x : ShortenedGraph L r z //
          shortenedInput L r z inp x = w} : ℝ) :=
        incidenceMultiplicity_column _ _ w
      _ ≤ _ := by exact_mod_cast shortened_input_fiber_bound L hL r z inp hz w

/-- The input and output residual operators are contractions on these
same marked-coordinate spaces; domination is never applied after signs. -/
theorem projected_restricted_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z : Fin 16) (s : Finset GraphPosition)
    (out inp : Fin 16) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : (MaskCoordinates inp → V) → ℝ) :
    (∑ y, markedResidual out (action (restrictedGraphIncidence L r z s out inp)
      (markedResidual inp f)) y ^ 2) ≤
      ((Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize out)) *
        (Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize inp))) *
          ∑ x, f x ^ 2 := by
  calc
    _ ≤ ∑ y, action (restrictedGraphIncidence L r z s out inp)
        (markedResidual inp f) y ^ 2 := markedResidual_energy hn out _
    _ ≤ _ := (restricted_energy L hL r z s out inp hr hz _).trans
      (mul_le_mul_of_nonneg_left (markedResidual_energy hn inp f) (by positivity))

def rawSquared (m : ℝ) (d a e b : Fin 5) : ℝ :=
  m^(4-((4-a.val)+(4-b.val)+d.val)) *
    m^(4-((4-a.val)+(4-b.val)+e.val))

def rawCap (m : ℝ) (d a e b : Fin 5) : ℝ :=
  Real.sqrt (rawSquared m d a e b)

def coefficient (m : ℝ) (d a e b : Fin 5) : ℝ :=
  rawCap m d a e b / (supportFactor m d a * supportFactor m e b)

def squaredBound (m : ℝ) (d a e b : Fin 5) : ℝ :=
  (ResidualIncidenceCoefficient.multiplicity d a : ℝ) * (ResidualIncidenceCoefficient.multiplicity e b : ℝ) *
    rawSquared m d a e b / (m-1)^freeCount d a e b

def comparisonCap (m : ℝ) (d a e b : Fin 5) : ℝ :=
  Real.sqrt (squaredBound m d a e b)

theorem rawSquared_nonneg (m : ℝ) (hm : 0 ≤ m) (d a e b : Fin 5) :
    0 ≤ rawSquared m d a e b := by
  exact mul_nonneg (pow_nonneg hm _) (pow_nonneg hm _)

theorem rawCap_sq (m : ℝ) (hm : 0 ≤ m) (d a e b : Fin 5) :
    rawCap m d a e b ^ 2 = rawSquared m d a e b :=
  Real.sq_sqrt (rawSquared_nonneg m hm d a e b)

theorem squaredBound_nonneg (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    0 ≤ squaredBound m d a e b := by
  unfold squaredBound
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (rawSquared_nonneg m (le_trans (by norm_num) hm) d a e b))
      (pow_nonneg (sub_nonneg.mpr hm) _)

theorem comparisonCap_nonneg (m : ℝ) (d a e b : Fin 5) :
    0 ≤ comparisonCap m d a e b := Real.sqrt_nonneg _

theorem comparisonCap_sq (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    comparisonCap m d a e b ^ 2 = squaredBound m d a e b :=
  Real.sq_sqrt (squaredBound_nonneg m hm d a e b)

theorem coefficient_sq (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    coefficient m d a e b ^ 2 =
      rawSquared m d a e b / (m-1)^freeCount d a e b := by
  unfold coefficient supportFactor freeCount
  rw [div_pow, mul_pow, rawCap_sq m (le_trans (by norm_num) hm),
    Real.sq_sqrt (pow_nonneg (sub_nonneg.mpr hm) _),
    Real.sq_sqrt (pow_nonneg (sub_nonneg.mpr hm) _), ← pow_add]

theorem multiplicity_coefficient_sq (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    (ResidualIncidenceCoefficient.multiplicity d a : ℝ) * (ResidualIncidenceCoefficient.multiplicity e b : ℝ) *
      coefficient m d a e b ^ 2 = squaredBound m d a e b := by
  rw [coefficient_sq m hm]
  unfold squaredBound
  ring

theorem support_residual_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : (MaskCoordinates inp → V) → ℝ) (g : (MaskCoordinates out → V) → ℝ) :
    |∑ x : Fin 4 → V, supportEmbedding r out (markedResidual out g) (L x) *
      supportEmbedding z inp (markedResidual inp f) x| ≤
      Real.sqrt ((Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize out)) *
        (Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize inp))) *
          l2 f * l2 g := by
  rw [supportEmbedding_diffusion_bilinear L r z out inp hr hz, markedResidual_inner]
  have hb : l2 (markedResidual out (action
      (restrictedGraphIncidence L r z (unmarkedGraphPositions r z out inp) out inp)
      (markedResidual inp f))) ≤
      Real.sqrt ((Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize out)) *
        (Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize inp))) * l2 f := by
    apply l2_le_of_energy _ f _ (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by positivity)]
    exact projected_restricted_energy L hL hn r z
      (unmarkedGraphPositions r z out inp) out inp hr hz f
  calc
    _ ≤ l2 g * l2 (markedResidual out (action
        (restrictedGraphIncidence L r z (unmarkedGraphPositions r z out inp) out inp)
        (markedResidual inp f))) := abs_inner_le_l2 _ _
    _ ≤ _ := (mul_le_mul_of_nonneg_left hb (l2_nonneg _)).trans_eq (by ring)

theorem normalized_support_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : (MaskCoordinates inp → V) → ℝ) (hf : markedResidual inp f = f)
    (g : (MaskCoordinates out → V) → ℝ) (hg : markedResidual out g = g) :
    |∑ x : Fin 4 → V, supportEmbedding r out g (L x) * supportEmbedding z inp f x| ≤
      (Real.sqrt ((Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize out)) *
        (Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize inp))) /
        (supportNormFactor V r out * supportNormFactor V z inp)) *
          l2 (supportEmbedding z inp f) * l2 (supportEmbedding r out g) := by
  have h := support_residual_diffusion_bilinear L hL hn r z out inp hr hz f g
  rw [hf, hg] at h
  rw [supportEmbedding_l2 hn z inp hz, supportEmbedding_l2 hn r out hr]
  have ho := ne_of_gt (supportNormFactor_pos (V := V) hn r out)
  have hi := ne_of_gt (supportNormFactor_pos (V := V) hn z inp)
  convert h using 1
  field_simp [ho, hi]

theorem supportProduct_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f g : (Fin 4 → V) → ℝ) :
    |∑ x : Fin 4 → V,
      action (supportProduct 0 (AES.maskBit out) (AES.maskBit r)) g (L x) *
      action (supportProduct 0 (AES.maskBit inp) (AES.maskBit z)) f x| ≤
      (Real.sqrt ((Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize out)) *
        (Fintype.card V : ℝ)^(4-(AES.maskSize r+AES.maskSize z+AES.maskSize inp))) /
        (supportNormFactor V r out * supportNormFactor V z inp)) *
          l2 (action (supportProduct 0 (AES.maskBit inp) (AES.maskBit z)) f) *
          l2 (action (supportProduct 0 (AES.maskBit out) (AES.maskBit r)) g) := by
  obtain ⟨f', hf, hef⟩ := supportProduct_residual_representation hn z inp hz f
  obtain ⟨g', hg, heg⟩ := supportProduct_residual_representation hn r out hr g
  rw [hef, heg]
  exact normalized_support_diffusion_bilinear L hL hn r z out inp hr hz f' hf g' hg

theorem selected_coefficient (d a e b : Fin 5)
    (p : SelectedSupport d a) (r : SelectedSupport e b) :
    Real.sqrt ((Fintype.card V : ℝ)^
      (4-(AES.maskSize p.val.val.2+AES.maskSize r.val.val.2+AES.maskSize p.val.val.1)) *
      (Fintype.card V : ℝ)^
      (4-(AES.maskSize p.val.val.2+AES.maskSize r.val.val.2+AES.maskSize r.val.val.1))) /
        (supportNormFactor V p.val.val.2 p.val.val.1 *
          supportNormFactor V r.val.val.2 r.val.val.1) =
      coefficient (Fintype.card V) d a e b := by
  have hpzero : AES.maskSize p.val.val.2 = 4-a.val := by
    have hp := p.property
    omega
  have hrzero : AES.maskSize r.val.val.2 = 4-b.val := by
    have hr := r.property
    omega
  rw [hpzero, hrzero, p.val.property.2, r.val.property.2,
    selected_supportFactor d a p, selected_supportFactor e b r]
  rfl

theorem selected_support_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5)
    (p : SelectedSupport d a) (r : SelectedSupport e b)
    (f g : (Fin 4 → V) → ℝ) :
    |∑ x, supportIndexComponent 0 p.val g (L x) * supportIndexComponent 0 r.val f x| ≤
      coefficient (Fintype.card V) d a e b *
        l2 (supportIndexComponent 0 r.val f) * l2 (supportIndexComponent 0 p.val g) := by
  have h := supportProduct_diffusion_bilinear L hL hn p.val.val.2 r.val.val.2
    p.val.val.1 r.val.val.1 p.val.property.1 r.val.property.1 f g
  rw [selected_coefficient d a e b p r] at h
  exact h

theorem selected_comparison_energy (m : ℝ) (hm : 1 ≤ m)
    (d a e b : Fin 5) (hda : d ≤ a) (heb : e ≤ b)
    (f : SelectedSupport e b → ℝ) :
    (∑ p : SelectedSupport d a,
      action (fun _ : SelectedSupport d a => fun _ : SelectedSupport e b =>
        coefficient m d a e b) f p ^ 2) ≤
      comparisonCap m d a e b ^ 2 * ∑ r, f r ^ 2 := by
  have h := constant_comparison_energy (A := SelectedSupport d a)
    (B := SelectedSupport e b) (coefficient m d a e b) f
  rw [selectedSupport_card d a hda, selectedSupport_card e b heb,
    multiplicity_coefficient_sq m hm, ← comparisonCap_sq m hm] at h
  exact h

theorem refined_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5)
    (hda : d ≤ a) (heb : e ≤ b) (f g : (Fin 4 → V) → ℝ) :
    |∑ x, action (refinedKernel 0 d a) g (L x) * action (refinedKernel 0 e b) f x| ≤
      comparisonCap (Fintype.card V) d a e b *
        l2 (action (refinedKernel 0 e b) f) * l2 (action (refinedKernel 0 d a) g) := by
  have hm : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn.le
  have h := orthogonal_bilinear_comparison
    (fun r : SelectedSupport e b => supportIndexComponent 0 r.val f)
    (fun p : SelectedSupport d a => supportIndexComponent 0 p.val g) L
    (fun p r hpr => selected_orthogonal 0 hn e b p r hpr f f)
    (fun p r hpr => selected_orthogonal 0 hn d a p r hpr g g)
    (fun _ : SelectedSupport d a => fun _ : SelectedSupport e b =>
      coefficient (Fintype.card V) d a e b)
    (comparisonCap (Fintype.card V) d a e b) (comparisonCap_nonneg _ _ _ _ _)
    (selected_comparison_energy _ hm d a e b hda heb)
    (fun p r => selected_support_bilinear L hL hn d a e b p r f g)
  have hout (x : Fin 4 → V) :
      (∑ p : SelectedSupport d a, supportIndexComponent 0 p.val g x) =
        action (refinedKernel 0 d a) g x :=
    congrFun (selected_action_sum 0 d a g) x
  have hin (x : Fin 4 → V) :
      (∑ r : SelectedSupport e b, supportIndexComponent 0 r.val f x) =
        action (refinedKernel 0 e b) f x :=
    congrFun (selected_action_sum 0 e b f) x
  simpa only [hout, hin, selected_action_sum] using h

/-- Retain the actual projected input energy before its optional contraction. -/
theorem refined_diffusion_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5)
    (hda : d ≤ a) (heb : e ≤ b) (f : (Fin 4 → V) → ℝ) :
    (∑ x, diffusionTransfer L d a e b f x ^ 2) ≤
      squaredBound (Fintype.card V) d a e b * ∑ x, action (refinedKernel 0 e b) f x ^ 2 := by
  let g := diffusionTransfer L d a e b f
  let c := comparisonCap (Fintype.card V) d a e b
  have hm : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn.le
  have heq : (∑ x, action (refinedKernel 0 d a) g (L x) *
      action (refinedKernel 0 e b) f x) = ∑ y, g y ^ 2 := by
    calc
      _ = ∑ y, action (refinedKernel 0 d a) g y *
          action (refinedKernel 0 e b) f (L.symm y) := by
        have hs := Equiv.sum_comp L.toEquiv
          (fun y => action (refinedKernel 0 d a) g y *
            action (refinedKernel 0 e b) f (L.symm y))
        change (∑ x, action (refinedKernel 0 d a) g (L x) *
          action (refinedKernel 0 e b) f (L.symm (L x))) =
            ∑ y, action (refinedKernel 0 d a) g y *
              action (refinedKernel 0 e b) f (L.symm y) at hs
        simpa only [L.symm_apply_apply] using hs
      _ = ∑ y, g y * action (refinedKernel 0 d a)
          (fun x => action (refinedKernel 0 e b) f (L.symm x)) y :=
        refined_inner 0 d a g _
      _ = _ := by simp only [g, diffusionTransfer, pow_two]
  have hp : l2 (action (refinedKernel 0 d a) g) ≤ l2 g := by
    simpa only [one_mul] using l2_le_of_energy (action (refinedKernel 0 d a) g) g 1
      (by norm_num) (by simpa only [one_pow, one_mul] using
        FourResidualStep.refined_energy_le 0 hn d a g)
  have hb := refined_diffusion_bilinear L.toAddMonoidHom hL hn d a e b hda heb f g
  change |∑ x, action (refinedKernel 0 d a) g (L x) *
      action (refinedKernel 0 e b) f x| ≤
    comparisonCap (Fintype.card V) d a e b *
      l2 (action (refinedKernel 0 e b) f) * l2 (action (refinedKernel 0 d a) g) at hb
  rw [heq, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), ← l2_sq g] at hb
  have hg := l2_nonneg g
  have hfg := l2_nonneg (action (refinedKernel 0 e b) f)
  have hc : 0 ≤ c := comparisonCap_nonneg _ _ _ _ _
  have ht := hb.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hc hfg))
  have hnorm : l2 g ≤ c * l2 (action (refinedKernel 0 e b) f) := by
    by_cases hz : l2 g = 0
    · rw [hz]
      exact mul_nonneg hc hfg
    · have hg' : 0 < l2 g := lt_of_le_of_ne hg (Ne.symm hz)
      exact le_of_mul_le_mul_right (by simpa only [pow_two] using ht) hg'
  have hsq := (sq_le_sq₀ hg (mul_nonneg hc hfg)).mpr hnorm
  simpa only [mul_pow, l2_sq, g, c, comparisonCap_sq _ hm] using hsq

theorem refined_diffusion_energy_le
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (d a e b : Fin 5)
    (hda : d ≤ a) (heb : e ≤ b) (f : (Fin 4 → V) → ℝ) :
    (∑ x, diffusionTransfer L d a e b f x ^ 2) ≤
      squaredBound (Fintype.card V) d a e b * ∑ x, f x ^ 2 := by
  have hm : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn.le
  exact (refined_diffusion_energy L hL hn d a e b hda heb f).trans
    (mul_le_mul_of_nonneg_left (FourResidualStep.refined_energy_le 0 hn e b f)
      (squaredBound_nonneg _ hm d a e b))

end AESConcrete.DirectIncidenceCoefficient
