import AESMixing.PhysicalLawOps
import AESPaper.TwoLayerGrouping

/-!
The paper's superbox grouping, derived from the physical difference
chain. Fixed input/output ShiftRows relabelings are retained explicitly.
-/
noncomputable section
namespace AESMixing.AES

theorem ordinaryDifferenceLaw_iterate (n : ℕ) (a : State) :
    ordinaryDifferenceLaw n a =
      ((mixLaw ∘ shiftLaw ∘ substituteLaw)^[n]) (differencePoint a) := by
  have hop : (mixLaw ∘ shiftLaw ∘ substituteLaw) = action (differenceChannel ordinaryLayer) := by
    funext f
    rw [Function.comp_apply, Function.comp_apply, ordinary_difference_action]
  conv_rhs => rw [hop]
  induction n with
  | zero => rfl
  | succ n ih =>
    conv_lhs => rw [ordinaryDifferenceLaw]
    conv_rhs => rw [Function.iterate_succ_apply']
    exact congrArg (action (differenceChannel ordinaryLayer)) ih

theorem mix_physical_difference (n : ℕ) (a : State) :
    mixLaw (physicalDifferenceLaw (n+1) a) = ordinaryDifferenceLaw (n+1) a := by
  exact (congrArg mixLaw (final_difference_action (ordinaryDifferenceLaw n a))).trans
    (ordinary_difference_action (ordinaryDifferenceLaw n a)).symm

theorem physical_superbox_grouping (n : ℕ) (a : State) :
    physicalDifferenceLaw (2*n+2) a =
      shiftLaw (superboxLaw (((interSuperboxLaw ∘ superboxLaw)^[n])
        (shiftLaw (differencePoint a)))) := by
  have hm := mix_physical_difference (2*n+1) a
  change mixLaw (physicalDifferenceLaw (2*n+2) a) = ordinaryDifferenceLaw (2*n+2) a at hm
  have hi := ordinaryDifferenceLaw_iterate (2*n+2) a
  have hg := two_layer_grouping substituteLaw shiftLaw mixLaw
    substitute_shift_commutes n (differencePoint a)
  exact lawRelabel_injective mixColumnsEquiv.toEquiv (hm.trans (hi.trans hg))

theorem shift_differencePoint (a : State) :
    shiftLaw (differencePoint a) = differencePoint (shiftRows a) := by
  exact lawRelabel_differencePoint shiftRowsEquiv.toEquiv a

theorem four_round_superboxes (a : State) :
    physicalDifferenceLaw 4 a =
      shiftLaw (superboxLaw (interSuperboxLaw (superboxLaw (differencePoint (shiftRows a))))) := by
  have h := physical_superbox_grouping 1 a
  rw [show 2 * 1 + 2 = 4 from rfl] at h
  conv_rhs at h =>
    arg 1
    arg 1
    rw [Function.iterate_one, Function.comp_apply]
  exact h.trans (congrArg
    (fun f : State → ℝ => shiftLaw (superboxLaw (interSuperboxLaw (superboxLaw f))))
    (shift_differencePoint a))

end AESMixing.AES
