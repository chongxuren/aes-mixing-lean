import AESConcrete.MDSGraphFirstCap
import AESConcrete.FirstHighReturn
import AESConcrete.NonzeroUniformGraphCap

/-! Compose the two actual graph caps with the first return theorem.
The unconditional endpoint is a local physical-system return bound; the full
10/14/16 experiment theorem remains open. The earlier conditional interface
is retained. Constructive mathematics only; no attacks or manuscript edits. -/

noncomputable section
namespace AESConcrete.GraphFirstReturn

theorem system_first_high_return_cap_of_graph
    (h12 : ‖PhysicalProjectionSystem.system.step 13 12‖ ≤
      AESRound.Terminal.lambda * AESRound.Certificate.L 13 12) :
    ‖PhysicalProjectionSystem.system.ret 13 13‖ ≤
      AESRound.Terminal.lambda ^ 2 * AESRound.Certificate.J 13 13 :=
  FirstHighReturn.system_first_high_return_cap
    MDSGraphFirstCap.system_thirteen_eleven_step_cap h12

theorem system_first_high_return_cap :
    ‖PhysicalProjectionSystem.system.ret 13 13‖ ≤
      AESRound.Terminal.lambda ^ 2 * AESRound.Certificate.J 13 13 :=
  system_first_high_return_cap_of_graph
    NonzeroUniformGraphCap.system_thirteen_twelve_step_cap

end AESConcrete.GraphFirstReturn
