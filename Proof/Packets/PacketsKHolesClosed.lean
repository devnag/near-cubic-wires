import Proof.Packets.PacketsKHolesSym
import Proof.Packets.PacketsKeysMaskStage
import Proof.Packets.PacketsMaskCountWord

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual.KH
open NearCubicWires NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.PacketsConstruction.Residual

/-- **The kit-dependent packets holes, closed** (no hypotheses). -/
theorem kHoles : ∀ a, KHoles a :=
  kHoles_of_mask_count (fun a => NearCubicWires.PacketsKeys.Stage.maskStage a)
    (fun a => NearCubicWires.PacketsMaskCount.maskCountWord a)

end NearCubicWires.PacketsConstruction.Residual.KH
