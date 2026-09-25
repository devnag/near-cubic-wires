import Proof.Packets.PacketsKeysPrep
import Proof.Packets.PacketsResidualHoles

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsKeys.Prep
open NearCubicWires NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.RepairRepresentation
noncomputable section

/-- **`PrepFam a`**. -/
def prepFam (a : DecompositionAlgorithm) : PrepFam a where
  u := e a
  need := fun _ => 0
  need_pb := PB.const 0
  costC := (vec a).coefficient + 2
  costD := (vec a).degree
  stage := fun X hu _ => prepStage X hu
  cost_le := fun X hu _ r => (prepStage X hu).cost_le r

end
end NearCubicWires.PacketsKeys.Prep

