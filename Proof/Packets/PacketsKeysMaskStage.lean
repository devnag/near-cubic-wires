import Proof.Packets.PacketsKeysSymMask
import Proof.Packets.PacketsKeysThrMask
import Proof.Packets.PacketsMaskCountJoin

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsKeys.Stage
open NearCubicWires NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

def maskStage (a : DecompositionAlgorithm) : KeyStage a (fun r k j => (maskBitsList a r k).getD j []) :=
  (symMask a).join (thrMask a)

end
end NearCubicWires.PacketsKeys.Stage

