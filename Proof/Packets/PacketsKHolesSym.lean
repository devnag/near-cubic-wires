import Proof.Packets.PacketsKHoles
import Proof.Packets.PacketsSymMetaPG

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual.KH
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction NearCubicWires.PacketsConstruction.Residual
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

def symAt (a : DecompositionAlgorithm) : PacketsCombine.SymMeta a (kitShapePG a) :=
  NearCubicWires.PacketsSymBits.Meta.symMetaPG a (wS a)

/-- **The kit-dependent holes, from the mask bits and the mask-loop counter alone.** -/
theorem kHoles_of_mask_count (maskS : ∀ a, KeyStage a (fun r k j => (maskBitsList a r k).getD j []))
    (cntS : ∀ a, KeyWord a (fun r k => CompareMachine.word (maskCount a r k))) : ∀ a, KHoles a :=
  kHoles_of maskS cntS symAt

end
end NearCubicWires.PacketsConstruction.Residual.KH
