import Proof.Packets.PacketsXVectorWorkerParentsBounded
import Proof.Packets.PacketsXVectorWorkerLevelBody

/-! A complete actual level update. Both nested arithmetic loops, every
indexed write, and bank turnover are discharged; the remaining two machine
interfaces are the finite level preparation and finite literal provider. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds SubstitutionCensus
noncomputable section

def oneLevelFuel (R D N preparation : Nat):=
  preparation+allParentsFuel R D N+VectorTransfer.budget R N+2*R+9

attribute [local irreducible] prepareLevel parents levelBody

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
