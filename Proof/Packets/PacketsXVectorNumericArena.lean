import Proof.Packets.GradedWindowReusable
import Proof.Packets.PacketsXDeltaMetadata

/-! Concrete 299-tape numeric arena. All window and delta scalar masters are
outside the private arithmetic work, and the cleanup is an actual parallel
R-cell overwrite with retained capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open RecoveryRootRound
noncomputable section

def heads (i : Fin 299) : Nat :=
  if i=31 ∨ i=258 ∨ i=259 ∨ i=260 ∨ i=296 ∨ i=297 ∨ i=298 then 1 else 0


end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
