import Proof.Hierarchy.CompetitorThresholdConstants

/-! The literal threshold decision with independently retained finite zero
padding on each tape. This transports the same physical transition run;
it neither creates padding nor assumes any extra arithmetic hypothesis. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMixedThreshold
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorThresholdDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (lower : Bool) (b p n d : ℕ) (q : ℚ) (pads : Fin 67 → ℕ) : Fin 67 → List Bool :=
  fun i => ZeroPadding.pad (pads i) (CompetitorThresholdDecision.input lower b p n d q i)

end NearCubicWires.RepairOrdinary.CompetitorMixedThreshold
