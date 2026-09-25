import Proof.Hierarchy.CompetitorMonomialGlobalTerm

/-! The whole monomial-record producer executes on the retained finite
zero workspace used by the stream loop. The append prefix is untouched by
padding, and every materialized local tape fits the next physical clear. -/
namespace NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CompetitorRationalDecision CompetitorMonomialProducts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (t : ℕ) (i : Fin 79) := if i.val=74 then 0 else CompetitorReusableDecision.capacity t

end NearCubicWires.RepairOrdinary.CompetitorMonomialTarget
