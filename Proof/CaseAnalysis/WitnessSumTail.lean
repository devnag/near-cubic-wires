import Proof.CaseAnalysis.WitnessSumStorage

/-! A false term or mass verdict halts immediately. Only the successful
whole sum body enters the single rewind/erase tail and returns the exact
next-sum layout, with all three retained output cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumTail
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine {s : ℕ} (body : Machine 3061 s):=
  RecoveryGatedSequence.machine body SumCleanup.machine 724
def budget (H fuel : ℕ):=fuel+SumCleanup.budget H+2

end NearCubicWires.RepairOrdinary.CloseoutWitness.SumTail
