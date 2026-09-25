import Proof.CaseAnalysis.WitnessSumControl

/-! One complete prepared sum: the actual counted term loop rejects
immediately, or the original final mass test runs once and resets the
accumulator. Both retained record streams keep their logical cursors. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumBody
open LocalBitMultitape RecoveryRootRound RecoveryExecution CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ) :=
  RecoveryGatedSequence.machine (TermLoop.machine circuit) (ending k q) 724
def budget (P B k cost K : ℕ) := TermLoop.budget cost K+SumFinish.budget P B k+2
def passed (C : ℕ) (q : ℚ) (words : List (List Bool)) (circuitPass : List Bool → Bool) : Bool :=
  TermLoop.passed C words circuitPass && decide ((TermLoop.mass C words words.length).value ≤ q)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumBody
