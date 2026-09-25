import Proof.CaseAnalysis.WitnessSumTail

/-! One complete raw sum: exact header and actual count, retained count
record, counted original terms, fixed mass check, and successful reset.
Every failure stops before the next stage and needs no restored layout. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def worker {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  SumWork.enter (SumDock.body circuit k q)
noncomputable def tail {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  SumTail.machine (worker circuit k q)
noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  RecoveryGatedSequence.machine SumDock.reader (tail circuit k q) 724
def budget (P H B T k cost : ℕ) (bits arity : List Bool):=
  SumPrefix.budget bits arity T+
    SumTail.budget H (SumBody.budget P B k cost (SumHeader.words bits).length+2)+2
def passed (C T : ℕ) (q : ℚ) (bits arity : List Bool) (circuitPass : List Bool → Bool):=
  SumHeader.flag bits arity T && SumBody.passed C q (SumHeader.words bits) circuitPass

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SumRound
