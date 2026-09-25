import Proof.CaseAnalysis.CloseoutWitnessFamilyLayout

/-! One complete original family field: the paid loader and verdict
prime feed the already-checked whole sum directly. Successful output
returns the same reusable bank and three ordered logical streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRound
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

noncomputable def body {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  TapeEmbedding.machine 2 (SumRound.machine circuit k q)
noncomputable def machine {s : ℕ} (circuit : Machine 1703 s) (k : ℕ) (q : ℚ):=
  Composition.machine FamilyLoad.prepare (body circuit k q)
def budget (P H B T k cost : ℕ) (bits arity : List Bool):=
  FamilyLoad.budget bits+1+SumRound.budget P H B T k cost bits arity
def coefficientWord (C : ℕ) (bits : List Bool):=
  (SumHeader.words bits).flatMap (TermLoop.coefficientWord C)
def nativeWord (word : List Bool → List Bool) (bits : List Bool):=
  (SumHeader.words bits).flatMap word
def countWord (bits : List Bool):=RepairRepresentation.natWord (SumFields.count bits)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyRound
