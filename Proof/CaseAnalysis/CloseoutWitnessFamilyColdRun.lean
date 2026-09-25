import Proof.CaseAnalysis.WitnessFamilyReady
import Proof.CaseAnalysis.WitnessFamilyHeads
import Proof.CaseAnalysis.WitnessFamilyMode

/-! Actual cold family validation in either mode: paid workspace setup,
canonical exact-V header, every original sum and term, actual circuit
worker, coefficient guard, exact mass test and retained native streams. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold
open LocalBitMultitape CompetitorSumFold CompetitorSumWidth
open RepairSource.VerifierDecoding
open private joined from Proof.CaseAnalysis.RowsCircuitBottomReturned
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def budget (P H V sumCost : ℕ) (bits : List Bool):=FamilyPrepare.budget P H+1+FamilyRun.budget V sumCost bits
def input (P H V C T core W L : ℕ) (bits arity : List Bool) (ambient : Fin 94 → List Bool):=
  FamilyPrepare.tapes (natBitLength C) bits (FamilyInput.blanked
    (FamilyInput.target P H (natBitLength C) V T core W L bits arity [] [] [] ambient))
def passed (sym : Bool) (V C T core W L : ℕ) (q : ℚ) (bits arity : List Bool):=
  FamilyRun.passed V C T q bits arity (FamilyMode.flag sym core W L)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCold
