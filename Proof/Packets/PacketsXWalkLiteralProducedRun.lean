import Proof.Packets.PacketsXWalkLiteralProducedLayout

/-! A fixed ordinary program from raw scalars and the actual walk sample words
to the complete rewound transcript, with no supplied palette or workspace. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
open VectorBottomUp CloseoutRowsModeCache Theorem25Completion.CycleBounds
noncomputable section
variable {population active depth n : Nat}
attribute [local irreducible] entryMachine WalkLiteralCold.program

def walkMachine := RecoveryFocus.machine coldSlots WalkLiteralCold.program
def machine := Composition.machine entryMachine walkMachine
def budget (C w root population active depth S n : Nat) (mask : List Bool) :=
  entryBudget C (commonReserve C w) root population active mask+1+
    WalkLiteralCold.programBudget C w population active root depth S n
def finalHeads (n : Nat) := dockH coldSlots preparedHeads (WalkLiteralCold.H (160*n) 0)

end
end Theorem25Completion.WalkLiteralProduced
