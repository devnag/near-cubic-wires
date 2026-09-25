import Proof.SourceAssembly.SourceCodeFamily
import Proof.MachineModel.BlockScrubEntry

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction
noncomputable section

/-- `stop` halts at once: every bank is its own exit at zero fuel. -/
theorem stop_step {U : Nat} (H : Fin U → Nat) (A : Fin U → List Bool) :
    Step (CloseoutRowsOriginalSwitch.stop U) 0 H A H A := by
  let c : Configuration U 1 := ⟨0, H, A⟩
  let r : ExecutionReceipt U 1 := ⟨c, 0, c.tapeCells⟩
  exact ⟨r, rfl, rfl, rfl, Nat.le_refl 0⟩

end
end NearCubicWires.SourceConstruction
end
