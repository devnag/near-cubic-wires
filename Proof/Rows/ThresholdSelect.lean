import Proof.Rows.SelectionWord
import Proof.Assembly.LiveRows

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_ThresholdSelect
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPrime
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed
open PCJ45bee56da9f34d5a_SelectionWord (gridWord)
open scoped BigOperators
noncomputable section

/-! ## 0. A residue is smaller than its modulus -/

/-! ## 1. \(f_{g,p}(z)\) at an arbitrary live set -/

/-! ## 2. The comparison stream -/

/-! ## 3. The producer -/

end
end PCJ45bee56da9f34d5a_ThresholdSelect
