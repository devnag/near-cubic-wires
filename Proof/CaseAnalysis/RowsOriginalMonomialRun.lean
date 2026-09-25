import Proof.CaseAnalysis.RowsOriginalMonomial
import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomialRun

/-! A halted ordinary receipt for the complete ordered original-factor
expansion, including the empty tuple and every repeated requested factor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
open SubstitutionFactor (data heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
