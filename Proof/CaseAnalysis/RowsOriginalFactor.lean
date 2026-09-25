import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorRun
import Proof.CaseAnalysis.RowsRawAtomCache

/-! One original family factor uses the actual single-cache reader and the
existing Cartesian product, accumulator copy, and logical-length cleanup. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFactor
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
open SubstitutionFactor (heads data productMachine accMachine atomMachine copyMachine productClearMachine)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalFactor
