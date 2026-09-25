import Proof.Supplier.RowTupleFrame

/-! One actual enumerated frame executes through the complete reusable
equation body and its paid three-cell trailer. The next cursor is exactly
the end of that frame, including the zero-degree case. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFramedBody
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (w : ℕ) (ds : List ℕ) := frame (SignedSortKey.binary (w*ds.length+1) (RowTupleDigits.encode w ds))

end NearCubicWires.RepairOrdinary.RowTupleFramedBody
