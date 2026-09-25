import Proof.Supplier.RowTupleMaskLoop
import Proof.Supplier.RowMaskLookupReady

/-! The tuple's actual occurrence stream is returned to its first cell and
its counted driver to head1, ready for the common-width equation consumer. -/
namespace NearCubicWires.RepairOrdinary.RowTupleMaskReady
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (N w M k : ℕ) := RowTupleMaskLoop.budget N w M k
def budget (N w M k count : ℕ) := 2*capacity N w M k+count+5

end NearCubicWires.RepairOrdinary.RowTupleMaskReady
