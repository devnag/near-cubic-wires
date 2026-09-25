import Proof.CaseAnalysis.RowsTouchingSupportScan

/-! The same retained support frame supplies both candidate flags and the
actual unary row-index input for binomial lookup in one pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def count : List Cell→ℕ
  | []=>0
  | e::xs=>(kept e).toNat+count xs

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
