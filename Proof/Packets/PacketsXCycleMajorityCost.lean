import Proof.Packets.PacketsXBooleanSelectorResident
import Proof.Assembly.ClosureBinaryEnumerator

/-! Explicit majority truth-row callback and enumeration costs. These scalar
lemmas evaluate the actual component budgets; the callback execution theorem
must still attach the displayed sum to its composed machine. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires PCJ9eff70d512234a4c_Fixed.Materializer

def majorityTermBudget (C w N : Nat):=BooleanSelectorResident.budget C w N+14*N+14*commonReserve C w+59

end Theorem25Completion.CycleBounds
