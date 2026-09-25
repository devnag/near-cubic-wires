import Proof.CaseAnalysis.RowsModeParityReusable

/-! The existing wrapping predecessor is sufficient for the shifted-window
coefficient. Its only wrapped zero case has lower binomial index zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeShift
open SignedSortKey RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def top (w offset b : Nat):=value (RecoveryListPredecessor.result (binary w (offset+b)) true)

theorem top_fit (w offset b : Nat) : top w offset b<2^w:=by
  simpa [top] using value_lt (RecoveryListPredecessor.result (binary w (offset+b)) true)

theorem top_binary (w offset b : Nat) :
    RecoveryListPredecessor.result (binary w (offset+b)) true=binary w (top w offset b):=by
  simpa [top] using (BoundedCounter.binary_of_value
    (RecoveryListPredecessor.result (binary w (offset+b)) true)).symm

theorem coefficient (w offset b : Nat) (hfit : offset+b<2^w) :
    (top w offset b).choose b%2=(offset+b-1).choose b%2:=by
  by_cases hzero:offset+b=0
  · have hb:b=0:=by omega
    simp [hb]
  · have hv:=binary_value w (offset+b) hfit
    have h:=RecoveryListPredecessor.predecessor_value (binary w (offset+b)) (by rw [hv];exact hzero)
    rw [hv] at h
    exact congrArg (fun x=>x.choose b%2) h

end NearCubicWires.RepairOrdinary.CloseoutRowsModeShift
