import Proof.CaseAnalysis.RowsModeCacheReuseRun

/-! The original delta target has an exact unsigned preparation.
One split of the actual child counter produces both offset and capped count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeDeltaTarget
open SupplierListPolynomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capped_target (childCard window parent child : Nat) :
    deltaTarget? childCard window parent child=
      if 2*child ≤ min childCard window+parent ∧
          min childCard window+parent ≤ 2*child+2*window
      then some (min childCard window+parent-2*child) else none:=by
  have hm:childCard=childCard-window+min childCard window:=by omega
  have hg : (((childCard-window : Nat) : Int) ≤ (childCard : Int)+parent-2*child ∧
      (childCard : Int)+parent-2*child ≤ ((childCard-window+2*window : Nat) : Int)) ↔
      (2*child ≤ min childCard window+parent ∧ min childCard window+parent ≤ 2*child+2*window):=by omega
  simp only [deltaTarget?,desiredDeltaLiteral,hg]
  split_ifs with h
  · apply congrArg some
    omega
  · rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsModeDeltaTarget
