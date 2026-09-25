import Proof.Rows.CountedGateCell

/-! Native bytes already dominate the sum of every signed coefficient and
threshold magnitude. No arithmetic advice or unary magnitude is supplied. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000
namespace PCJ45bee56da9f34d5a_NativeGateWidth
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierEstimator NearCubicWires.RepairRepresentation
open PCJ45bee56da9f34d5a_FramedGateBank
open scoped BigOperators

theorem magnitude {q : Nat} (g : NormalizedThresholdGate q) (B w : Nat)
 (hb : (PCJ45bee56da9f34d5a_FullGateBounds.source g).length≤B) (hw : B≤w) :
 (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs)<2^w := by
 have h:=RowCachedEquation.equation_magnitude (strict g)
 have h' : (g.threshold-1).natAbs+(∑i,(g.weight i).natAbs)<2^(PCJ45bee56da9f34d5a_FullGateBounds.source g).length := by
  simpa [SupplierPrime.equationMagnitudeBound,RowCachedEquation.equation,strict,
    PCJ45bee56da9f34d5a_FullGateBounds.source,exactWord,Nat.add_comm] using h
 exact h'.trans_le (Nat.pow_le_pow_right (by decide) (hb.trans hw))
end PCJ45bee56da9f34d5a_NativeGateWidth
