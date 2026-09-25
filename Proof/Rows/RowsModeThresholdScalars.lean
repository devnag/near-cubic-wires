import Proof.Rows.RowsModeThresholdSparse

/-! Exact canonical scalar fields for the physical threshold mode.
Only the at-most-four selected child magnitudes and targets are folded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeThresholdSparse
open SupplierPipeline SupplierEstimator SupplierPrime RepairRepresentation ThresholdAlignedEnvelope
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem canonical_base (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) :
    equationListBase (ThresholdRows.equations a r sel)=
      ((∑ i : Fin r.circuits.length,
        childMagnitude ((ThresholdRows.children a (r.circuits.get i)).get (sel i)))+1 : Nat):=by
  unfold equationListBase ThresholdRows.equations
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,thresholdChildEquation_magnitudeBound]

end NearCubicWires.RepairOrdinary.CloseoutRowsModeThresholdSparse
