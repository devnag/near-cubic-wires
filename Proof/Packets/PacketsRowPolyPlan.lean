import Proof.Packets.PacketsStreamBound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-- SYM row polynomial = conjunction of shifted one-hot lookups of walk coordinate vectors. -/
theorem sym_rowPoly (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.SymKey r L target) :
    (rcDecode a (.sym r four L target) k).polynomial =
      Normalized.structuralGF2FiniteConjunction (fun i : Fin r.circuits.length =>
        Normalized.structuralGF2OneHotLookup
          (shiftedFiniteLookup (k.offset i) (symmetricCircuitTopLookup r i))
          (LiveRows.coordinatePoly true (symmetricFourfoldOccurrences r)
            (CyclicChoice.live (symmetricFourfoldOccurrences r) L) (symmetricListDenominator r target)
            (symmetricCircuitMask r i) k.seed)) := rfl

/-- THR row polynomial = modular radix row over the digit masks' walk coordinate vectors. -/
theorem thr_rowPoly (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (four : r.circuits.length ≤ 4) (L target : ℕ) (k : RCFive.RowKeys.ThrKey a r L target) :
    (rcDecode a (.thr r four L target) k).polynomial =
      Normalized.structuralGF2ModularRadixRow (digits := modulusDigitCount k.prime.val)
        k.prime.val k.residue.val 2
        (fun digit candidate => LiveRows.coordinatePoly true (thresholdFourfoldOccurrences r)
          (CyclicChoice.live (thresholdFourfoldOccurrences r) L)
          (CloseoutFinalC10ThresholdRows.listDenominator a r target)
          (Finset.univ.filter (fun i =>
            (modularCoefficientResidue (ThresholdRows.equation a r k.selection) k.prime.val i).testBit digit.val))
          k.seed candidate) := rfl

end
end NearCubicWires.PacketsConstruction
