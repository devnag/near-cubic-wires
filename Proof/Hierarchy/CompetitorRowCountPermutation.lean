import Proof.Hierarchy.CompetitorCountTableBounds

/-! Physical positional-subset enumeration may permute external cut order.
The exact signed sum is invariant under that permutation; ordered equations
inside each power-radix stack are unchanged. -/
namespace NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope MatrixScoreBatch EquationRow RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem request_modEq_perm {l r : ℕ} (w Q : ℕ) (rows : List (List (List (Equation l r))))
    (input : EquationRow.Input) (hc : input.cuts.Perm (RowPowerBinLift.batch w Q rows))
    (hw : ∀ ms ∈ rows,∀ e ∈ ms.flatten,equationMagnitudeBound e<2^w)
    (row column : Fin (request input).U) : Int.ModEq ((2 : ℤ)^Q)
      (weightedDominance (leftScore (request input)) (rightScore (request input))
        (weight (request input)) row column) (count rows row.val column.val) := by
  rw [request_value]
  have hs := (hc.map (fun c => exactValue c row.val column.val)).sum_eq
  rw [hs,batch_value w Q rows hw]
  exact lifted_modEq Q rows row.val column.val

end NearCubicWires.RepairOrdinary.CompetitorRowCountMeaning

namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open CompetitorCrossScheduler (producer)
open SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
open SupplierPrime ThresholdAlignedEnvelope RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairOrdinary.CompetitorCountTable
