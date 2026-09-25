import Proof.Supplier.RowOffsetFamilies
import Proof.Hierarchy.CompetitorCountTableRecordRow

/-! Actual residual-cell selectors for the cropped matrix-count consumer.
The physical row carries the larger external RIGHT half and the column the
smaller external LEFT half. Offsets are summed, with no cardinality divisor. -/
namespace NearCubicWires.RepairOrdinary.RowExternalSelection
open SupplierPipeline SupplierEstimator SupplierPrime CompetitorCountMask CompetitorSelectedCells
open CompetitorFinalTable
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def total {u : ℕ} (odd : Bool) (f : Fin u→Fin u→ℕ) : ℕ :=
  if odd then ∑ i,∑ j : Fin (u/2),f i (lowerColumn j) else ∑ i,∑ j,f i j

theorem rect_selected_sum {u v : ℕ} (f : Fin u→Fin v→ℕ) (s : Fin u→Fin v→Bool) :
    (selected (rect f s)).sum=∑ i,∑ j,if s i j then f i j else 0 := by
  simp [selected,rect,List.map_flatten,List.map_ofFn,List.sum_flatten,List.sum_ofFn,Function.comp_def]

theorem cells_selected_sum {u : ℕ} (odd : Bool) (f : Fin u→Fin u→ℕ) (s : Fin u→Fin u→Bool) :
    (selected (cells odd f s)).sum=total odd (fun i j=>if s i j then f i j else 0) := by
  cases odd <;> simp [cells,total,rect_selected_sum]

end
end NearCubicWires.RepairOrdinary.RowExternalSelection
