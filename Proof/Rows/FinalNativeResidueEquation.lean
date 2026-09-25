import Proof.Rows.FinalNativeResidueWeights

/-! The actual weights loop followed by exactly one negated original-target
callback. The physical count tape is retained; the completed coefficient
stream remains at its append end for the subsequent paid rewind. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueEquation
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def weights {n : ℕ} (eq : SupplierPipeline.LabelledEquation (Fin n)) := List.ofFn eq.weights

theorem weight_word (p w : ℕ) {n : ℕ} (eq : SupplierPipeline.LabelledEquation (Fin n)) (i : Fin n) :
    C10NativeResidueWeights.words p w (weights eq) i.val=FinalPrimeReduce.reducedWord p w eq i.val := by
  unfold C10NativeResidueWeights.words weights
  rw [List.getD_eq_getElem _ 0 (by simp only [List.length_ofFn]; exact i.isLt),List.getElem_ofFn]
  exact C10NativeResidue.weight_word p w eq i

theorem weight_blocks (p w : ℕ) {n : ℕ} (eq : SupplierPipeline.LabelledEquation (Fin n)) :
    FinalPrimeModular.blocks (C10NativeResidueWeights.words p w (weights eq)) 0 n=
      FinalPrimeModular.blocks (FinalPrimeReduce.reducedWord p w eq) 0 n := by
  rw [C10NativeResidueWeights.blocks_range,C10NativeResidueWeights.blocks_range]
  apply List.flatMap_congr
  intro i hi
  have hn : i<n := by simpa only [←List.range_eq_range',List.mem_range] using hi
  exact congrArg frame (weight_word p w eq ⟨i,hn⟩)

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueEquation
