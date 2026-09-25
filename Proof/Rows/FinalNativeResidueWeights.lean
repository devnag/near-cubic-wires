import Proof.Rows.FinalNativeResidueCallback
import Proof.CaseAnalysis.RowsOriginalClauseLoop

/-! Weights-only repetition of the actual native callback. One supplied
physical count driver controls all calls; its rewind is included. The
same canonical bank and retained templates persist, including at zero weights. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueWeights
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def words (p w : ℕ) (zs : List ℤ) (j : ℕ) :=
  SignedSortKey.binary w (FinalPrimeReduce.intResidue p (zs.getD j 0))


theorem blocks_range (f : ℕ→List Bool) (j n : ℕ) :
    FinalPrimeModular.blocks f j n=(List.range' j n).flatMap (fun i=>frame (f i)) := by
  induction n generalizing j with
  | zero=>rfl
  | succ n ih=>simp only [FinalPrimeModular.blocks,List.range'_succ,List.flatMap_cons,ih]

theorem concatenated (p w : ℕ) (zs : List ℤ) :
    FinalPrimeModular.blocks (words p w zs) 0 zs.length=
      zs.flatMap (fun z=>frame (SignedSortKey.binary w (FinalPrimeReduce.intResidue p z))) := by
  rw [blocks_range,←List.range_eq_range']
  simpa only [words] using CloseoutRowsFamilyLoop.flatMap_index zs 0
    (fun z=>frame (SignedSortKey.binary w (FinalPrimeReduce.intResidue p z)))

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidueWeights
