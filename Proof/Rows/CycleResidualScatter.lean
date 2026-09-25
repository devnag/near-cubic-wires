import Proof.Rows.MaskProductBody

/-! An ordinary residual-coordinate scatter. At an original live coordinate
it writes false; at a residual coordinate it consumes the next compressed
bit. This directly consumes the frozen live membership mask rather than
requiring an additional precomputed complement mask. The counted scan and
paid head restoration include all coordinates, including q=0. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleResidualScatter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding




theorem cfg_eq {t s : Nat} (phase : Fin 5) (a b : Configuration t s) (total driver : Nat)
    (hh : a.heads=b.heads) (ht : a.tapes=b.tapes) :
    RepeatMachine.cfg phase a total driver=RepeatMachine.cfg phase b total driver := by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh,ht]




end Theorem25Completion.CycleResidualScatter
