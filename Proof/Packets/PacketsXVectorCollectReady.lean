import Proof.Packets.PacketsXVectorPaletteCollectLayout

/-! Retained, physically produced words needed to rewind the collected bank. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

structure TranscriptRewindReady (R S N : Nat) (work : Fin 299 → List Bool) : Prop where
  width : work 31=ZeroPadding.pad S (UnaryTemplate.tape R)
  count : work 297=ZeroPadding.pad S (CompareMachine.word N)
  scratch : work 261=List.replicate S false
  zero : work 263=List.replicate S false
  payload : work 257=List.replicate S false

theorem collect_ready (R S N : Nat) (raw : Fin 299 → List Bool) (hRS : R≤S)
    (hwidth : raw 31=UnaryTemplate.tape R)
    (hcount : raw 297=ZeroPadding.pad R (CompareMachine.word N))
    (hscratch : raw 261=ZeroPadding.pad R [])
    (hzero : raw 263=List.replicate R false) :
    TranscriptRewindReady R S N
      (Function.update (fun i=>ZeroPadding.pad S (raw i)) 257 (List.replicate S false)) := by
  constructor
  · simpa only [Function.update_of_ne (by decide : (31 : Fin 299)≠257)] using congrArg (ZeroPadding.pad S) hwidth
  · simp only [Function.update_of_ne (by decide : (297 : Fin 299)≠257),hcount,
      MatrixBucketRootPower.pad_pad R S _ hRS]
  · simp only [Function.update_of_ne (by decide : (261 : Fin 299)≠257),hscratch,
      MatrixBucketRootPower.pad_pad R S _ hRS]
    simp [ZeroPadding.pad]
  · simp only [Function.update_of_ne (by decide : (263 : Fin 299)≠257),hzero,
      Rewind.Workspace.pad_zeros,Nat.max_eq_left hRS]

  · exact Function.update_self _ _ _

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
