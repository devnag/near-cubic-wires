import Proof.Packets.ReusableNativeNormalize

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding

theorem input_layout (C R : Nat) (P : List (List Nat)) (hC : C≤R) (hR : 1≤R) :
    input C R P=Function.update (ready C R []) 30 (ZeroPadding.pad R (ExtIncidence.stream P)) := by
  have one : ZeroPadding.pad R [false]=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  have zero : ZeroPadding.pad R (List.replicate C false)=List.replicate R false := by
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hC]
  funext i
  fin_cases i <;> simp [input,ready,readyData,bank,padded,NativeNormalized.A,NativeNormalized.extra,
    NormalizedAddition.data,NormalizedAddition.extras,NormalizeCold.data,Normalize.records,
    NearCubicWires.RepairSource.ProjectionNormalization.SuffixScan.stream,
    CompareMachine.word,Fin.addCases,Function.update,one,zero,ZeroPadding.pad]
  all_goals first | omega | (rw [←List.replicate_succ];congr 1;omega)


end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
