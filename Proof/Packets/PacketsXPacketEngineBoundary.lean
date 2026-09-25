import Proof.Packets.PacketsXPacketOuterNormalize
import Proof.Packets.PacketsXPacketNativeMeaning

/-! Exact retained word equality between the arithmetic arena and the
native packet-output arena. Zero-backed scratch is retained as allocated
words; only the existing reserve lower bound is used. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketEngineBoundary
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport

theorem state_flat (C R : Nat) (left right : List (List Bool)) (out : List Bool) (hR : 1≤R) :
    ReusableArithmetic.state C R left right=
      fun i : Fin 34=>Theorem25Completion.CycleFlatDock.bank C R left.flatten left.length right out (i.castAdd 1) := by
  have hz : ZeroPadding.pad R [false]=List.replicate R false := by
    change ZeroPadding.pad R (List.replicate 1 false)=_
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  have hc : ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := hz
  funext i
  fin_cases i <;>simp [ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
    ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,NormalizeCold.data,
    Normalize.records,Fin.addCases,Theorem25Completion.CycleFlatDock.bank,
    hz,hc,show ZeroPadding.pad R []=List.replicate R false from by simp [ZeroPadding.pad]]

theorem heads_flat (out : List Bool) : ReusableArithmetic.heads=
    fun i : Fin 34=>Theorem25Completion.CycleFlatDock.heads out (i.castAdd 1) := by
  funext i;fin_cases i <;>rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.PacketEngineBoundary
