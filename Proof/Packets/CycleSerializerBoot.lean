import Proof.Packets.CycleLiveSuccessor

/-! Seed the serializer's index in an already allocated zero log. The log is
produced by the record-width machine; two actual transitions write the index
mark and position both scalar cursors at their first mark. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace Theorem25Completion.CycleSerializerBoot
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch


theorem index_write (B : Nat) : writeTapeBit (List.replicate (B+3) false) 1 true =
    ZeroPadding.pad (B+3) (UnaryTemplate.tape 1) := by
  simp [writeTapeBit,ZeroPadding.pad,UnaryTemplate.tape,List.replicate_succ]

end Theorem25Completion.CycleSerializerBoot
