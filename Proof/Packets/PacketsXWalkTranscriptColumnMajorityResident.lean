import Proof.Packets.PacketsXWalkTranscriptColumnMajoritySource
import Proof.Packets.PacketsXMajorityCompleteBootstrapResident

/-! Source replacement for the actual retained scalar palette. No scalar
word is replaced by a shorter or unpadded logical representative. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumnMajoritySource
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open MajorityComplete.Bootstrap
noncomputable section

theorem ready_with_source (palette : Fin 10→List Bool) (C R S : Nat)
    (ps qs : List (Ring.Poly Nat)) (hRS : R+3≤S) (hC : C≤S) (hlen : ps.length=qs.length) :
    readyWith palette C R S qs=
      Function.update (readyWith palette C R S ps) 44 (OrderedPacketStep.bank C R qs) := by
  unfold readyWith
  rw [ready_work_same_length C R S ps qs hRS hC hlen]
  exact data_source palette S _ _ _

end
end Theorem25Completion.WalkTranscriptColumnMajoritySource
