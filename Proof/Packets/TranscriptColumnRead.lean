import Proof.Packets.PacketVector

/-! Copy the packet at the current transcript cursor while restoring that
cursor. All movement and both block copies are performed by the machine. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
noncomputable section

def read := Composition.machine PacketBank.countDown
  (Composition.machine PacketBank.copyPayload (Composition.machine PacketBank.seekRow
    (Composition.machine PacketBank.copyCount (Composition.machine PacketBank.backRow
      PacketBank.countUp))))
def readBudget (R : Nat) := 8*R+15

theorem read_run (R N : Nat) (pre payload count post oldPayload oldCount : List Bool)
    (hp : payload.length=R) (hc : count.length=R)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step read (readBudget R)
      (PacketBank.H pre.length 1)
      (PacketBank.A R N (pre++payload++count++post) oldPayload oldCount)
      (PacketBank.H pre.length 1)
      (PacketBank.A R N (pre++payload++count++post) payload count) := by
  let source := pre++payload++count++post
  have first := PacketBank.countDown_run R N pre.length 0 source oldPayload oldCount
  have second := PacketBank.copyPayload_run R N 0 pre payload (count++post)
    oldPayload oldCount hp hop
  have second' : Step PacketBank.copyPayload (2*R+2)
      (PacketBank.H pre.length 0) (PacketBank.A R N source oldPayload oldCount)
      (PacketBank.H pre.length 0) (PacketBank.A R N source payload oldCount) := by
    simpa only [source,List.append_assoc] using second
  have third := PacketBank.seekRow_run R N pre.length 0 source payload oldCount
  have fourth := PacketBank.copyCount_run R N (pre++payload) count post payload oldCount hc hoc
  have fourth' : Step PacketBank.copyCount (2*R+2)
      (PacketBank.H (pre.length+R) 0) (PacketBank.A R N source payload oldCount)
      (PacketBank.H (pre.length+R) 0) (PacketBank.A R N source payload count) := by
    simpa only [source,List.length_append,hp,List.append_assoc] using fourth
  have fifth := PacketBank.backRow_run R N pre.length 0 source payload count
  have last := PacketBank.countUp_run R N pre.length 0 source payload count
  have whole := first.seq (second'.seq (third.seq (fourth'.seq (fifth.seq last))))
  have fuel : 1+1+((2*R+2)+1+((2*R+2)+1+((2*R+2)+1+((2*R+2)+1+1))))=
      readBudget R := by unfold readBudget;ring
  rw [fuel] at whole
  exact whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
