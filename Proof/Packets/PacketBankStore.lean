import Proof.Packets.PacketBankPrimitives

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def store := Composition.machine countDown
  (Composition.machine appendPayload (Composition.machine seekRow
    (Composition.machine appendCount (Composition.machine seekRow countUp))))
def storeBudget (R : Nat) := 8*R+15

/-- Append a physically resident two-block packet. Both operand tapes and
all their ready cursors are retained; the bank cursor advances to its new end. -/
theorem store_run (R index : Nat) (bank payload count : List Bool)
    (hp : payload.length=R) (hc : count.length=R) :
    Step store (storeBudget R) (H bank.length 1) (A R index bank payload count)
      (H (bank++payload++count).length 1) (A R index (bank++payload++count) payload count) := by
  have first:=countDown_run R index bank.length 0 bank payload count
  have second:=appendPayload_run R index 0 bank payload count hp
  have third:=seekRow_run R index bank.length 0 (bank++payload) payload count
  have fourth:=appendCount_run R index (bank++payload) payload count hc
  have fourth' : Step appendCount (2*R+2) (H (bank.length+R) 0)
      (A R index (bank++payload) payload count)
      (H (bank.length+R) 0) (A R index (bank++payload++count) payload count) := by
    simpa only [List.length_append,hp] using fourth
  have fifth:=seekRow_run R index (bank.length+R) 0 (bank++payload++count) payload count
  have last:=countUp_run R index (bank.length+R+R) 0 (bank++payload++count) payload count
  have h:=first.seq (second.seq (third.seq (fourth'.seq (fifth.seq last))))
  have fuel : 1+1+((2*R+2)+1+((2*R+2)+1+((2*R+2)+1+((2*R+2)+1+1))))=
      storeBudget R := by unfold storeBudget;ring
  rw [fuel] at h
  simpa only [store,List.length_append,hp,hc] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
