import Proof.Packets.PacketBankLookup
import Proof.Packets.PacketBankStore

/-! Paid cursor adapters for the reusable arithmetic arena, whose operand
payload and row-count tapes both have cursor zero at the public boundary. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def lookupZero := Composition.machine countUp (Composition.machine lookup countDown)
def storeZero := Composition.machine countUp (Composition.machine store countDown)

theorem lookup_zero_run (R index : Nat) (pre payload count post oldPayload oldCount : List Bool)
    (hpre : pre.length=2*index*R) (hp : payload.length=R) (hc : count.length=R)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step lookupZero (lookupBudget R index+4)
      (H 0 0) (A R index (pre++payload++count++post) oldPayload oldCount)
      (H 0 0) (A R index (pre++payload++count++post) payload count) := by
  have first:=countUp_run R index 0 0 (pre++payload++count++post) oldPayload oldCount
  have second:=lookup_run R index pre payload count post oldPayload oldCount hpre hp hc hop hoc
  have third:=countDown_run R index 0 0 (pre++payload++count++post) payload count
  have h:=first.seq (second.seq third)
  have fuel : 1+1+(lookupBudget R index+1+1)=lookupBudget R index+4 := by omega
  rw [fuel] at h
  exact h

theorem store_zero_run (R index : Nat) (bank payload count : List Bool)
    (hp : payload.length=R) (hc : count.length=R) :
    Step storeZero (storeBudget R+4) (H bank.length 0) (A R index bank payload count)
      (H (bank++payload++count).length 0) (A R index (bank++payload++count) payload count) := by
  have first:=countUp_run R index bank.length 0 bank payload count
  have second:=store_run R index bank payload count hp hc
  have third:=countDown_run R index (bank++payload++count).length 0
    (bank++payload++count) payload count
  have h:=first.seq (second.seq third)
  have fuel : 1+1+(storeBudget R+1+1)=storeBudget R+4 := by omega
  rw [fuel] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
