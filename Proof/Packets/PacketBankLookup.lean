import Proof.Packets.PacketBankPrimitives

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def lookup := Composition.machine countDown
  (Composition.machine seek (Composition.machine seek
    (Composition.machine copyPayload (Composition.machine seekRow
      (Composition.machine copyCount (Composition.machine backRow
        (Composition.machine back (Composition.machine back countUp))))))))
def lookupBudget (R index : Nat) := 4*(index*(2*R+5)+3)+8*R+19

/-- Indexed lookup reads exactly the selected two-block packet and restores
its resident bank cursor and physical child-index driver. Existing operand
words are overwritten; the physical counter cursor returns to head one. -/
theorem lookup_run (R index : Nat) (pre payload count post oldPayload oldCount : List Bool)
    (hpre : pre.length=2*index*R) (hp : payload.length=R) (hc : count.length=R)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step lookup (lookupBudget R index)
      (H 0 1) (A R index (pre++payload++count++post) oldPayload oldCount)
      (H 0 1) (A R index (pre++payload++count++post) payload count) := by
  have hpre' : pre.length=index*R+index*R := by rw [hpre];ring
  let bank:=pre++payload++count++post
  have first:=countDown_run R index 0 0 bank oldPayload oldCount
  have second:=seek_run R index 0 0 bank oldPayload oldCount
  have third:=seek_run R index (index*R) 0 bank oldPayload oldCount
  have fourth:=copyPayload_run R index 0 pre payload (count++post) oldPayload oldCount hp hop
  have fourth' : Step copyPayload (2*R+2) (H (index*R+index*R) 0)
      (A R index bank oldPayload oldCount) (H (index*R+index*R) 0)
      (A R index bank payload oldCount) := by
    simpa only [bank,hpre',List.append_assoc] using fourth
  have fifth:=seekRow_run R index (index*R+index*R) 0 bank payload oldCount
  have sixth:=copyCount_run R index (pre++payload) count post payload oldCount hc hoc
  have sixth' : Step copyCount (2*R+2) (H (index*R+index*R+R) 0)
      (A R index bank payload oldCount) (H (index*R+index*R+R) 0)
      (A R index bank payload count) := by
    simpa only [bank,List.length_append,hpre',hp] using sixth
  have seventh:=backRow_run R index (index*R+index*R) 0 bank payload count
  have eighth:=back_run R index (index*R) 0 bank payload count
  have ninth:=back_run R index 0 0 bank payload count
  have last:=countUp_run R index 0 0 bank payload count
  simp only [Nat.zero_add] at second ninth
  have h:=first.seq (second.seq (third.seq (fourth'.seq (fifth.seq
    (sixth'.seq (seventh.seq (eighth.seq (ninth.seq last))))))))
  have fuel : 1+1+((index*(2*R+5)+3)+1+((index*(2*R+5)+3)+1+((2*R+2)+1+
      ((2*R+2)+1+((2*R+2)+1+((2*R+2)+1+((index*(2*R+5)+3)+1+
        ((index*(2*R+5)+3)+1+1))))))))=lookupBudget R index := by unfold lookupBudget;ring
  rw [fuel] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
