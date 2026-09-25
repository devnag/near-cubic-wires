import Proof.Packets.PacketBankLookup

/-! Actual indexed replacement of one resident two-R-bit packet. Source
operands and all cursors are retained; every other bank entry is unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem writePayload_run (R index cp : Nat) (pre old post payload count : List Bool)
    (hp : payload.length=R) (ho : old.length=R) :
    Step appendPayload (2*R+2) (H pre.length cp) (A R index (pre++old++post) payload count)
      (H pre.length cp) (A R index (pre++payload++post) payload count) := by
  have h:=PhysicalBankCopy.copy_step_boundary payload old (ho.trans hp.symm) [] [] pre post
  rw [hp] at h
  apply PhysicalFocusBoundary.focus h appendPayloadSlots (by decide)
    (H pre.length cp) (H pre.length cp)
    (A R index (pre++old++post) payload count) (A R index (pre++payload++post) payload count)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [appendPayloadSlots,A,PhysicalBankCopy.cfg]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [appendPayloadSlots,A,PhysicalBankCopy.cfg]
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl)

theorem writeCount_run (R index : Nat) (pre old post payload count : List Bool)
    (hc : count.length=R) (ho : old.length=R) :
    Step appendCount (2*R+2) (H pre.length 0) (A R index (pre++old++post) payload count)
      (H pre.length 0) (A R index (pre++count++post) payload count) := by
  have h:=PhysicalBankCopy.copy_step_boundary count old (ho.trans hc.symm) [] [] pre post
  rw [hc] at h
  apply PhysicalFocusBoundary.focus h appendCountSlots (by decide)
    (H pre.length 0) (H pre.length 0)
    (A R index (pre++old++post) payload count) (A R index (pre++count++post) payload count)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [appendCountSlots,A,PhysicalBankCopy.cfg]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [appendCountSlots,A,PhysicalBankCopy.cfg]
  · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl)

def storeSelected := Composition.machine countDown
  (Composition.machine seek (Composition.machine seek
    (Composition.machine appendPayload (Composition.machine seekRow
      (Composition.machine appendCount (Composition.machine backRow
        (Composition.machine back (Composition.machine back countUp))))))))

theorem store_selected_run (R index : Nat) (pre oldPayload oldCount post payload count : List Bool)
    (hpre : pre.length=2*index*R) (hp : payload.length=R) (hc : count.length=R)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step storeSelected (lookupBudget R index)
      (H 0 1) (A R index (pre++oldPayload++oldCount++post) payload count)
      (H 0 1) (A R index (pre++payload++count++post) payload count) := by
  have hpre' : pre.length=index*R+index*R := by rw [hpre];ring
  let before:=pre++oldPayload++oldCount++post
  let middle:=pre++payload++oldCount++post
  let after:=pre++payload++count++post
  have first:=countDown_run R index 0 0 before payload count
  have second:=seek_run R index 0 0 before payload count
  have third:=seek_run R index (index*R) 0 before payload count
  have fourth:=writePayload_run R index 0 pre oldPayload (oldCount++post) payload count hp hop
  have fourth' : Step appendPayload (2*R+2) (H (index*R+index*R) 0)
      (A R index before payload count) (H (index*R+index*R) 0)
      (A R index middle payload count) := by
    simpa only [before,middle,hpre',List.append_assoc] using fourth
  have fifth:=seekRow_run R index (index*R+index*R) 0 middle payload count
  have sixth:=writeCount_run R index (pre++payload) oldCount post payload count hc hoc
  have sixth' : Step appendCount (2*R+2) (H (index*R+index*R+R) 0)
      (A R index middle payload count) (H (index*R+index*R+R) 0)
      (A R index after payload count) := by
    simpa only [middle,after,List.length_append,hpre',hp] using sixth
  have seventh:=backRow_run R index (index*R+index*R) 0 after payload count
  have eighth:=back_run R index (index*R) 0 after payload count
  have ninth:=back_run R index 0 0 after payload count
  have last:=countUp_run R index 0 0 after payload count
  simp only [Nat.zero_add] at second ninth
  have h:=first.seq (second.seq (third.seq (fourth'.seq (fifth.seq
    (sixth'.seq (seventh.seq (eighth.seq (ninth.seq last))))))))
  have fuel : 1+1+((index*(2*R+5)+3)+1+((index*(2*R+5)+3)+1+((2*R+2)+1+
      ((2*R+2)+1+((2*R+2)+1+((2*R+2)+1+((index*(2*R+5)+3)+1+
        ((index*(2*R+5)+3)+1+1))))))))=lookupBudget R index := by unfold lookupBudget;ring
  rw [fuel] at h
  exact h

def storeSelectedZero := Composition.machine countUp (Composition.machine storeSelected countDown)

theorem store_selected_zero_run (R index : Nat) (pre oldPayload oldCount post payload count : List Bool)
    (hpre : pre.length=2*index*R) (hp : payload.length=R) (hc : count.length=R)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step storeSelectedZero (lookupBudget R index+4)
      (H 0 0) (A R index (pre++oldPayload++oldCount++post) payload count)
      (H 0 0) (A R index (pre++payload++count++post) payload count) := by
  have first:=countUp_run R index 0 0 (pre++oldPayload++oldCount++post) payload count
  have second:=store_selected_run R index pre oldPayload oldCount post payload count hpre hp hc hop hoc
  have third:=countDown_run R index 0 0 (pre++payload++count++post) payload count
  have h:=first.seq (second.seq third)
  have fuel : 1+1+(lookupBudget R index+1+1)=lookupBudget R index+4 := by omega
  rw [fuel] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
