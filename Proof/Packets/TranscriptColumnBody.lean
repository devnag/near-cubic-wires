import Proof.Packets.TranscriptColumnRead

/-! A physical time-column step. The resident row-width driver advances the
transcript cursor by exactly one complete row after copying its selected
packet to the output column. No computed index word is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def H (sourcePos targetPos : Nat) : Fin 7 → Nat := ![1,sourcePos,0,1,1,0,targetPos]
def A (R N : Nat) (source payload count target : List Bool) : Fin 7 → List Bool :=
  ![UnaryTemplate.tape R,source,payload,count,CompareMachine.word N,[],target]
def sourceSlots : Fin 6 → Fin 7 := ![0,1,2,3,4,5]
def targetSlots : Fin 6 → Fin 7 := ![0,6,2,3,4,5]
def readCurrent := RecoveryFocus.machine sourceSlots read
def appendCurrent := RecoveryFocus.machine targetSlots PacketBank.store
def advance := RecoveryFocus.machine sourceSlots PacketBank.seek
def body := Composition.machine readCurrent
  (Composition.machine appendCurrent (Composition.machine advance advance))
def bodyBudget (R N : Nat) := 16*R+2*N*(2*R+5)+39

theorem read_current (R N pos : Nat) (pre payload count post oldPayload oldCount target : List Bool)
    (hp : payload.length=R) (hc : count.length=R)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step readCurrent (readBudget R) (H pre.length pos)
      (A R N (pre++payload++count++post) oldPayload oldCount target)
      (H pre.length pos) (A R N (pre++payload++count++post) payload count target) := by
  apply PhysicalFocusBoundary.focus (read_run R N pre payload count post oldPayload oldCount hp hc hop hoc)
    sourceSlots (by decide) (H pre.length pos) (H pre.length pos) _ _
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl) | exact False.elim (away 3 rfl)

private theorem target_heads (pos index : Nat) :
    ∀i,PacketBank.H index 1 i=H pos index (targetSlots i) := by
  intro i;fin_cases i <;> rfl

private theorem target_tapes (R N : Nat) (source payload count target : List Bool) :
    ∀i,PacketBank.A R N target payload count i=A R N source payload count target (targetSlots i) := by
  intro i;fin_cases i <;> rfl

private theorem target_outside (pos oldPos newPos : Nat)
    (R N : Nat) (source payload count oldTarget newTarget : List Bool) :
    ∀i,(∀j,targetSlots j≠i)→
      H pos oldPos i=H pos newPos i ∧
      A R N source payload count oldTarget i=A R N source payload count newTarget i := by
  intro i away
  have hi : i≠6 := by intro he;subst i;exact away 1 rfl
  fin_cases i <;> simp_all [H,A]

theorem focus_target {states fuel : Nat} (program : Machine 6 states)
    (R N pos : Nat) (source payload count target result : List Bool)
    (small : Step program fuel (PacketBank.H target.length 1)
      (PacketBank.A R N target payload count) (PacketBank.H result.length 1)
      (PacketBank.A R N result payload count)) :
    Step (RecoveryFocus.machine targetSlots program) fuel (H pos target.length)
      (A R N source payload count target) (H pos result.length)
      (A R N source payload count result) := by
  exact PhysicalFocusBoundary.focus small targetSlots (by decide)
    (H pos target.length) (H pos result.length)
    (A R N source payload count target) (A R N source payload count result)
    (target_heads pos target.length) (target_tapes R N source payload count target)
    (target_heads pos result.length) (target_tapes R N source payload count result)
    (target_outside pos target.length result.length R N source payload count target result)

theorem append_current (R N pos : Nat) (source payload count target : List Bool)
    (hp : payload.length=R) (hc : count.length=R) :
    Step appendCurrent (PacketBank.storeBudget R) (H pos target.length)
      (A R N source payload count target)
      (H pos (target++payload++count).length)
      (A R N source payload count (target++payload++count)) := by
  exact focus_target PacketBank.store R N pos source payload count target
    (target++payload++count) (PacketBank.store_run R N target payload count hp hc)

theorem advance_run (R N pos targetPos : Nat) (source payload count target : List Bool) :
    Step advance (N*(2*R+5)+3) (H pos targetPos) (A R N source payload count target)
      (H (pos+N*R) targetPos) (A R N source payload count target) := by
  apply PhysicalFocusBoundary.focus (PacketBank.seek_run R N pos 1 source payload count)
    sourceSlots (by decide) (H pos targetPos) (H (pos+N*R) targetPos) _ _
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

/-- Copy the selected packet and move to the same coordinate in the next
row, charging both width-counted scans to the actual unary row driver. -/
theorem body_run (R N : Nat) (pre post target : List Bool) (P old : PacketVector.Packet)
    (hP : PacketVector.Fits R P) (ho : PacketVector.Fits R old) :
    Step body (bodyBudget R N) (H pre.length target.length)
      (A R N (pre++PacketVector.entry R P++post)
        (PacketVector.payload R old) (PacketVector.count R old) target)
      (H (pre.length+N*(2*R)) (target++PacketVector.entry R P).length)
      (A R N (pre++PacketVector.entry R P++post)
        (PacketVector.payload R P) (PacketVector.count R P) (target++PacketVector.entry R P)) := by
  let source := pre++PacketVector.entry R P++post
  let payload := PacketVector.payload R P
  let count := PacketVector.count R P
  have first := read_current R N target.length pre payload count post
    (PacketVector.payload R old) (PacketVector.count R old) target
    (PacketVector.payload_length hP) (PacketVector.count_length hP)
    (PacketVector.payload_length ho) (PacketVector.count_length ho)
  have first' : Step readCurrent (readBudget R) (H pre.length target.length)
      (A R N source (PacketVector.payload R old) (PacketVector.count R old) target)
      (H pre.length target.length) (A R N source payload count target) := by
    simpa only [source,PacketVector.entry,payload,count,List.append_assoc] using first
  have second := append_current R N pre.length source payload count target
    (PacketVector.payload_length hP) (PacketVector.count_length hP)
  have third := advance_run R N pre.length (target++payload++count).length source payload count (target++payload++count)
  have fourth := advance_run R N (pre.length+N*R) (target++payload++count).length source payload count (target++payload++count)
  have whole := first'.seq (second.seq (third.seq fourth))
  have cost : readBudget R+1+(PacketBank.storeBudget R+1+((N*(2*R+5)+3)+1+(N*(2*R+5)+3)))=
      bodyBudget R N := by unfold readBudget PacketBank.storeBudget bodyBudget;ring
  have pos : pre.length+N*R+N*R=pre.length+N*(2*R) := by ring
  simpa only [body,cost,pos,source,payload,count,PacketVector.entry,List.append_assoc] using whole

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
