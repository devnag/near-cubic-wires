import Proof.Packets.PhysicalBankCopy
import Proof.Rows.PhysicalDriverMoves
import Proof.Rows.MaskProductBody

/-! Actual six-tape packet bank operations. A packet occupies two R-bit
blocks, holding the padded raw mask bank and padded physical row counter. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def H (pos counterPos : Nat) : Fin 6→Nat := ![1,pos,0,counterPos,1,0]
def A (R index : Nat) (bank payload count : List Bool) : Fin 6→List Bool :=
  ![UnaryTemplate.tape R,bank,payload,count,CompareMachine.word index,[]]
def indexedSlots : Fin 4→Fin 6 := ![0,1,5,4]
def rowSlots : Fin 3→Fin 6 := ![0,1,5]
def payloadSlots : Fin 3→Fin 6 := ![0,1,2]
def countSlots : Fin 3→Fin 6 := ![0,1,3]
def appendPayloadSlots : Fin 3→Fin 6 := ![0,2,1]
def appendCountSlots : Fin 3→Fin 6 := ![0,3,1]
def counterSlot : Fin 1→Fin 6 := ![3]
def seek := RecoveryFocus.machine indexedSlots MaskSeek.machine
def back := RecoveryFocus.machine indexedSlots MaskBack.machine
def seekRow := RecoveryFocus.machine rowSlots MaskSeek.body
def backRow := RecoveryFocus.machine rowSlots MaskBack.body
def copyPayload := RecoveryFocus.machine payloadSlots PhysicalBankCopy.machine
def copyCount := RecoveryFocus.machine countSlots PhysicalBankCopy.machine
def appendPayload := RecoveryFocus.machine appendPayloadSlots PhysicalBankCopy.machine
def appendCount := RecoveryFocus.machine appendCountSlots PhysicalBankCopy.machine
def countDown := RecoveryFocus.machine counterSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def countUp := RecoveryFocus.machine counterSlot (Completion.PhysicalDriverMoves.machine 1 .right)

theorem seek_run (R index pos cp : Nat) (bank payload count : List Bool) :
    Step seek (index*(2*R+5)+3) (H pos cp) (A R index bank payload count)
      (H (pos+index*R) cp) (A R index bank payload count) := by
  obtain ⟨r,rr,rf,_⟩:=MaskSeek.seek_run R index pos bank []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h indexedSlots (by decide)
    (H pos cp) (H (pos+index*R) cp) (A R index bank payload count) (A R index bank payload count)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem back_run (R index pos cp : Nat) (bank payload count : List Bool) :
    Step back (index*(2*R+5)+3) (H (pos+index*R) cp) (A R index bank payload count)
      (H pos cp) (A R index bank payload count) := by
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run R index pos bank []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h indexedSlots (by decide)
    (H (pos+index*R) cp) (H pos cp) (A R index bank payload count) (A R index bank payload count)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem seekRow_run (R index pos cp : Nat) (bank payload count : List Bool) :
    Step seekRow (2*R+2) (H pos cp) (A R index bank payload count)
      (H (pos+R) cp) (A R index bank payload count) := by
  obtain ⟨r,rr,rf,_⟩:=MaskSeek.row_run R pos bank []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h rowSlots (by decide)
    (H pos cp) (H (pos+R) cp) (A R index bank payload count) (A R index bank payload count)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem backRow_run (R index pos cp : Nat) (bank payload count : List Bool) :
    Step backRow (2*R+2) (H (pos+R) cp) (A R index bank payload count)
      (H pos cp) (A R index bank payload count) := by
  obtain ⟨r,rr,rf,_⟩:=MaskBack.row_run R pos bank []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  exact PhysicalFocusBoundary.focus h rowSlots (by decide)
    (H (pos+R) cp) (H pos cp) (A R index bank payload count) (A R index bank payload count)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))

theorem countDown_run (R index pos cp : Nat) (bank payload count : List Bool) :
    Step countDown 1 (H pos (cp+1)) (A R index bank payload count)
      (H pos cp) (A R index bank payload count) := by
  have h:=Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>cp+1) (fun _=>count)
  exact PhysicalFocusBoundary.focus h counterSlot (by decide)
    (H pos (cp+1)) (H pos cp) (A R index bank payload count) (A R index bank payload count)
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl))

theorem countUp_run (R index pos cp : Nat) (bank payload count : List Bool) :
    Step countUp 1 (H pos cp) (A R index bank payload count)
      (H pos (cp+1)) (A R index bank payload count) := by
  have h:=Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>cp) (fun _=>count)
  exact PhysicalFocusBoundary.focus h counterSlot (by decide)
    (H pos cp) (H pos (cp+1)) (A R index bank payload count) (A R index bank payload count)
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
    (by intro i;fin_cases i;rfl) (by intro i;fin_cases i;rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl))

theorem copyPayload_run (R index cp : Nat) (pre payload post old count : List Bool)
    (hp : payload.length=R) (ho : old.length=R) :
    Step copyPayload (2*R+2) (H pre.length cp) (A R index (pre++payload++post) old count)
      (H pre.length cp) (A R index (pre++payload++post) payload count) := by
  have h:=PhysicalBankCopy.copy_step_boundary payload old (ho.trans hp.symm) pre post [] []
  rw [hp] at h
  refine PhysicalFocusBoundary.focus h payloadSlots (by decide)
    (H pre.length cp) (H pre.length cp)
    (A R index (pre++payload++post) old count) (A R index (pre++payload++post) payload count)
    ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [payloadSlots,A,PhysicalBankCopy.cfg]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [payloadSlots,A,PhysicalBankCopy.cfg]
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl)

theorem copyCount_run (R index : Nat) (pre count post payload old : List Bool)
    (hc : count.length=R) (ho : old.length=R) :
    Step copyCount (2*R+2) (H pre.length 0) (A R index (pre++count++post) payload old)
      (H pre.length 0) (A R index (pre++count++post) payload count) := by
  have h:=PhysicalBankCopy.copy_step_boundary count old (ho.trans hc.symm) pre post [] []
  rw [hc] at h
  refine PhysicalFocusBoundary.focus h countSlots (by decide)
    (H pre.length 0) (H pre.length 0)
    (A R index (pre++count++post) payload old) (A R index (pre++count++post) payload count)
    ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [countSlots,A,PhysicalBankCopy.cfg]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [countSlots,A,PhysicalBankCopy.cfg]
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl)

theorem appendPayload_run (R index cp : Nat) (bank payload count : List Bool) (hp : payload.length=R) :
    Step appendPayload (2*R+2) (H bank.length cp) (A R index bank payload count)
      (H bank.length cp) (A R index (bank++payload) payload count) := by
  obtain ⟨r,rr,rf,_⟩:=PhysicalBankCopy.append_run payload [] [] bank
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  rw [hp] at h
  refine PhysicalFocusBoundary.focus h appendPayloadSlots (by decide)
    (H bank.length cp) (H bank.length cp)
    (A R index bank payload count) (A R index (bank++payload) payload count) ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [appendPayloadSlots,A]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [appendPayloadSlots,A,PhysicalBankCopy.cfg]
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl)

theorem appendCount_run (R index : Nat) (bank payload count : List Bool) (hc : count.length=R) :
    Step appendCount (2*R+2) (H bank.length 0) (A R index bank payload count)
      (H bank.length 0) (A R index (bank++count) payload count) := by
  obtain ⟨r,rr,rf,_⟩:=PhysicalBankCopy.append_run count [] [] bank
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  rw [hc] at h
  refine PhysicalFocusBoundary.focus h appendCountSlots (by decide)
    (H bank.length 0) (H bank.length 0)
    (A R index bank payload count) (A R index (bank++count) payload count) ?_ ?_ ?_ ?_ ?_
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [appendCountSlots,A]
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> simp [appendCountSlots,A,PhysicalBankCopy.cfg]
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 2 rfl)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketBank
