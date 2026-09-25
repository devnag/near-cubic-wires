import Proof.Packets.TranscriptColumnLayout

/-! Restore a column extractor's source head by executing the row-width
backward scan once per physically counted time. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def retreat := RecoveryFocus.machine sourceSlots PacketBank.back
def retreatRow := Composition.machine retreat retreat
def retreatBudget (R N : Nat) := 2*N*(2*R+5)+7
def rewindRows := RepeatMachine.machine retreatRow (fun _ _=>true)
def rewindBudget (R N T : Nat) := T*(retreatBudget R N+3)+3

theorem retreat_run (R N pos targetPos : Nat) (source payload count target : List Bool) :
    Step retreat (N*(2*R+5)+3) (H (pos+N*R) targetPos) (A R N source payload count target)
      (H pos targetPos) (A R N source payload count target) := by
  apply PhysicalFocusBoundary.focus (PacketBank.back_run R N pos 1 source payload count)
    sourceSlots (by decide) (H (pos+N*R) targetPos) (H pos targetPos) _ _
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i;fin_cases i <;> rfl
  · intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl)

theorem retreat_row (R N pos targetPos : Nat) (source payload count target : List Bool) :
    Step retreatRow (retreatBudget R N) (H (pos+N*(2*R)) targetPos)
      (A R N source payload count target) (H pos targetPos) (A R N source payload count target) := by
  have one := retreat_run R N (pos+N*R) targetPos source payload count target
  have two := retreat_run R N pos targetPos source payload count target
  have h := one.seq two
  have posEq : pos+N*R+N*R=pos+N*(2*R) := by ring
  have fuel : (N*(2*R+5)+3)+1+(N*(2*R+5)+3)=retreatBudget R N := by unfold retreatBudget;ring
  simpa only [retreatRow,posEq,fuel] using h

theorem rewind_rows (R N T offset targetPos : Nat) (source payload count target : List Bool) :
    Step rewindRows (rewindBudget R N T)
      (Fin.addCases (H (offset+T*(N*(2*R))) targetPos) (fun _ : Fin 1=>1))
      (Fin.addCases (A R N source payload count target) (fun _ : Fin 1=>CompareMachine.word T))
      (Fin.addCases (H offset targetPos) (fun _ : Fin 1=>1))
      (Fin.addCases (A R N source payload count target) (fun _ : Fin 1=>CompareMachine.word T)) := by
  let hs := fun i=>H (offset+(T-i)*(N*(2*R))) targetPos
  let tapes := fun _ : Nat=>A R N source payload count target
  have steps (i : Nat) (hi : i<T) :
      Step retreatRow (retreatBudget R N) (hs i) (tapes i) (hs (i+1)) (tapes (i+1)) := by
    have h := retreat_row R N (offset+(T-(i+1))*(N*(2*R))) targetPos source payload count target
    have sub : T-i=T-(i+1)+1 := by omega
    have posEq : offset+(T-(i+1))*(N*(2*R))+N*(2*R)=offset+(T-i)*(N*(2*R)) := by
      rw [sub];ring
    simpa only [hs,tapes,posEq] using h
  have h := PhysicalRepeatStep.run retreatRow T (retreatBudget R N) hs tapes steps
  simpa only [rewindRows,rewindBudget,hs,tapes,Nat.sub_zero,Nat.sub_self,Nat.zero_mul,Nat.add_zero] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.TranscriptColumn
