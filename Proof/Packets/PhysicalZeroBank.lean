import Proof.Packets.MaskConstant
import Proof.Packets.PhysicalRepeatStep

/-! Dense packet-table allocation by actual writes. Given only physical R
and N drivers, write N all-false two-R-bit entries into an empty bank and
return its cursor. No prefilled table is part of the input. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def H (pos : Nat) : Fin 3→Nat := ![1,pos,0]
def A (R : Nat) (bank : List Bool) : Fin 3→List Bool := ![UnaryTemplate.tape R,bank,[]]
def zeroSlots : Fin 2→Fin 3 := ![0,1]
def zero := RecoveryFocus.machine zeroSlots MaskConstant.maskMachine
def chunk := Composition.machine zero MaskSeek.body
def packet := Composition.machine chunk chunk
def loop := RepeatMachine.machine packet (fun _ _=>true)
def heads (pos : Nat) : Fin 4→Nat := ![1,pos,0,1]
def tapes (R N : Nat) (bank : List Bool) : Fin 4→List Bool :=
  ![UnaryTemplate.tape R,bank,[],CompareMachine.word N]
def machine := Composition.machine loop (Composition.machine MaskBack.machine MaskBack.machine)
def budget (R N : Nat) := N*(12*R+24)+11

theorem chunk_run (R : Nat) (bank : List Bool) :
    Step chunk (4*R+5) (H bank.length) (A R bank)
      (H (bank.length+R)) (A R (bank++List.replicate R false)) := by
  obtain ⟨r,rr,rf,_⟩:=MaskConstant.mask_run R bank
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have first:=PhysicalFocusBoundary.focus h zeroSlots (by decide)
    (H bank.length) (H bank.length) (A R bank) (A R (bank++List.replicate R false))
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 1 rfl))
  obtain ⟨r,rr,rf,_⟩:=MaskSeek.row_run R bank.length (bank++List.replicate R false) []
  have second:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have all:=first.seq second
  have fuel : (2*R+2)+1+(2*R+2)=4*R+5 := by omega
  rw [fuel] at all
  exact all

theorem packet_run (R : Nat) (bank : List Bool) :
    Step packet (8*R+11) (H bank.length) (A R bank)
      (H (bank.length+2*R)) (A R (bank++List.replicate (2*R) false)) := by
  have first:=chunk_run R bank
  have second:=chunk_run R (bank++List.replicate R false)
  simp only [List.length_append,List.length_replicate] at second
  have h:=first.seq second
  have fuel : (4*R+5)+1+(4*R+5)=8*R+11 := by omega
  rw [fuel] at h
  have zeros : List.replicate R false++List.replicate R false=List.replicate (2*R) false := by
    rw [←List.replicate_add,show R+R=2*R by omega]
  have pos : bank.length+R+R=bank.length+2*R := by omega
  simpa only [packet,pos,List.append_assoc,zeros] using h

theorem loop_run (R N : Nat) :
    Step loop (N*(8*R+14)+3) (heads 0) (tapes R N [])
      (heads (N*(2*R))) (tapes R N (List.replicate (N*(2*R)) false)) := by
  have body (i : Nat) (_ : i<N) : Step packet (8*R+11)
      (H (i*(2*R))) (A R (List.replicate (i*(2*R)) false))
      (H ((i+1)*(2*R))) (A R (List.replicate ((i+1)*(2*R)) false)) := by
    have h:=packet_run R (List.replicate (i*(2*R)) false)
    have he : i*(2*R)+2*R=(i+1)*(2*R) := by ring
    simpa only [List.length_replicate,←List.replicate_add,he] using h
  have h:=PhysicalRepeatStep.run packet N (8*R+11)
    (fun i=>H (i*(2*R))) (fun i=>A R (List.replicate (i*(2*R)) false)) body
  have fuel : N*((8*R+11)+3)+3=N*(8*R+14)+3 := by ring
  rw [fuel] at h
  simp only [Nat.zero_mul,List.replicate_zero] at h
  convert h using 1
  all_goals first | rfl | (funext i;fin_cases i <;>rfl)

theorem back_run (R N pos : Nat) (bank : List Bool) :
    Step MaskBack.machine (N*(2*R+5)+3) (heads (pos+N*R)) (tapes R N bank)
      (heads pos) (tapes R N bank) := by
  obtain ⟨r,rr,rf,_⟩:=MaskBack.back_run R N pos bank []
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  convert h using 1
  all_goals first | rfl | (funext i;fin_cases i <;>rfl)

theorem run (R N : Nat) :
    Step machine (budget R N) (heads 0) (tapes R N [])
      (heads 0) (tapes R N (List.replicate (N*(2*R)) false)) := by
  have first:=loop_run R N
  have second:=back_run R N (N*R) (List.replicate (N*(2*R)) false)
  have third:=back_run R N 0 (List.replicate (N*(2*R)) false)
  have he : N*R+N*R=N*(2*R) := by ring
  rw [he] at second
  simp only [Nat.zero_add] at third
  have h:=first.seq (second.seq third)
  have fuel : (N*(8*R+14)+3)+1+((N*(2*R+5)+3)+1+(N*(2*R+5)+3))=budget R N := by
    unfold budget;ring
  rw [fuel] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
