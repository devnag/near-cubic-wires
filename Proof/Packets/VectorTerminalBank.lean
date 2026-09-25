import Proof.Packets.PhysicalZeroBank
import Proof.Packets.PacketBankWrite
import Proof.Packets.PacketVector

/-! Actual terminal-vector initialization: allocate every packet, generate
one from the runtime mask width, and overwrite the first packet. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminalBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] PhysicalZeroBank.machine MaskConstant.oneMachine PacketBank.storeSelected

def H (cp : Nat) (i : Fin 8) : Nat := if i=6 then cp else (![1,0,0,1,1,0,0,1] : Fin 8→Nat) i
def A (R C M : Nat) (bank payload count : List Bool) (i : Fin 8) : List Bool :=
  if i=1 then bank else if i=5 then payload else if i=6 then count else
    (![UnaryTemplate.tape R,[],[],CompareMachine.word (M+1),UnaryTemplate.tape C,
      [],[],CompareMachine.word 0] : Fin 8→List Bool) i
def allocateSlots : Fin 4→Fin 8 := ![0,1,2,3]
def oneSlots : Fin 1→Fin 8 := ![6]
def writeSlots : Fin 6→Fin 8 := ![0,1,5,6,7,2]
def allocate := RecoveryFocus.machine allocateSlots PhysicalZeroBank.machine
def one := RecoveryFocus.machine oneSlots (MaskConstant.countMachine true)
def write := RecoveryFocus.machine writeSlots PacketBank.storeSelected
def machine := Composition.machine allocate (Composition.machine one write)
def budget (R _C M : Nat) := PhysicalZeroBank.budget R (M+1)+PacketBank.lookupBudget R 0+4

set_option maxHeartbeats 50000 in
theorem allocate_run (R C M : Nat) (payload count : List Bool) :
    Step allocate (PhysicalZeroBank.budget R (M+1))
      (H 0) (A R C M [] payload count)
      (H 0) (A R C M (List.replicate ((M+1)*(2*R)) false) payload count) := by
  exact PhysicalFocusBoundary.focus (PhysicalZeroBank.run R (M+1)) allocateSlots (by decide)
    (H 0) (H 0) _ _
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i away
        have hi:i≠1 := by intro he;exact away 1 he.symm
        exact ⟨rfl,by simp only [A,if_neg hi]⟩)


theorem one_run (R C M : Nat) (bank : List Bool) (hC : C≤R) :
    Step one 2 (H 0)
      (A R C M bank (List.replicate R false) (List.replicate R false))
      (H 1) (A R C M bank (ZeroPadding.pad R (List.replicate C false))
        (ZeroPadding.pad R (CompareMachine.word 1))) := by
  have hz : ZeroPadding.pad R (List.replicate C false)=List.replicate R false := by
    simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hC]
  rw [hz]
  obtain ⟨r,rr,rf,_⟩:=MaskConstant.count_run true
  have localRun:=(Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).pad (fun _=>R)
  apply PhysicalFocusBoundary.focus localRun oneSlots (by decide) (H 0) (H 1) _ _
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;simp [oneSlots,A,MaskConstant.countCfg,ZeroPadding.pad]
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    have h6:i≠6 := by intro he;exact away 0 he.symm
    exact ⟨by simp only [H,if_neg h6],by simp only [A,if_neg h6]⟩


theorem write_run (R C M : Nat) (payload count : List Bool)
    (hp : payload.length=R) (hc : count.length=R) :
    Step write (PacketBank.lookupBudget R 0)
      (H 1) (A R C M (List.replicate ((M+1)*(2*R)) false) payload count)
      (H 1) (A R C M (payload++count++List.replicate (M*(2*R)) false) payload count) := by
  have he : List.replicate ((M+1)*(2*R)) false=
      []++List.replicate R false++List.replicate R false++List.replicate (M*(2*R)) false := by
    simp only [List.nil_append,←List.replicate_add]
    congr 1;ring
  rw [he]
  have localRun:=PacketBank.store_selected_run R 0 [] (List.replicate R false)
    (List.replicate R false) (List.replicate (M*(2*R)) false) payload count
    (by simp) hp hc (by simp) (by simp)
  exact PhysicalFocusBoundary.focus localRun writeSlots (by decide) (H 1) (H 1) _ _
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i away
        have hi:i≠1 := by intro he;exact away 1 he.symm
        exact ⟨rfl,by simp only [A,if_neg hi]⟩)

def result (R C M : Nat) : List Bool :=
  ZeroPadding.pad R (List.replicate C false)++ZeroPadding.pad R (CompareMachine.word 1)++
    List.replicate (M*(2*R)) false


theorem run (R C M : Nat) (hC : C≤R) (hR : 2≤R) :
    Step machine (budget R C M) (H 0)
      (A R C M [] (List.replicate R false) (List.replicate R false))
      (H 1) (A R C M (result R C M) (ZeroPadding.pad R (List.replicate C false))
        (ZeroPadding.pad R (CompareMachine.word 1))) := by
  have first:=allocate_run R C M (List.replicate R false) (List.replicate R false)
  have second:=one_run R C M (List.replicate ((M+1)*(2*R)) false) hC
  have last:=write_run R C M (ZeroPadding.pad R (List.replicate C false))
    (ZeroPadding.pad R (CompareMachine.word 1))
    (by simp [ZeroPadding.pad_length,Nat.max_eq_left hC])
    (by simp [ZeroPadding.pad_length,CompareMachine.word,Nat.max_eq_left hR])
  have whole:=first.seq (second.seq last)
  have hf : PhysicalZeroBank.budget R (M+1)+1+(2+1+PacketBank.lookupBudget R 0)=budget R C M := by
    unfold budget;omega
  rw [hf] at whole
  exact whole


theorem empty_entry (R : Nat) (hR : 1≤R) :
    PacketVector.entry R []=List.replicate (2*R) false := by
  simp only [PacketVector.entry,PacketVector.payload,PacketVector.count,List.flatten_nil,List.length_nil,
    CompareMachine.word,List.replicate_zero,ZeroPadding.pad]
  simp only [List.length_nil,Nat.sub_zero,List.nil_append,List.length_singleton]
  have he : [false]++List.replicate (R-1) false=List.replicate R false := by
    simpa only [List.replicate_one] using (List.replicate_add 1 (R-1) false).symm.trans
      (congrArg (fun n=>List.replicate n false) (by omega : 1+(R-1)=R))
  rw [he,←List.replicate_add]
  congr 1;omega


theorem empty_bank (R M : Nat) (hR : 1≤R) :
    PacketVector.bank R (List.replicate M [])=List.replicate (M*(2*R)) false := by
  induction M with
  | zero=>simp [PacketVector.bank]
  | succ M ih=>
    rw [List.replicate_succ,PacketVector.bank,List.flatMap_cons]
    change PacketVector.entry R []++PacketVector.bank R (List.replicate M [])=_
    rw [empty_entry R hR,ih,←List.replicate_add]
    congr 1;ring


theorem result_bank (R C M : Nat) (hR : 1≤R) :
    result R C M=PacketVector.bank R ([List.replicate C false]::List.replicate M []) := by
  simp only [PacketVector.bank,List.flatMap_cons]
  change result R C M=PacketVector.entry R [List.replicate C false]++PacketVector.bank R (List.replicate M [])
  rw [empty_bank R M hR]
  simp [result,PacketVector.entry,PacketVector.payload,PacketVector.count,List.append_assoc]

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorTerminalBank
