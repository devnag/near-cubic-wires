import Proof.Amplification.RecoveryFocusDock
import Proof.CaseAnalysis.RowsModeIndexBlock

/-! One real tuple digit is read and emitted as an ordinary index block.
The binary copy is overwritten on each iteration; tuple/width are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleDigit
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : Nat) (out : List Bool) : Fin 6→Nat:=![pos,0,1,0,0,out.length]
def data (w C : Nat) (source copy out : List Bool) (flag : Bool) : Fin 6→List Bool:=
  ![source,frame copy,CompareMachine.word w,[flag],List.replicate C false,out]
noncomputable def first:=TapeEmbedding.machine 3 FieldMachine.machine
def slots : Fin 4→Fin 6:=![1,3,4,5]
noncomputable def last:=RecoveryFocus.machine slots CloseoutRowsModeIndexBlock.machine
noncomputable def machine:=Composition.machine first last
def budget (w n : Nat):=4*w+3+CloseoutRowsModeIndexBlock.budget w n

theorem digit_run (w n C : Nat) (pre tail copy out : List Bool) (flag : Bool)
    (hn : n<2^w) (hc : 2*w+1≤C) (hcopy : copy.length≤w) :
    ∃ residue : List Bool,residue.length=w ∧
      Step machine (budget w n) (heads pre.length out)
        (data w C (pre++Streaming.marks (binary w n)++tail) copy out flag)
        (heads (pre.length+2*w) (out++ExtIncidence.block n))
        (data w C (pre++Streaming.marks (binary w n)++tail) residue (out++ExtIncidence.block n) false) := by
  obtain ⟨r,hr,rf,_rs,_⟩:=FieldMachine.field_run pre (binary w n) tail (frame copy)
    (by simp only [frame_length,binary_length];omega)
  let extraHeads : Fin 3→Nat:=![0,0,out.length]
  let extraTapes : Fin 3→List Bool:=![[flag],List.replicate C false,out]
  let firstReceipt:=TapeEmbedding.receipt extraHeads extraTapes r
  have firstRun:=TapeEmbedding.run_embed FieldMachine.machine extraHeads extraTapes _ _ r hr
  have initial : TapeEmbedding.config extraHeads extraTapes
      (FieldMachine.scan 0 (pre++Streaming.marks (binary w n)++tail) pre.length w 0 [] (frame copy))=
      (⟨first.start,heads pre.length out,
        data w C (pre++Streaming.marks (binary w n)++tail) copy out flag⟩ : Configuration 6 6):=by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> simp [TapeEmbedding.config,Fin.addCases,FieldMachine.scan,
        StablePartition.Workspace.overlay,extraTapes,data]
  simp only [binary_length] at firstRun rf
  rw [initial] at firstRun
  have fh : firstReceipt.final.heads=heads (pre.length+2*w) out:=by
    change (TapeEmbedding.config extraHeads extraTapes r.final).heads=_
    rw [rf];funext i;fin_cases i <;> rfl
  have ft : firstReceipt.final.tapes=data w C (pre++Streaming.marks (binary w n)++tail) (binary w n) out flag:=by
    change (TapeEmbedding.config extraHeads extraTapes r.final).tapes=_
    rw [rf];funext i;fin_cases i <;> rfl
  obtain ⟨residue,hres,raw⟩:=CloseoutRowsModeIndexBlock.block_run w n C out flag hn hc
  obtain ⟨b,hb,bh,bt,_⟩:=raw
  obtain ⟨lastReceipt,lastRun,_control,_steps,lh,lt,keep⟩:=RecoveryFocus.dock slots (by decide)
    CloseoutRowsModeIndexBlock.machine _ firstReceipt.final.heads firstReceipt.final.tapes _
    (by intro i;rw [fh];fin_cases i <;> rfl)
    (by intro i;rw [ft];fin_cases i <;> rfl) b hb
  have whole:=Composition.run_join first last _ _ _ firstReceipt lastReceipt firstRun lastRun
  have time:4*w+2+1+CloseoutRowsModeIndexBlock.budget w n=budget w n:=by unfold budget;omega
  rw [time] at whole
  have sourceKeep:=keep 0 (by decide)
  have widthKeep:=keep 2 (by decide)
  refine ⟨residue,hres,Step.of_run whole ?_ ?_⟩
  · change lastReceipt.final.heads=_
    funext i;fin_cases i
    · exact sourceKeep.1.trans (congrFun fh 0)
    · exact (lh 0).trans (congrFun bh 0)
    · exact widthKeep.1.trans (congrFun fh 2)
    · exact (lh 1).trans (congrFun bh 1)
    · exact (lh 2).trans (congrFun bh 2)
    · exact (lh 3).trans (congrFun bh 3)
  · change lastReceipt.final.tapes=_
    funext i;fin_cases i
    · exact sourceKeep.2.trans (congrFun ft 0)
    · exact (lt 0).trans (congrFun bt 0)
    · exact widthKeep.2.trans (congrFun ft 2)
    · exact (lt 1).trans (congrFun bt 1)
    · exact (lt 2).trans (congrFun bt 2)
    · exact (lt 3).trans (congrFun bt 3)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeTupleDigit
