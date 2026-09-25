import Proof.Packets.ParityFilterLoop
import Proof.Packets.ParityFilterForward
import Proof.Packets.MaterializerCursorReady

/-! The coefficient filter returns its output cursor and freshly produced
unary count cursor to the serializer ABI by two paid, erased movement logs. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def readyMachine := CursorRestore.machine (CursorRestore.machine machine 7) 8
noncomputable def readyInput (_B : Nat) (masks : List (List Bool))
    (candidatePrefix sourcePrefix candidateSuffix sourceSuffix out : List Bool)
    (rows : List PhysicalParityScan.Clause) (kept cap logCap outputCap countCap : Nat) (eq found : Bool) :=
  CursorReady.input (CursorReady.input
    (loopCfg 0 (candidatePrefix++candidateStream masks++candidateSuffix)
      (sourcePrefix++PhysicalParityScan.stream rows++sourceSuffix) out
      candidatePrefix.length sourcePrefix.length kept cap rows.length logCap masks.length 1 eq found)
    outputCap) countCap

def filterBudget (B count candidates cap : Nat) := candidates*(budget B count cap+3)+3

theorem ready_run (B : Nat) (masks : List (List Bool))
    (candidatePrefix sourcePrefix candidateSuffix sourceSuffix out : List Bool)
    (rows : List PhysicalParityScan.Clause) (kept cap logCap outputCap countCap : Nat) (eq found : Bool)
    (hw : ∀ bits∈masks,bits.length=B)
    (hcap : ∀ bits∈masks,∀ row∈rows,PhysicalParityProbe.budget (PhysicalParityScan.supportRecord bits) row≤cap)
    (hlog : rows.length*(2*cap+5)+3≤logCap)
    (hout : filterBudget B rows.length masks.length cap≤outputCap)
    (hcount : 2*filterBudget B rows.length masks.length cap+2≤countCap) :
    ∃ r,runFrom readyMachine (4*filterBudget B rows.length masks.length cap+6)
      (readyInput B masks candidatePrefix sourcePrefix candidateSuffix sourceSuffix out rows
        kept cap logCap outputCap countCap eq found)=some r ∧
      r.steps≤4*filterBudget B rows.length masks.length cap+6 ∧
      r.final.tapes 7=out++(selected rows masks).flatten ∧ r.final.heads 7=out.length ∧
      r.final.tapes 8=CompareMachine.word (kept+(selected rows masks).length) ∧ r.final.heads 8=kept+1 ∧
      r.final.tapes 10=List.replicate outputCap false ∧ r.final.heads 10=0 ∧
      r.final.tapes 11=List.replicate countCap false ∧ r.final.heads 11=0 := by
  obtain ⟨a,ha,_,haf⟩ := filter_run B masks candidatePrefix sourcePrefix candidateSuffix sourceSuffix out rows
    kept cap logCap eq found hw hcap hlog
  have forwardOut : CursorRestore.NoLeft machine 7 := CursorRestore.repeat_forward body (fun _ _=>true) 7 output_forward
  have forwardCount : CursorRestore.NoLeft machine 8 := CursorRestore.repeat_forward body (fun _ _=>true) 8 count_forward
  obtain ⟨b,hb,_,hbf⟩ := CursorReady.run machine 7 forwardOut _ outputCap _ a ha hout
  have outerForward : CursorRestore.NoLeft (CursorRestore.machine machine 7) 8 :=
    CursorRestore.other_forward machine 7 8 (by decide) forwardCount
  obtain ⟨c,hc,hcs,hcf⟩ := CursorReady.run (CursorRestore.machine machine 7) 8 outerForward _ countCap _ b hb hcount
  have ht : 2*(2*(masks.length*(budget B rows.length cap+3)+3)+2)+2=
      4*filterBudget B rows.length masks.length cap+6 := by unfold filterBudget; ring
  rw [ht] at hc hcs
  refine ⟨c,hc,hcs,?_⟩
  rw [hcf,hbf,haf]
  simp [CursorReady.ending,CursorReady.input,SelectiveReset.finished,Rewind.config,
    ZeroPadding.config,Rewind.recording,loopCfg,cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
    Fin.addCases]

end PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
