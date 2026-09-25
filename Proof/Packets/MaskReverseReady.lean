import Proof.Rows.MaskSeek
import Proof.Packets.MaterializerCursorReady

/-! Fixed-width bank reversal starts and ends at the bank's entry cursor.
The appended reversed bank is physically positioned for immediate consumption. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverseReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def raw := Composition.machine MaskSeek.machine MaskReverse.machine
noncomputable def machine := CursorRestore.machine raw 2

def budget (B N : Nat) := N*(6*B+12)+7
noncomputable def input (B N pos : Nat) (source out : List Bool) (cap : Nat) :=
  CursorReady.input (Composition.leftConfig (Fintype.card (RepeatMachine.Control 5)) (MaskSeek.loopCfg 0 B pos source out N 1)) cap

theorem flat_length (B : Nat) (rows : List (List Bool)) (hw : ∀ row∈rows,row.length=B) :
    rows.flatten.length=rows.length*B := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    rw [List.flatten_cons,List.length_append,hw row (by simp),ih (fun r hr=>hw r (by simp [hr]))]
    simp [Nat.add_mul,Nat.add_comm]

theorem raw_run (B : Nat) (rows : List (List Bool)) (pre suffix out : List Bool)
    (hw : ∀ row∈rows,row.length=B) :
    ∃ r,runFrom raw (budget B rows.length)
      (Composition.leftConfig _ (MaskSeek.loopCfg 0 B pre.length (pre++rows.flatten++suffix) out rows.length 1))=some r ∧
      r.steps=budget B rows.length ∧
      r.final=Composition.rightConfig _
        (MaskReverse.loopCfg 3 B pre.length (pre++rows.flatten++suffix) (out++rows.reverse.flatten) rows.length 1) := by
  obtain ⟨a,ha,haf,has⟩ := MaskSeek.seek_run B rows.length pre.length (pre++rows.flatten++suffix) out
  obtain ⟨b,hb,hbf,hbs⟩ := MaskReverse.reverse_run B rows pre suffix out hw
  have join : runFrom MaskReverse.machine (rows.length*(4*B+7)+3)
      (Composition.restart a.final MaskReverse.machine.start)=some b := by
    rw [haf]
    rw [flat_length B rows hw] at hb
    exact hb
  have h := Composition.run_join MaskSeek.machine MaskReverse.machine _ _ _ a b ha join
  have ht : rows.length*(2*B+5)+3+1+(rows.length*(4*B+7)+3)=budget B rows.length := by unfold budget; ring
  rw [ht] at h
  refine ⟨_,h,?_,?_⟩
  · simp only [Composition.joinedReceipt,has,hbs,ht]
  · change Composition.rightConfig _ b.final=_
    rw [hbf]

theorem seek_forward : CursorRestore.NoLeft MaskSeek.body 2 := by
  intro q bits a ha
  fin_cases q <;> simp [MaskSeek.body] at ha
  all_goals split at ha <;> cases ha <;> simp

theorem reverse_forward : CursorRestore.NoLeft MaskReverse.body 2 := by
  intro q bits a ha
  fin_cases q <;> simp [MaskReverse.body] at ha
  all_goals split at ha <;> cases ha <;> simp

theorem forward : CursorRestore.NoLeft raw 2 :=
  CursorRestore.composition_forward MaskSeek.machine MaskReverse.machine 2
    (CursorRestore.repeat_forward MaskSeek.body (fun _ _=>true) 2 seek_forward)
    (CursorRestore.repeat_forward MaskReverse.body (fun _ _=>true) 2 reverse_forward)

theorem ready_run (B : Nat) (rows : List (List Bool)) (pre suffix out : List Bool) (cap : Nat)
    (hw : ∀ row∈rows,row.length=B) (hcap : budget B rows.length≤cap) :
    ∃ r,runFrom machine (2*budget B rows.length+2)
      (input B rows.length pre.length (pre++rows.flatten++suffix) out cap)=some r ∧
      r.steps≤2*budget B rows.length+2 ∧
      r.final.tapes 0=UnaryTemplate.tape B ∧ r.final.heads 0=1 ∧
      r.final.tapes 1=pre++rows.flatten++suffix ∧ r.final.heads 1=pre.length ∧
      r.final.tapes 2=out++rows.reverse.flatten ∧ r.final.heads 2=out.length ∧
      r.final.tapes 3=CompareMachine.word rows.length ∧ r.final.heads 3=1 ∧
      r.final.tapes 4=List.replicate cap false ∧ r.final.heads 4=0 := by
  obtain ⟨a,ha,_,haf⟩ := raw_run B rows pre suffix out hw
  obtain ⟨r,hr,hrs,hrf⟩ := CursorReady.run raw 2 forward _ cap _ a ha hcap
  refine ⟨r,hr,hrs,?_⟩
  rw [hrf,haf]
  simp [CursorReady.ending,SelectiveReset.finished,Rewind.config,Composition.leftConfig,Composition.rightConfig,
    MaskReverse.loopCfg,MaskReverse.cfg,MaskSeek.loopCfg,MaskSeek.cfg,RepeatMachine.cfg,controlConfig,
    TapeEmbedding.config,Fin.addCases]

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverseReady
