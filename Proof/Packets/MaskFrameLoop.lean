import Proof.Packets.MaskFrame
import Proof.PCP.VerifierDecodingRepeatBody

/-! An actual counted loop framing a flat bank of raw masks. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable abbrev loop := RepeatMachine.machine machine (fun _ _=>true)
def record (bits : List Bool) := frame bits++[false,false]
def records (rows : List (List Bool)) := rows.flatMap record
noncomputable def loopCfg (phase : Fin 5) (B : Nat) (dummy source : List Bool)
    (pos : Nat) (out count : List Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (cfg machine.start B 1 0 dummy source pos out count) total driver

theorem loop_control (q : Fin 8) (phase : Fin 5) (B : Nat) (dummy source : List Bool)
    (pos : Nat) (out count : List Bool) (total driver : Nat) :
    RepeatMachine.cfg phase (cfg q B 1 0 dummy source pos out count) total driver=
      loopCfg phase B dummy source pos out count total driver := rfl

theorem loop_remaining (B : Nat) (rows : List (List Bool))
    (dummy pre tail out count : List Bool) (total done : Nat)
    (hw : ∀ row∈rows,row.length=B) (hn : done+rows.length=total) :
    Timed loop (rows.length*(3*B+8)+total+3)
      (loopCfg 0 B dummy (pre++rows.flatten++tail)
        pre.length out count total (done+1))
      (loopCfg 3 B dummy (pre++rows.flatten++tail)
        (pre.length+rows.flatten.length) (out++records rows)
        (count++List.replicate rows.length true) total 1) := by
  induction rows generalizing pre out count done with
  | nil =>
    have hd : done=total := by simpa using hn
    subst done
    simpa [loop,loopCfg,records] using RepeatMachine.exhaust machine (fun _ _=>true)
      (cfg machine.start B 1 0 dummy (pre++tail)
        pre.length out count) total
  | cons row rows ih =>
    have hrow : row.length=B := hw row (by simp)
    have hrows : ∀ r∈rows,r.length=B := fun r hr=>hw r (by simp [hr])
    obtain ⟨r,hr,hf,hs⟩:=row_run row dummy pre (rows.flatten++tail) out count
    have first:=RepeatMachine.iteration machine (fun _ _=>true)
      (cfg machine.start row.length 1 0 dummy
        (pre++row++(rows.flatten++tail)) pre.length out count) total done r rfl
      (by simp only [List.length_cons] at hn;omega) hr
    rw [hf,hs,loop_control,loop_control,hrow] at first
    change Timed loop (3*B+6+2)
      (loopCfg 0 B dummy (pre++row++(rows.flatten++tail))
        pre.length out count total (done+1))
      (loopCfg 0 B dummy (pre++row++(rows.flatten++tail))
        (pre.length+B) (out++frame row++[false,false])
        (count++[true]) total (done+2)) at first
    have rest:=ih (pre++row) (out++record row) (count++[true]) (done+1)
      hrows (by simp only [List.length_cons] at hn;omega)
    have h:=first.trans (by simpa [record,List.length_append,hrow,List.append_assoc,
      Nat.add_assoc] using rest)
    have fuel : (3*B+6+2)+(rows.length*(3*B+8)+total+3)=
        (rows.length+1)*(3*B+8)+total+3 := by ring
    simp only [Nat.add_assoc] at fuel h
    rw [fuel] at h
    simpa [records,record,List.flatten_cons,List.append_assoc,List.replicate_succ,
      List.length_append,hrow,Nat.add_assoc] using h

theorem loop_run (B : Nat) (rows : List (List Bool))
    (dummy pre tail out count : List Bool)
    (hw : ∀ row∈rows,row.length=B) :
    ∃ r,runFrom loop (rows.length*(3*B+9)+3)
      (loopCfg 0 B dummy (pre++rows.flatten++tail)
        pre.length out count rows.length 1)=some r ∧
      r.final=loopCfg 3 B dummy (pre++rows.flatten++tail)
        (pre.length+rows.flatten.length) (out++records rows)
        (count++List.replicate rows.length true) rows.length 1 ∧
      r.steps=rows.length*(3*B+9)+3 := by
  have h:=loop_remaining B rows dummy pre tail out count rows.length 0
    hw (by omega)
  have fuel : rows.length*(3*B+8)+rows.length+3=rows.length*(3*B+9)+3 := by ring
  rw [fuel] at h
  simpa only [Nat.zero_add] using h.run (by
    simp [loop,loopCfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
