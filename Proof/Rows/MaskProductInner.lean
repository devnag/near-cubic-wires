import Proof.Rows.MaskProductRowReady
import Proof.PCP.VerifierDecodingRepeatBody

/-! The right-minor loop in Cartesian monomial multiplication. Each actual
iteration emits one record and increments the unary output counter. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable abbrev inner := RepeatMachine.machine machine (fun _ _=>true)
def record (mask bits : List Bool) := frame (values (mask.zip bits))++[false,false]
def records (mask : List Bool) (rows : List (List Bool)) := rows.flatMap (record mask)
noncomputable def innerCfg (phase : Fin 5) (B mh : Nat) (left right : List Bool)
    (pos : Nat) (out count : List Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (cfg machine.start B 1 mh left right pos out count) total driver

theorem inner_control (q : Fin 8) (phase : Fin 5) (B mh : Nat) (left right : List Bool)
    (pos : Nat) (out count : List Bool) (total driver : Nat) :
    RepeatMachine.cfg phase (cfg q B 1 mh left right pos out count) total driver=
      innerCfg phase B mh left right pos out count total driver := rfl

theorem inner_remaining (B : Nat) (mask : List Bool) (rows : List (List Bool))
    (mpre mtail pre tail out count : List Bool) (total done : Nat)
    (hm : mask.length=B) (hw : ∀ row∈rows,row.length=B) (hn : done+rows.length=total) :
    Timed inner (rows.length*(3*B+8)+total+3)
      (innerCfg 0 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
        pre.length out count total (done+1))
      (innerCfg 3 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
        (pre.length+rows.flatten.length) (out++records mask rows)
        (count++List.replicate rows.length true) total 1) := by
  induction rows generalizing pre out count done with
  | nil =>
    have hd : done=total := by simpa using hn
    subst done
    simpa [inner,innerCfg,records] using RepeatMachine.exhaust machine (fun _ _=>true)
      (cfg machine.start B 1 mpre.length (mpre++mask++mtail) (pre++tail)
        pre.length out count) total
  | cons row rows ih =>
    have hrow : row.length=B := hw row (by simp)
    have hrows : ∀ r∈rows,r.length=B := fun r hr=>hw r (by simp [hr])
    obtain ⟨r,hr,hf,hs⟩:=row_run mask row mpre mtail pre (rows.flatten++tail) out count
      (hm.trans hrow.symm)
    have first:=RepeatMachine.iteration machine (fun _ _=>true)
      (cfg machine.start row.length 1 mpre.length (mpre++mask++mtail)
        (pre++row++(rows.flatten++tail)) pre.length out count) total done r rfl
      (by simp only [List.length_cons] at hn;omega) hr
    rw [hf,hs,inner_control,inner_control,hrow] at first
    change Timed inner (3*B+6+2)
      (innerCfg 0 B mpre.length (mpre++mask++mtail) (pre++row++(rows.flatten++tail))
        pre.length out count total (done+1))
      (innerCfg 0 B mpre.length (mpre++mask++mtail) (pre++row++(rows.flatten++tail))
        (pre.length+B) (out++frame (values (mask.zip row))++[false,false])
        (count++[true]) total (done+2)) at first
    have rest:=ih (pre++row) (out++record mask row) (count++[true]) (done+1)
      hrows (by simp only [List.length_cons] at hn;omega)
    have h:=first.trans (by simpa [record,List.length_append,hrow,List.append_assoc,
      Nat.add_assoc] using rest)
    have fuel : (3*B+6+2)+(rows.length*(3*B+8)+total+3)=
        (rows.length+1)*(3*B+8)+total+3 := by ring
    simp only [Nat.add_assoc] at fuel h
    rw [fuel] at h
    simpa [records,record,List.flatten_cons,List.append_assoc,List.replicate_succ,
      List.length_append,hrow,Nat.add_assoc] using h

theorem inner_run (B : Nat) (mask : List Bool) (rows : List (List Bool))
    (mpre mtail pre tail out count : List Bool) (hm : mask.length=B)
    (hw : ∀ row∈rows,row.length=B) :
    ∃ r,runFrom inner (rows.length*(3*B+9)+3)
      (innerCfg 0 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
        pre.length out count rows.length 1)=some r ∧
      r.final=innerCfg 3 B mpre.length (mpre++mask++mtail) (pre++rows.flatten++tail)
        (pre.length+rows.flatten.length) (out++records mask rows)
        (count++List.replicate rows.length true) rows.length 1 ∧
      r.steps=rows.length*(3*B+9)+3 := by
  have h:=inner_remaining B mask rows mpre mtail pre tail out count rows.length 0
    hm hw (by omega)
  have fuel : rows.length*(3*B+8)+rows.length+3=rows.length*(3*B+9)+3 := by ring
  rw [fuel] at h
  simpa only [Nat.zero_add] using h.run (by
    simp [inner,innerCfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
