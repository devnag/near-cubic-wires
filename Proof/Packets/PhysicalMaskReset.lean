import Proof.Packets.PhysicalMaskBank
/-! Paid reusable-template reset after one native monomial serialization.
The old unary counter cells remain allocated as zero reserve; no shrinking
of physical tape lists or free head reset is used. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.PhysicalMaskReset
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch

def counter (done remaining : Nat) : List Bool :=
  false :: true :: (List.replicate done false ++ List.replicate remaining true ++ [false])
def cfg (B : Nat) (source : List Bool) (sourcePos : Nat) (q : Fin 4)
    (widthPos : Nat) (index : List Bool) (indexPos : Nat) (out : List Bool) : Configuration 4 4 :=
  ⟨q, ![widthPos,sourcePos,indexPos,out.length], ![UnaryTemplate.tape B,source,index,out]⟩
def machine : Machine 4 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bits => if q.val=0 then
      some ⟨1,fun _=>none,![.left,.stay,.right,.stay]⟩
    else if q.val=1 then some (if bits 2 then
      ⟨1,![none,none,some false,none],![.left,.stay,.right,.stay]⟩ else
      ⟨2,fun _=>none,![.right,.stay,.left,.stay]⟩)
    else if q.val=2 then some (if bits 2 then
      ⟨3,fun _=>none,fun _=>.stay⟩ else
      ⟨2,fun _=>none,![.stay,.stay,.left,.stay]⟩)
    else none

theorem start_step (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) :
    step machine (cfg B source sourcePos 0 (B+1) (UnaryTemplate.tape (B+1)) 1 out)=
      some (cfg B source sourcePos 1 B (counter 0 B) 2 out) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · simp [applyAction,counter,UnaryTemplate.tape,List.replicate_succ]

theorem read_counter (done remaining : Nat) :
    readTapeBit (counter done (remaining+1)) (done+2)=true := by
  simpa [counter,List.replicate_succ] using
    Streaming.read_append (false::true::List.replicate done false)
      (List.replicate remaining true++[false]) true

theorem write_at (pre tail : List Bool) (before after : Bool) :
    writeTapeBit (pre++before::tail) pre.length after = pre++after::tail := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simp [writeTapeBit,ih]

theorem erase_counter (done remaining : Nat) :
    writeTapeBit (counter done (remaining+1)) (done+2) false = counter (done+1) remaining := by
  have h := write_at (false::true::List.replicate done false)
    (List.replicate remaining true++[false]) true false
  change writeTapeBit (counter done (remaining+1)) (done+2) false =
    false::true::(List.replicate (done+1) false ++ List.replicate remaining true ++ [false])
  rw [List.replicate_succ']
  simpa [counter,List.replicate_succ,List.append_assoc,Nat.add_assoc] using h

theorem erase_step (B done remaining : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) :
    step machine (cfg B source sourcePos 1 (remaining+1) (counter done (remaining+1)) (done+2) out)=
      some (cfg B source sourcePos 1 remaining (counter (done+1) remaining) (done+3) out) := by
  simp [step,machine,cfg,Configuration.scanned,read_counter]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,erase_counter]

theorem turn_step (B done : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) :
    step machine (cfg B source sourcePos 1 0 (counter done 0) (done+2) out)=
      some (cfg B source sourcePos 2 1 (counter done 0) (done+1) out) := by
  have h : readTapeBit (counter done 0) (done+2)=false := by
    simpa [counter] using Streaming.read_append (false::true::List.replicate done false) [] false
  simp [step,machine,cfg,Configuration.scanned,h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem zero_at (B pos : Nat) (h : pos < B) :
    readTapeBit (counter B 0) (pos+2)=false := by
  obtain ⟨rest,he⟩ := Nat.exists_eq_add_of_le (show pos+1≤B by omega)
  subst B
  have hh := Streaming.read_append (false::true::List.replicate pos false)
    (List.replicate rest false++[false]) false
  simpa [counter,List.replicate_add,List.replicate_succ',List.append_assoc] using hh

theorem back_step (B pos : Nat) (source : List Bool) (sourcePos : Nat)
    (out : List Bool) (h : pos < B) :
    step machine (cfg B source sourcePos 2 1 (counter B 0) (pos+2) out)=
      some (cfg B source sourcePos 2 1 (counter B 0) (pos+1) out) := by
  simp [step,machine,cfg,Configuration.scanned,zero_at B pos h]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem finish_step (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) :
    step machine (cfg B source sourcePos 2 1 (counter B 0) 1 out)=
      some (cfg B source sourcePos 3 1 (counter B 0) 1 out) := by
  simp [step,machine,cfg,Configuration.scanned,counter,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · rfl
  · rfl

theorem erase_prefix (B remaining done : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) :
    Timed machine (remaining+1)
      (cfg B source sourcePos 1 remaining (counter done remaining) (done+2) out)
      (cfg B source sourcePos 2 1 (counter (done+remaining) 0) (done+remaining+1) out) := by
  induction remaining generalizing done with
  | zero => simpa using Timed.single (by rfl) (turn_step B done source sourcePos out)
  | succ remaining ih =>
    have first := Timed.single (by rfl) (erase_step B done remaining source sourcePos out)
    have tail := ih (done+1)
    have h := first.trans tail
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem return_prefix (B pos : Nat) (source : List Bool) (sourcePos : Nat)
    (out : List Bool) (h : pos≤B) :
    Timed machine (pos+1)
      (cfg B source sourcePos 2 1 (counter B 0) (pos+1) out)
      (cfg B source sourcePos 3 1 (counter B 0) 1 out) := by
  induction pos with
  | zero => exact Timed.single (by rfl) (finish_step B source sourcePos out)
  | succ pos ih =>
    exact Timed.step (by rfl) (back_step B pos source sourcePos out (by omega)) (ih (by omega))

theorem counter_padded (B : Nat) :
    counter B 0=ZeroPadding.pad (B+3) (UnaryTemplate.tape 1) := by
  simp only [counter,ZeroPadding.pad,UnaryTemplate.tape,List.replicate_one,List.replicate_zero,
    List.append_nil,List.nil_append,List.length_cons,List.cons_append,
    List.cons.injEq,true_and]
  exact List.replicate_succ'.symm.trans List.replicate_succ

theorem reset_run (B : Nat) (source : List Bool) (sourcePos : Nat) (out : List Bool) :
    ∃ r, runFrom machine (2*B+3)
      (cfg B source sourcePos 0 (B+1) (UnaryTemplate.tape (B+1)) 1 out)=some r ∧
      r.final=cfg B source sourcePos 3 1 (ZeroPadding.pad (B+3) (UnaryTemplate.tape 1)) 1 out ∧
      r.steps=2*B+3 := by
  have first := Timed.single (by rfl) (start_step B source sourcePos out)
  have erase := erase_prefix B B 0 source sourcePos out
  simp only [Nat.zero_add] at erase
  have h := (first.trans erase).trans (return_prefix B B source sourcePos out le_rfl)
  have time : 1+(B+1)+(B+1)=2*B+3 := by omega
  rw [time] at h
  simpa only [counter_padded] using h.run (by rfl)

end PCJ9eff70d512234a4c_Fixed.PhysicalMaskReset
