import Proof.Rows.MaskSeek

/-! Counted backwards cursor return. The source word and its runtime width
and row-count drivers are preserved; no movement log is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskBack
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def body : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=>
    if q.val=0 then some (if scan 0 then ⟨0,fun _=>none,![.right,.left,.stay]⟩
      else ⟨1,fun _=>none,![.left,.stay,.stay]⟩)
    else if q.val=1 then some (if scan 0 then ⟨1,fun _=>none,![.left,.stay,.stay]⟩
      else ⟨2,fun _=>none,![.right,.stay,.stay]⟩)
    else none

abbrev cfg := MaskSeek.cfg

theorem back_step (B i pos : Nat) (hi : i<B) (source out : List Bool) :
    step body (cfg 0 B (i+1) (pos+1) source out)=some (cfg 0 B (i+2) pos source out) := by
  simp [step,body,cfg,MaskSeek.cfg,Configuration.scanned,UnaryTemplate.tape_mark B i hi]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_stop (B pos : Nat) (source out : List Bool) :
    step body (cfg 0 B (B+1) pos source out)=some (cfg 1 B B pos source out) := by
  simp [step,body,cfg,MaskSeek.cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back (B n pos : Nat) (hn : n≤B) (source out : List Bool) :
    Timed body (n+1) (cfg 0 B (B-n+1) (pos+n) source out) (cfg 1 B B pos source out) := by
  induction n with
  | zero => simpa using Timed.single (by rfl) (back_stop B pos source out)
  | succ n ih =>
    have hs:=back_step B (B-(n+1)) (pos+n) (by omega) source out
    have he : B-(n+1)+2=B-n+1 := by omega
    rw [he] at hs
    have h:=(Timed.single (by rfl) hs).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem reset_step (B n pos : Nat) (hn : n<B) (source out : List Bool) :
    step body (cfg 1 B (n+1) pos source out)=some (cfg 1 B n pos source out) := by
  simp [step,body,cfg,MaskSeek.cfg,Configuration.scanned,UnaryTemplate.tape_mark B n hn]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem reset_stop (B pos : Nat) (source out : List Bool) :
    step body (cfg 1 B 0 pos source out)=some (cfg 2 B 1 pos source out) := by
  simp [step,body,cfg,MaskSeek.cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext j;fin_cases j <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem reset (B n pos : Nat) (hn : n≤B) (source out : List Bool) :
    Timed body (n+1) (cfg 1 B n pos source out) (cfg 2 B 1 pos source out) := by
  induction n with
  | zero => exact Timed.single (by rfl) (reset_stop B pos source out)
  | succ n ih =>
    have h:=(Timed.single (by rfl) (reset_step B n pos (by omega) source out)).trans (ih (by omega))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem row_run (B pos : Nat) (source out : List Bool) :
    ∃ r,runFrom body (2*B+2) (cfg 0 B 1 (pos+B) source out)=some r ∧
      r.final=cfg 2 B 1 pos source out ∧ r.steps=2*B+2 := by
  have first:=back B B pos le_rfl source out
  simp only [Nat.sub_self,Nat.zero_add] at first
  have h:=first.trans (reset B B pos le_rfl source out)
  have fuel : (B+1)+(B+1)=2*B+2 := by omega
  simpa only [fuel] using h.run (by rfl)

noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)
noncomputable def loopCfg (phase : Fin 5) (B pos : Nat) (source out : List Bool) (total driver : Nat) :=
  RepeatMachine.cfg phase (cfg body.start B 1 pos source out) total driver

theorem remaining (B n pos total done : Nat) (hn : done+n=total) (source out : List Bool) :
    Timed machine (n*(2*B+4)+total+3)
      (loopCfg 0 B (pos+n*B) source out total (done+1))
      (loopCfg 3 B pos source out total 1) := by
  induction n generalizing done with
  | zero =>
    have he : done=total := by omega
    subst done
    simpa [machine,loopCfg] using RepeatMachine.exhaust body (fun _ _=>true)
      (cfg body.start B 1 pos source out) total
  | succ n ih =>
    obtain ⟨r,hr,hf,hs⟩:=row_run B (pos+n*B) source out
    have it:=RepeatMachine.iteration body (fun _ _=>true)
      (cfg 0 B 1 (pos+n*B+B) source out) total done r rfl (by omega) hr
    rw [hf,hs] at it
    change Timed machine (2*B+2+2) (loopCfg 0 B (pos+n*B+B) source out total (done+1))
      (loopCfg 0 B (pos+n*B) source out total (done+2)) at it
    have rest:=ih (done+1) (by omega)
    have h:=it.trans (by simpa [Nat.add_assoc] using rest)
    have fuel : (2*B+2+2)+(n*(2*B+4)+total+3)=(n+1)*(2*B+4)+total+3 := by ring
    have start : pos+n*B+B=pos+(n+1)*B := by ring
    simp only [Nat.add_assoc] at fuel start h
    rw [fuel,start] at h
    exact h

theorem back_run (B N pos : Nat) (source out : List Bool) :
    ∃ r,runFrom machine (N*(2*B+5)+3) (loopCfg 0 B (pos+N*B) source out N 1)=some r ∧
      r.final=loopCfg 3 B pos source out N 1 ∧ r.steps=N*(2*B+5)+3 := by
  have h:=remaining B N pos N 0 (by omega) source out
  have fuel : N*(2*B+4)+N+3=N*(2*B+5)+3 := by ring
  rw [fuel] at h
  simpa only [Nat.zero_add] using h.run (by
    simp [machine,loopCfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskBack
