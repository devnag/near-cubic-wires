import Proof.CaseAnalysis.RowsModeHashReturned

/-! Position the original lower-diagonal and translation cursors for the
next hash row by scanning the incremented original row template. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPosition
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,fun _=>none,![.right,.stay,.right]⟩
    else if q=1 then some (if bits 0 then ⟨1,fun _=>none,![.right,.right,.stay]⟩
      else ⟨2,fun _=>none,![.left,.stay,.stay]⟩) else none

def data (n : Nat) (lower translation : List Bool) : Fin 3→List Bool:=![CompareMachine.word n,lower,translation]
def cfg (q : Fin 3) (n d p t : Nat) (lower translation : List Bool) : Configuration 3 3:=
  ⟨q,![d,p,t],data n lower translation⟩

theorem start_step (n t : Nat) (lower translation : List Bool) :
    step machine (cfg 0 n 0 0 t lower translation)=some (cfg 1 n 1 0 (t+1) lower translation):=by
  simp only [step,machine,cfg,if_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem scan_step (n k t : Nat) (lower translation : List Bool) (hk : k<n) :
    step machine (cfg 1 n (k+1) k t lower translation)=some (cfg 1 n (k+2) (k+1) t lower translation):=by
  have hm:readTapeBit (CompareMachine.word n) (k+1)=true:=by simp [hk]
  simp only [step,machine,cfg,Configuration.scanned,data,Matrix.cons_val_zero,hm,if_true]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop_step (n t : Nat) (lower translation : List Bool) :
    step machine (cfg 1 n (n+1) n t lower translation)=some (cfg 2 n n n t lower translation):=by
  have hm:readTapeBit (CompareMachine.word n) (n+1)=false:=by simp
  simp only [step,machine,cfg,Configuration.scanned,data,Matrix.cons_val_zero,hm,if_true,Bool.false_eq_true,if_false]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem loop (n k remaining t : Nat) (lower translation : List Bool) (hk : k+remaining=n) :
    Timed machine (remaining+1) (cfg 1 n (k+1) k t lower translation) (cfg 2 n n n t lower translation):=by
  induction remaining generalizing k with
  | zero=>
    have h:k=n:=by omega
    subst k
    exact Timed.single (by rfl) (stop_step n t lower translation)
  | succ remaining ih=>
    have first:=Timed.single (by rfl) (scan_step n k t lower translation (by omega))
    have last:=ih (k+1) (by omega)
    simpa only [Nat.add_comm 1] using first.trans last

theorem position_run (n t : Nat) (lower translation : List Bool) :
    Step machine (n+2) ![0,0,t] (data n lower translation) ![n,n,t+1] (data n lower translation):=by
  have first:=Timed.single (by rfl) (start_step n t lower translation)
  have last:=loop n 0 n (t+1) lower translation (by omega)
  have whole:=first.trans last
  have time:1+(n+1)=n+2:=by omega
  rw [time] at whole
  obtain ⟨r,hr,rf,_⟩:=whole.run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashPosition
