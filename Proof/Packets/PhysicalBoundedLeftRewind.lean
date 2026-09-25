import Proof.Amplification.RecoveryTimedExecution
import Proof.MachineModel.OrdinaryUnaryTemplate

/-! A paid unary capacity bounds the current cursor. The fixed machine walks
that many cells left, with the physical head's usual clamp at zero, then
restores its capacity driver. It never changes either tape. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace Completion.PhysicalBoundedLeftRewind
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def cfg (state : Fin 3) (capacity driverPos sourcePos : Nat) (source : List Bool) :
    Configuration 2 3 := ⟨state,![driverPos,sourcePos],![UnaryTemplate.tape capacity,source]⟩

def machine : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==2
  rule:=fun s bs=>if s.val=0 then some
    (if bs 0 then ⟨0,fun _=>none,![.right,.left]⟩
      else ⟨1,fun _=>none,![.left,.stay]⟩)
    else if s.val=1 then some
      (if bs 0 then ⟨1,fun _=>none,![.left,.stay]⟩
        else ⟨2,fun _=>none,![.right,.stay]⟩) else none

theorem forward_step (capacity j pos : Nat) (source : List Bool) (hj : j<capacity) :
    step machine (cfg 0 capacity (j+1) pos source)=
      some (cfg 0 capacity (j+2) (pos-1) source) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark capacity j hj]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem forward_stop (capacity pos : Nat) (source : List Bool) :
    step machine (cfg 0 capacity (capacity+1) pos source)=
      some (cfg 1 capacity capacity pos source) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem forward_timed (capacity j n pos : Nat) (source : List Bool) (hn : j+n=capacity) :
    Timed machine (n+1) (cfg 0 capacity (j+1) pos source)
      (cfg 1 capacity capacity (pos-n) source) := by
  induction n generalizing j pos with
  | zero =>
    have hj : j=capacity := by omega
    simpa only [hj,Nat.sub_zero] using Timed.single (by rfl) (forward_stop capacity pos source)
  | succ n ih =>
    have first := Timed.single (by rfl) (forward_step capacity j pos source (by omega))
    have tail := ih (j+1) (pos-1) (by omega)
    have h := first.trans tail
    have he : pos-1-n=pos-(n+1) := by omega
    simpa only [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem back_step (capacity j pos : Nat) (source : List Bool) (hj : j<capacity) :
    step machine (cfg 1 capacity (j+1) pos source)=
      some (cfg 1 capacity j pos source) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark capacity j hj]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem back_stop (capacity pos : Nat) (source : List Bool) :
    step machine (cfg 1 capacity 0 pos source)=some (cfg 2 capacity 1 pos source) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> rfl
  · rfl

theorem back_timed (capacity n pos : Nat) (source : List Bool) (hn : n≤capacity) :
    Timed machine (n+1) (cfg 1 capacity n pos source) (cfg 2 capacity 1 pos source) := by
  induction n with
  | zero => exact Timed.single (by rfl) (back_stop capacity pos source)
  | succ n ih =>
    have h := (Timed.single (by rfl) (back_step capacity n pos source (by omega))).trans (ih (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem run_sub (capacity pos : Nat) (source : List Bool) :
    ∃ r,runFrom machine (2*capacity+2) (cfg 0 capacity 1 pos source)=some r ∧
      r.final=cfg 2 capacity 1 (pos-capacity) source ∧ r.steps=2*capacity+2 := by
  have first := forward_timed capacity 0 capacity pos source (by omega)
  have last := back_timed capacity capacity (pos-capacity) source le_rfl
  have h := first.trans last
  simpa only [Nat.zero_add,Nat.two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    using h.run (by rfl)

theorem run (capacity pos : Nat) (source : List Bool) (hpos : pos≤capacity) :
    ∃ r,runFrom machine (2*capacity+2) (cfg 0 capacity 1 pos source)=some r ∧
      r.final=cfg 2 capacity 1 0 source ∧ r.steps=2*capacity+2 := by
  simpa only [Nat.sub_eq_zero_of_le hpos] using run_sub capacity pos source

end Completion.PhysicalBoundedLeftRewind
