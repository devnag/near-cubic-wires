import Proof.Packets.PhysicalSupportReturn

/-! The existing mask return worker restores a mask cursor to its actual
bank prefix, not only to absolute zero. No transition code is changed. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open PhysicalSupportReturn (cfg machine)

 theorem return_start (B base pos : Nat) (left right out : List Bool) :
    step machine (cfg 0 B (B+1) (base+B) left right pos out)=
      some (cfg 1 B B (base+B) left right pos out) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

 theorem return_bit (B base k pos : Nat) (left right out : List Bool) (hk : k<B) :
    step machine (cfg 1 B (k+1) (base+k+1) left right pos out)=
      some (cfg 1 B k (base+k) left right pos out) := by
  simp [step,machine,cfg,Configuration.scanned,UnaryTemplate.tape_mark B k hk]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

 theorem return_stop (B base pos : Nat) (left right out : List Bool) :
    step machine (cfg 1 B 0 base left right pos out)=
      some (cfg 2 B 1 base left right pos out) := by
  simp [step,machine,cfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

 theorem return_loop (B base k pos : Nat) (left right out : List Bool) (hk : k≤B) :
    Timed machine (k+1) (cfg 1 B k (base+k) left right pos out)
      (cfg 2 B 1 base left right pos out) := by
  induction k with
  | zero => simpa only [Nat.add_zero] using
      Timed.single (by rfl) (return_stop B base pos left right out)
  | succ k ih =>
    have one := Timed.single (by rfl : machine.halted 1=false)
      (return_bit B base k pos left right out (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using one.trans (ih (by omega))

 theorem return_run (B base pos : Nat) (left right out : List Bool) :
    ∃ r,runFrom machine (B+2) (cfg 0 B (B+1) (base+B) left right pos out)=some r ∧
      r.final=cfg 2 B 1 base left right pos out ∧ r.steps=B+2 := by
  have first := Timed.single (by rfl : machine.halted 0=false)
    (return_start B base pos left right out)
  have rest := return_loop B base B pos left right out (Nat.le_refl _)
  have h := first.trans rest
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.run (by rfl)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
