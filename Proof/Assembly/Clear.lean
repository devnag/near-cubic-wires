import Proof.PCP.VerifierDecodingCompare
import Proof.Amplification.RecoveryTimedExecution

/-! Clear a candidate unary score from the comparator's actual head1 entry.
The forward seek, erase and return are all executed; backing is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Clear
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state bs =>
    if state.val = 0 then
      some (if bs 0 then ⟨0,fun _ => none,fun _ => .right⟩
        else ⟨1,fun _ => none,fun _ => .left⟩)
    else if state.val = 1 then
      some (if bs 0 then ⟨1,fun _ => some false,fun _ => .left⟩
        else ⟨2,fun _ => none,fun _ => .right⟩)
    else none

def scanCfg (n k : Nat) : Configuration 1 3 :=
  ⟨0,fun _ => k+1,fun _ => CompareMachine.word n⟩
def backCfg (k z : Nat) : Configuration 1 3 :=
  ⟨1,fun _ => k,fun _ => false::(List.replicate k true++List.replicate z false)⟩
def finished (n : Nat) : Configuration 1 3 :=
  ⟨2,fun _ => 1,fun _ => List.replicate (n+1) false⟩

theorem scan_step (n k : Nat) (hk : k < n) :
    step machine (scanCfg n k) = some (scanCfg n (k+1)) := by
  simp [step,machine,scanCfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply]
  · rfl

theorem scan_stop (n : Nat) :
    step machine (scanCfg n n) = some (backCfg n 0) := by
  simp [step,machine,scanCfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,backCfg,HeadMove.apply]
  · simp [applyAction,backCfg,CompareMachine.word]

theorem back_step (k z : Nat) :
    step machine (backCfg (k+1) z) = some (backCfg k (z+1)) := by
  have hr : readTapeBit (false::(List.replicate (k+1) true++List.replicate z false))
      (k+1) = true := by
    simp [readTapeBit,List.getD]
  simp [step,machine,backCfg,Configuration.scanned,hr]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply]
  · funext i
    simpa only [applyAction,writeTapeBit] using
      congrArg (List.cons false) (Streaming.erase_counter k z)

theorem stop (z : Nat) :
    step machine (backCfg 0 z) = some (finished z) := by
  simp [step,machine,backCfg,Configuration.scanned,readTapeBit,List.getD]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,finished,HeadMove.apply]
  · simp [applyAction,finished,List.replicate_succ]

theorem scan_timed (n k count : Nat) (hk : k+count ≤ n) :
    Timed machine count (scanCfg n k) (scanCfg n (k+count)) := by
  induction count generalizing k with
  | zero => simpa only [Nat.add_zero] using Timed.refl machine (scanCfg n k)
  | succ count ih =>
    have hs := Timed.single (by rfl) (scan_step n k (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 count] using hs.trans (ih (k+1) (by omega))

theorem back_timed (k z : Nat) :
    Timed machine (k+1) (backCfg k z) (finished (k+z)) := by
  induction k generalizing z with
  | zero => simpa only [Nat.zero_add] using Timed.single (by rfl) (stop z)
  | succ k ih =>
    have hs := Timed.single (by rfl) (back_step k z)
    simpa only [Nat.add_assoc,Nat.add_comm 1 z,Nat.add_comm 1 (k+1)] using hs.trans (ih (z+1))

theorem clear_run (n : Nat) :
    ∃ r, runFrom machine (2*n+2) (scanCfg n 0) = some r ∧
      r.final = finished n ∧ r.steps = 2*n+2 := by
  have hs := scan_timed n 0 n (by omega)
  simp only [Nat.zero_add] at hs
  have hm := Timed.single (by rfl) (scan_stop n)
  have ht := back_timed n 0
  simp only [Nat.add_zero] at ht
  have whole := (hs.trans hm).trans ht
  have htime : n+1+(n+1) = 2*n+2 := by omega
  rw [htime] at whole
  exact whole.run (by rfl)

end PCJ93d4cfe17dc847a3.Clear
