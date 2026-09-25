import Proof.PCP.VerifierDecodingCompare
import Proof.Amplification.RecoveryTimedExecution

/-! A strict improvement overwrites the old unary best score directly.
Its monotonicity eliminates a separate erasing pass. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Best
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

theorem write_true (n k : Nat) (hk : k ≤ n) :
    writeTapeBit (List.replicate n true) k true = List.replicate (max n (k+1)) true := by
  induction n generalizing k with
  | zero =>
    have he : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    cases k with
    | zero => simp [writeTapeBit,List.replicate_succ]
    | succ k =>
      have he : max (n+1) (k+1+1) = max n (k+1)+1 := by omega
      simp only [List.replicate_succ,writeTapeBit]
      rw [ih k (by omega)]
      simp only [he,List.replicate_succ]

theorem write_score (m k : Nat) :
    writeTapeBit (CompareMachine.word (max m k)) (k+1) true =
      CompareMachine.word (max m (k+1)) := by
  have hm : max (max m k) (k+1) = max m (k+1) := by omega
  simp only [CompareMachine.word,writeTapeBit,write_true (max m k) k (by omega),hm]

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state bs =>
    if state.val = 0 then
      if bs 0 then some ⟨0, ![none,some true], fun _ => .right⟩
      else some ⟨1, fun _ => none, fun _ => .left⟩
    else if state.val = 1 then
      if bs 0 then some ⟨1, fun _ => none, fun _ => .left⟩
      else some ⟨2, fun _ => none, fun _ => .right⟩
    else none

def scanCfg (n m k : Nat) : Configuration 2 3 :=
  ⟨0, fun _ => k+1, ![CompareMachine.word n,CompareMachine.word (max m k)]⟩
def backCfg (n m k : Nat) : Configuration 2 3 :=
  ⟨1, fun _ => k, ![CompareMachine.word n,CompareMachine.word (max m n)]⟩
def finished (n m : Nat) : Configuration 2 3 :=
  ⟨2, fun _ => 1, ![CompareMachine.word n,CompareMachine.word (max m n)]⟩

theorem scan_step (n m k : Nat) (hk : k < n) :
    step machine (scanCfg n m k) = some (scanCfg n m (k+1)) := by
  simp [step,machine,scanCfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction,write_score]

theorem scan_stop (n m : Nat) :
    step machine (scanCfg n m n) = some (backCfg n m n) := by
  simp [step,machine,scanCfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,backCfg,HeadMove.apply]
  · rfl

theorem back_step (n m k : Nat) (hk : k < n) :
    step machine (backCfg n m (k+1)) = some (backCfg n m k) := by
  simp [step,machine,backCfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,HeadMove.apply]
  · rfl

theorem stop (n m : Nat) :
    step machine (backCfg n m 0) = some (finished n m) := by
  simp [step,machine,backCfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; simp [applyAction,finished,HeadMove.apply]
  · rfl

theorem scan_timed (n m k count : Nat) (hk : k+count ≤ n) :
    Timed machine count (scanCfg n m k) (scanCfg n m (k+count)) := by
  induction count generalizing k with
  | zero => simpa only [Nat.add_zero] using Timed.refl machine (scanCfg n m k)
  | succ count ih =>
    have hs := Timed.single (by rfl) (scan_step n m k (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 count] using hs.trans (ih (k+1) (by omega))

theorem back_timed (n m k : Nat) (hk : k ≤ n) :
    Timed machine (k+1) (backCfg n m k) (finished n m) := by
  induction k with
  | zero => exact Timed.single (by rfl) (stop n m)
  | succ k ih =>
    have hs := Timed.single (by rfl) (back_step n m k (by omega))
    simpa only [Nat.add_comm 1 (k+1)] using hs.trans (ih (by omega))

theorem best_run (n m : Nat) :
    ∃ r, runFrom machine (2*n+2) (scanCfg n m 0) = some r ∧
      r.final = finished n m ∧ r.steps = 2*n+2 := by
  have hs := scan_timed n m 0 n (by omega)
  simp only [Nat.zero_add] at hs
  have hm := Timed.single (by rfl) (scan_stop n m)
  have whole := (hs.trans hm).trans (back_timed n m n (by omega))
  have ht : n+1+(n+1) = 2*n+2 := by omega
  rw [ht] at whole
  exact whole.run (by rfl)

end PCJ93d4cfe17dc847a3.Best
