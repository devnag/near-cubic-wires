import Proof.PCP.VerifierDecodingCompare
import Proof.Amplification.RecoveryTimedExecution

/-! Return the three support-scanner mask heads by exactly q cells, retaining
their original offset. The physically supplied unary driver returns to1. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.MaskReturn
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state bs =>
    if state.val = 0 then
      if bs 0 then some ⟨0, fun _ => none, ![.right,.left,.left,.left]⟩
      else some ⟨1, fun _ => none, ![.left,.stay,.stay,.stay]⟩
    else if state.val = 1 then
      if bs 0 then some ⟨1, fun _ => none, ![.left,.stay,.stay,.stay]⟩
      else some ⟨2, fun _ => none, ![.right,.stay,.stay,.stay]⟩
    else none

def tapes (q : Nat) (mask : Fin 3 → List Bool) : Fin 4 → List Bool :=
  ![CompareMachine.word q,mask 0,mask 1,mask 2]

def scanCfg (q offset : Nat) (mask : Fin 3 → List Bool) (k : Nat) : Configuration 4 3 :=
  ⟨0, ![k+1,offset+q-k,offset+q-k,offset+q-k], tapes q mask⟩

def backCfg (q offset : Nat) (mask : Fin 3 → List Bool) (k : Nat) : Configuration 4 3 :=
  ⟨1, ![k,offset,offset,offset], tapes q mask⟩

def finished (q offset : Nat) (mask : Fin 3 → List Bool) : Configuration 4 3 :=
  ⟨2, ![1,offset,offset,offset], tapes q mask⟩

theorem scan_step (q offset : Nat) (mask : Fin 3 → List Bool) (k : Nat)
    (hk : k < q) :
    step machine (scanCfg q offset mask k) = some (scanCfg q offset mask (k+1)) := by
  simp [step,machine,scanCfg,tapes,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i
    · simp [applyAction,HeadMove.apply]
    all_goals
      change offset+q-k-1 = offset+q-(k+1)
      omega
  · rfl

theorem scan_stop (q offset : Nat) (mask : Fin 3 → List Bool) :
    step machine (scanCfg q offset mask q) = some (backCfg q offset mask q) := by
  simp [step,machine,scanCfg,tapes,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,backCfg,HeadMove.apply]
  · rfl

theorem back_step (q offset : Nat) (mask : Fin 3 → List Bool) (k : Nat)
    (hk : k < q) :
    step machine (backCfg q offset mask (k+1)) = some (backCfg q offset mask k) := by
  simp [step,machine,backCfg,tapes,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop (q offset : Nat) (mask : Fin 3 → List Bool) :
    step machine (backCfg q offset mask 0) = some (finished q offset mask) := by
  simp [step,machine,backCfg,tapes,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,finished,HeadMove.apply]
  · rfl

theorem scan_timed (q offset : Nat) (mask : Fin 3 → List Bool) (k n : Nat)
    (hn : k+n ≤ q) :
    Timed machine n (scanCfg q offset mask k) (scanCfg q offset mask (k+n)) := by
  induction n generalizing k with
  | zero => simpa only [Nat.add_zero] using Timed.refl machine (scanCfg q offset mask k)
  | succ n ih =>
    have hs := Timed.single (by rfl) (scan_step q offset mask k (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 n] using hs.trans (ih (k+1) (by omega))

theorem back_timed (q offset : Nat) (mask : Fin 3 → List Bool) (k : Nat)
    (hk : k ≤ q) :
    Timed machine (k+1) (backCfg q offset mask k) (finished q offset mask) := by
  induction k with
  | zero => exact Timed.single (by rfl) (stop q offset mask)
  | succ k ih =>
    have hs := Timed.single (by rfl) (back_step q offset mask k (by omega))
    simpa only [Nat.add_comm 1 (k+1)] using hs.trans (ih (by omega))

theorem return_run (q offset : Nat) (mask : Fin 3 → List Bool) :
    ∃ r, runFrom machine (2*q+2) (scanCfg q offset mask 0) = some r ∧
      r.final = finished q offset mask ∧ r.steps = 2*q+2 := by
  have hs := scan_timed q offset mask 0 q (by omega)
  simp only [Nat.zero_add] at hs
  have hm := Timed.single (by rfl) (scan_stop q offset mask)
  have whole := (hs.trans hm).trans (back_timed q offset mask q (by omega))
  have ht : q+1+(q+1) = 2*q+2 := by omega
  rw [ht] at whole
  exact whole.run (by rfl)

end PCJ93d4cfe17dc847a3.MaskReturn
