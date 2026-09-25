import Proof.PCP.VerifierDecodingCompare
import Proof.Amplification.RecoveryTimedExecution

/-! Replace the retained winning bitmap by the q raw bits at the candidate
offset. Both bitmap heads return to their entry positions; no erase pass. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Copy
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

theorem write_replace (pre tail : List Bool) (old b : Bool) :
    writeTapeBit (pre ++ old::tail) pre.length b = pre ++ b::tail := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simp [writeTapeBit,ih]

def machine : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 2
  rule := fun state bs =>
    if state.val = 0 then
      if bs 0 then some ⟨0, ![none,none,some (bs 1)], fun _ => .right⟩
      else some ⟨1, fun _ => none, ![.left,.stay,.stay]⟩
    else if state.val = 1 then
      if bs 0 then some ⟨1, fun _ => none, fun _ => .left⟩
      else some ⟨2, fun _ => none, ![.right,.stay,.stay]⟩
    else none

def scanCfg (q : Nat) (pre done xs old tail : List Bool) : Configuration 3 3 :=
  ⟨0, ![done.length+1,pre.length+done.length,done.length],
    ![CompareMachine.word q,pre++done++xs++tail,done++old]⟩

def backCfg (q : Nat) (pre xs tail : List Bool) (k : Nat) : Configuration 3 3 :=
  ⟨1, ![k,pre.length+k,k], ![CompareMachine.word q,pre++xs++tail,xs]⟩

def finished (q : Nat) (pre xs tail : List Bool) : Configuration 3 3 :=
  ⟨2, ![1,pre.length,0], ![CompareMachine.word q,pre++xs++tail,xs]⟩

theorem scan_step (q : Nat) (pre done xs old tail : List Bool) (b o : Bool)
    (hq : done.length < q) :
    step machine (scanCfg q pre done (b::xs) (o::old) tail) =
      some (scanCfg q pre (done++[b]) xs old tail) := by
  have hr : readTapeBit (pre++done++(b::xs)++tail) (pre.length+done.length) = b := by
    simpa only [List.length_append,List.cons_append,List.append_assoc] using
      Streaming.read_append (pre++done) (xs++tail) b
  simp [step,machine,scanCfg,Configuration.scanned,hq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply,Nat.add_assoc]
  · funext i
    fin_cases i <;> simp [applyAction,write_replace]
    simpa only [List.append_assoc,List.cons_append] using hr

theorem scan_stop (q : Nat) (pre done tail : List Bool) (hq : done.length = q) :
    step machine (scanCfg q pre done [] [] tail) = some (backCfg q pre done tail q) := by
  simp [step,machine,scanCfg,Configuration.scanned,hq]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,backCfg,HeadMove.apply]
  · simp [applyAction,backCfg]

theorem back_step (q : Nat) (pre xs tail : List Bool) (k : Nat) (hk : k < q) :
    step machine (backCfg q pre xs tail (k+1)) = some (backCfg q pre xs tail k) := by
  simp [step,machine,backCfg,Configuration.scanned,hk]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem stop (q : Nat) (pre xs tail : List Bool) :
    step machine (backCfg q pre xs tail 0) = some (finished q pre xs tail) := by
  simp [step,machine,backCfg,Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,finished,HeadMove.apply]
  · simp [applyAction,finished]

theorem forward_timed (q : Nat) (pre done xs old tail : List Bool)
    (hlen : old.length = xs.length) (hq : done.length+xs.length = q) :
    Timed machine (xs.length+1) (scanCfg q pre done xs old tail)
      (backCfg q pre (done++xs) tail q) := by
  induction xs generalizing done old with
  | nil =>
    have ho : old = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst old
    simpa using Timed.single (by rfl) (scan_stop q pre done tail (by simpa using hq))
  | cons b xs ih =>
    cases old with
    | nil => simp at hlen
    | cons o old =>
      have hs := Timed.single (by rfl) (scan_step q pre done xs old tail b o (by simp at hq; omega))
      have ht := ih (done++[b]) old (by simpa using hlen) (by simp at hq ⊢; omega)
      simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans ht

theorem back_timed (q : Nat) (pre xs tail : List Bool) (k : Nat) (hk : k ≤ q) :
    Timed machine (k+1) (backCfg q pre xs tail k) (finished q pre xs tail) := by
  induction k with
  | zero => exact Timed.single (by rfl) (stop q pre xs tail)
  | succ k ih =>
    have hs := Timed.single (by rfl) (back_step q pre xs tail k (by omega))
    simpa only [Nat.add_comm 1 (k+1)] using hs.trans (ih (by omega))

theorem copy_run (pre xs old tail : List Bool) (hlen : old.length = xs.length) :
    ∃ r, runFrom machine (2*xs.length+2) (scanCfg xs.length pre [] xs old tail) = some r ∧
      r.final = finished xs.length pre xs tail ∧ r.steps = 2*xs.length+2 := by
  have hf := forward_timed xs.length pre [] xs old tail hlen (by simp)
  simp only [List.nil_append] at hf
  have whole := hf.trans (back_timed xs.length pre xs tail xs.length (by omega))
  have ht : xs.length+1+(xs.length+1) = 2*xs.length+2 := by omega
  rw [ht] at whole
  exact whole.run (by rfl)

end PCJ93d4cfe17dc847a3.Copy
