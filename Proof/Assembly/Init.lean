import Proof.PCP.VerifierDecodingCompare
import Proof.Amplification.RecoveryTimedExecution

/-! Initial physical window, retained winner and loop drivers for the
ordinary cyclic-mask producer. The rule table is independent of every input. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ93d4cfe17dc847a3.Init
open NearCubicWires LocalBitMultitape RepairOrdinary RecoveryExecution Streaming
open NearCubicWires.RepairSource.VerifierDecoding

def bits (K n : Nat) : List Bool := (List.range n).map (fun i => decide (i < K))

@[simp] theorem bits_length (K n : Nat) : (bits K n).length = n := by simp [bits]
@[simp] theorem bits_zero (K : Nat) : bits K 0 = [] := rfl
theorem bits_succ (K n : Nat) : bits K (n+1) = bits K n ++ [decide (n<K)] := by
  simp [bits, List.range_succ]

theorem write_bits (K n : Nat) :
    writeTapeBit (bits K n) n (decide (n<K)) = bits K (n+1) := by
  have h := write_append (bits K n) (decide (n<K))
  simpa only [bits_length, ← bits_succ] using h

theorem write_second (q K n : Nat) :
    writeTapeBit (bits K q ++ bits K n) (q+n) (decide (n<K)) =
      bits K q ++ bits K (n+1) := by
  have h := write_append (bits K q ++ bits K n) (decide (n<K))
  simpa only [List.length_append, bits_length, List.append_assoc, ← bits_succ] using h

theorem write_unary (n : Nat) :
    writeTapeBit (CompareMachine.word n) (n+1) true = CompareMachine.word (n+1) := by
  have h := write_append (CompareMachine.word n) true
  simpa [CompareMachine.word, List.replicate_add, List.append_assoc] using h

def machine : Machine 8 6 where
  descriptionBits := 0
  start := 0
  halted := fun state => state.val == 5
  rule := fun state bs =>
    if state.val = 0 then
      some ⟨1, ![none,none,none,none,none,none,some false,none],
        ![.right,.right,.stay,.stay,.stay,.stay,.right,.right]⟩
    else if state.val = 1 then
      if bs 0 then
        some ⟨1, ![none,none,some (bs 1),some (bs 1),none,none,some true,none],
          ![.right,.right,.right,.right,.right,.right,.right,.stay]⟩
      else some ⟨2, fun _ => none, ![.left,.left,.stay,.stay,.stay,.stay,.stay,.stay]⟩
    else if state.val = 2 then
      if bs 0 then
        some ⟨2, fun _ => none, ![.left,.left,.stay,.left,.stay,.stay,.left,.stay]⟩
      else some ⟨3, fun _ => none, ![.right,.right,.stay,.stay,.stay,.stay,.stay,.stay]⟩
    else if state.val = 3 then
      if bs 0 then
        some ⟨3, ![none,none,some (bs 1),none,none,none,none,none],
          ![.right,.right,.right,.stay,.stay,.stay,.stay,.stay]⟩
      else some ⟨4, fun _ => none, ![.left,.left,.stay,.stay,.stay,.stay,.stay,.stay]⟩
    else if state.val = 4 then
      if bs 0 then
        some ⟨4, fun _ => none, ![.left,.left,.left,.stay,.stay,.stay,.stay,.stay]⟩
      else some ⟨5, fun _ => none, fun _ => .stay⟩
    else none

def initial (q K : Nat) (mword : List Bool) : Configuration 8 6 :=
  ⟨0, fun _ => 0, ![CompareMachine.word q,CompareMachine.word K,[],[],[],[],[],mword]⟩

def scanCfg (second : Bool) (q K : Nat) (mword : List Bool) (k : Nat) :
    Configuration 8 6 :=
  ⟨if second then 3 else 1,
    ![k+1,k+1,if second then q+k else k,if second then 0 else k,
      if second then q else k,if second then q else k,if second then 1 else k+1,1],
    ![CompareMachine.word q,CompareMachine.word K,
      if second then bits K q ++ bits K k else bits K k,
      if second then bits K q else bits K k,[],[],
      CompareMachine.word (if second then q else k),mword]⟩

def rewindCfg (second : Bool) (q K : Nat) (mword : List Bool) (k : Nat) :
    Configuration 8 6 :=
  ⟨if second then 4 else 2,
    ![k,k,if second then q+k else q,if second then 0 else k,q,q,
      if second then 1 else k+1,1],
    ![CompareMachine.word q,CompareMachine.word K,
      if second then bits K q ++ bits K q else bits K q,bits K q,[],[],
      CompareMachine.word q,mword]⟩

def finished (q K : Nat) (mword : List Bool) : Configuration 8 6 :=
  ⟨5, ![0,0,q,0,q,q,1,1],
    ![CompareMachine.word q,CompareMachine.word K,bits K q ++ bits K q,
      bits K q,[],[],CompareMachine.word q,mword]⟩

theorem start_step (q K : Nat) (mword : List Bool) :
    step machine (initial q K mword) = some (scanCfg false q K mword 0) := by
  simp [step, machine, initial]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, scanCfg, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, scanCfg, CompareMachine.word, writeTapeBit]

theorem scan_step (second : Bool) (q K : Nat) (mword : List Bool) (k : Nat)
    (hk : k < q) :
    step machine (scanCfg second q K mword k) =
      some (scanCfg second q K mword (k+1)) := by
  cases second <;> simp [step, machine, scanCfg, Configuration.scanned, hk]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, Nat.add_assoc]
    · funext i; fin_cases i <;> simp [applyAction, write_bits, write_second, write_unary]

theorem scan_stop (second : Bool) (q K : Nat) (mword : List Bool) :
    step machine (scanCfg second q K mword q) =
      some (rewindCfg second q K mword q) := by
  cases second <;> simp [step, machine, scanCfg, Configuration.scanned]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction, rewindCfg, HeadMove.apply]
    · rfl

theorem rewind_step (second : Bool) (q K : Nat) (mword : List Bool) (k : Nat)
    (hk : k < q) :
    step machine (rewindCfg second q K mword (k+1)) =
      some (rewindCfg second q K mword k) := by
  cases second <;> simp [step, machine, rewindCfg, Configuration.scanned, hk]
  all_goals
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply, Nat.add_assoc]
    · rfl

theorem second_start (q K : Nat) (mword : List Bool) :
    step machine (rewindCfg false q K mword 0) =
      some (scanCfg true q K mword 0) := by
  simp [step, machine, rewindCfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, scanCfg, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, scanCfg]

theorem halt_step (q K : Nat) (mword : List Bool) :
    step machine (rewindCfg true q K mword 0) = some (finished q K mword) := by
  simp [step, machine, rewindCfg, Configuration.scanned]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, finished, HeadMove.apply]
  · rfl

theorem scan_timed (second : Bool) (q K : Nat) (mword : List Bool)
    (k n : Nat) (hn : k+n ≤ q) :
    Timed machine n (scanCfg second q K mword k) (scanCfg second q K mword (k+n)) := by
  induction n generalizing k with
  | zero => simpa only [Nat.add_zero] using Timed.refl machine (scanCfg second q K mword k)
  | succ n ih =>
    have hs := Timed.single (by cases second <;> rfl) (scan_step second q K mword k (by omega))
    have ht := ih (k+1) (by omega)
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using hs.trans ht

theorem rewind_timed (second : Bool) (q K : Nat) (mword : List Bool)
    (k : Nat) (hk : k ≤ q) :
    Timed machine k (rewindCfg second q K mword k) (rewindCfg second q K mword 0) := by
  induction k with
  | zero => exact Timed.refl _ _
  | succ k ih =>
    have hs := Timed.single (by cases second <;> rfl) (rewind_step second q K mword k (by omega))
    simpa only [Nat.add_comm 1 k] using hs.trans (ih (by omega))

theorem initializer_timed (q K : Nat) (mword : List Bool) :
    Timed machine (4*q+5) (initial q K mword) (finished q K mword) := by
  have first := scan_timed false q K mword 0 q (by omega)
  have second := scan_timed true q K mword 0 q (by omega)
  simp only [Nat.zero_add] at first second
  have h0 := Timed.single (by rfl) (start_step q K mword)
  have h2 := Timed.single (by rfl) (scan_stop false q K mword)
  have h4 := Timed.single (by rfl) (second_start q K mword)
  have h6 := Timed.single (by rfl) (scan_stop true q K mword)
  have h8 := Timed.single (by rfl) (halt_step q K mword)
  have whole := (((((((h0.trans first).trans h2).trans
    (rewind_timed false q K mword q (by omega))).trans h4).trans second).trans h6).trans
    (rewind_timed true q K mword q (by omega))).trans h8
  have ht : 1+q+1+q+1+q+1+q+1 = 4*q+5 := by omega
  simpa only [ht] using whole

theorem initializer_run (q K : Nat) (mword : List Bool) :
    ∃ r, run machine (4*q+5) (initial q K mword).tapes = some r ∧
      r.final = finished q K mword ∧ r.steps = 4*q+5 := by
  exact (initializer_timed q K mword).run (by rfl)

end PCJ93d4cfe17dc847a3.Init
