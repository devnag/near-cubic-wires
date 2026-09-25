import Proof.MachineModel.Runs

/-! One actual scan splits the retained child counter at the original
window counter, producing both capped count and nonnegative offset. -/
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DeltaSplitCounters
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open RecoveryExecution NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,![none,none,some false,some false],fun _=>.right⟩
    else if q=1 then some (if bits 0 then
      ⟨1,![none,none,if bits 1 then some true else none,if bits 1 then none else some true],
        ![.right,.right,if bits 1 then .right else .stay,if bits 1 then .stay else .right]⟩
      else ⟨2,fun _=>none,fun _=>.stay⟩) else none
def heads (w k : Nat) : Fin 4→Nat:=![k+1,k+1,min k w+1,k-w+1]
def data (n w k : Nat) : Fin 4→List Bool:=
  ![CompareMachine.word n,CompareMachine.word w,CompareMachine.word (min k w),CompareMachine.word (k-w)]
def cfg (q : Fin 3) (n w k : Nat) : Configuration 4 3:=⟨q,heads w k,data n w k⟩

theorem write_word (n : Nat) :
    writeTapeBit (false::List.replicate n true) (n+1) true=false::List.replicate (n+1) true := by
  simpa only [List.length_cons,List.length_replicate,List.cons_append,List.replicate_add,List.replicate_one]
    using Streaming.write_append (false::List.replicate n true) true

theorem scan_step (n w k : Nat) (hk : k < n) :
    step machine (cfg 1 n w k)=some (cfg 1 n w (k+1)):=by
  have hn:(cfg 1 n w k).scanned 0=true:=by
    exact (CompareMachine.read_mark n k).trans (decide_eq_true hk)
  have hw:(cfg 1 n w k).scanned 1=decide (k<w):=CompareMachine.read_mark w k
  simp only [step,machine,hn,hw,if_true]
  by_cases hkw:k<w
  · have hm:min (k+1) w=min k w+1:=by omega
    have hd:k+1-w=k-w:=by omega
    simp only [decide_eq_true hkw,if_true]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,cfg,heads,HeadMove.apply,hm,hd]
    · funext i;fin_cases i <;> simp [applyAction,cfg,heads,data,hm,hd,CompareMachine.word,write_word]
  · have hm:min (k+1) w=min k w:=by omega
    have hd:k+1-w=k-w+1:=by omega
    simp only [decide_eq_false hkw]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,cfg,heads,HeadMove.apply,hm,hd]
    · funext i;fin_cases i <;> simp [applyAction,cfg,heads,data,hm,hd,CompareMachine.word,write_word]

theorem stop (n w : Nat) : step machine (cfg 1 n w n)=some (cfg 2 n w n):=by
  have hn:(cfg 1 n w n).scanned 0=false:=by
    exact (CompareMachine.read_mark n n).trans (by simp)
  simp only [step,machine,hn,if_false,Bool.false_eq_true]
  rfl

def input (n w : Nat) : Fin 4→List Bool := ![CompareMachine.word n,CompareMachine.word w,[],[]]

theorem scan_prefix (w k remaining : Nat) :
    Timed machine remaining (cfg 1 (k+remaining) w k) (cfg 1 (k+remaining) w (k+remaining)) := by
  induction remaining generalizing k with
  | zero=>simpa only [Nat.add_zero] using Timed.refl machine (cfg 1 k w k)
  | succ remaining ih=>
    have hs:=Timed.single (by rfl) (scan_step (k+(remaining+1)) w k (by omega))
    have ht:=ih (k+1)
    have he:k+1+remaining=k+(remaining+1):=by omega
    rw [he] at ht
    simpa only [Nat.add_comm 1 remaining] using hs.trans ht

theorem run (n w : Nat) : Step machine (n+2) (fun _=>0) (input n w) (heads w n) (data n w n) := by
  have hb:step machine (initialConfiguration machine (input n w))=some (cfg 1 n w 0) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [machine,initialConfiguration,applyAction,cfg,heads,HeadMove.apply]
    · funext i;fin_cases i <;>simp [machine,initialConfiguration,applyAction,cfg,data,input,CompareMachine.word] <;>rfl
  have hp:=scan_prefix w 0 n
  simp only [Nat.zero_add] at hp
  have whole:=((Timed.single (by rfl) hb).trans hp).trans (Timed.single (by rfl) (stop n w))
  have he:1+n+1=n+2:=by omega
  rw [he] at whole
  obtain ⟨r,hr,rf,_⟩:=whole.run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

noncomputable def returned := MaskedReset.machine machine (fun _=>true)
def padded (R : Nat) (a : Fin 4→List Bool) : Fin 5→List Bool :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad R (a i)) (fun _=>List.replicate R false)

theorem ready (R n w : Nat) (hr : n+2≤R) :
    Step returned (2*n+6) (fun _=>0) (padded R (input n w))
      (fun _=>0) (padded R (data n w n)) := by
  have h:=((run n w).pad (fun _=>R)).mask (fun _=>true) (by intros;rfl) hr
  have he:2*(n+2)+2=2*n+6:=by omega
  rw [he] at h
  exact (h.congr_in (by funext i;fin_cases i <;>rfl) rfl).congr
    (by funext i;fin_cases i <;>rfl) rfl

end PCJ9eff70d512234a4c_Fixed.Materializer.DeltaSplitCounters
