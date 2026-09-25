import Proof.SourceAssembly.SourceBundle

/-! One actual scan splits the retained child counter at the original
window counter, producing both capped count and nonnegative offset. -/
namespace NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then some ⟨1,fun _=>none,![.right,.right,.stay,.stay]⟩
    else if q=1 then some (if bits 0 then
      ⟨1,![none,none,if bits 1 then some true else none,if bits 1 then none else some true],
        ![.right,.right,if bits 1 then .right else .stay,if bits 1 then .stay else .right]⟩
      else ⟨2,fun _=>none,fun _=>.stay⟩) else none
def heads (w k : Nat) : Fin 4→Nat:=![k+1,k+1,min k w,k-w]
def data (n w k : Nat) : Fin 4→List Bool:=
  ![CompareMachine.word n,CompareMachine.word w,List.replicate (min k w) true,List.replicate (k-w) true]
def cfg (q : Fin 3) (n w k : Nat) : Configuration 4 3:=⟨q,heads w k,data n w k⟩

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
    · funext i;fin_cases i <;> simp [applyAction,cfg,heads,data,hm,hd]
  · have hm:min (k+1) w=min k w:=by omega
    have hd:k+1-w=k-w+1:=by omega
    simp only [decide_eq_false hkw]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [applyAction,cfg,heads,HeadMove.apply,hm,hd]
    · funext i;fin_cases i <;> simp [applyAction,cfg,heads,data,hm,hd]

theorem stop (n w : Nat) : step machine (cfg 1 n w n)=some (cfg 2 n w n):=by
  have hn:(cfg 1 n w n).scanned 0=false:=by
    exact (CompareMachine.read_mark n n).trans (by simp)
  simp only [step,machine,hn,if_false,Bool.false_eq_true]
  rfl

end NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin

/-! Complete executed counter split, including zero, with its own entry
head advance and a paid return for reuse of the original counters. -/
namespace NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scan_prefix (w k remaining : Nat) :
    Timed machine remaining (cfg 1 (k+remaining) w k) (cfg 1 (k+remaining) w (k+remaining)):=by
  induction remaining generalizing k with
  | zero=>simpa only [Nat.add_zero] using Timed.refl machine (cfg 1 k w k)
  | succ remaining ih=>
    have hs:=Timed.single (by rfl) (scan_step (k+(remaining+1)) w k (by omega))
    have ht:=ih (k+1)
    have he:k+1+remaining=k+(remaining+1):=by omega
    rw [he] at ht
    simpa only [Nat.add_comm 1 remaining] using hs.trans ht

theorem run (n w : Nat) : Step machine (n+2) (fun _=>0) (data n w 0) (heads w n) (data n w n):=by
  have hb:step machine (initialConfiguration machine (data n w 0))=some (cfg 1 n w 0):=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> simp [machine,initialConfiguration,applyAction,cfg,heads,HeadMove.apply]
    · funext i;fin_cases i <;> rfl
  have hp:=scan_prefix w 0 n
  simp only [Nat.zero_add] at hp
  have whole:=((Timed.single (by rfl) hb).trans hp).trans (Timed.single (by rfl) (stop n w))
  have he:1+n+1=n+2:=by omega
  rw [he] at whole
  obtain ⟨r,hr,rf,_⟩:=whole.run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)


end NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin

namespace NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
/-- Same existing split execution, with a paid cold recording log. -/
def split := CloseoutFinalC10ColdCacheRewind.machine PCJ6e421fabe2aa4155_SourceLiveMin.machine

theorem split_run (n w : Nat) : ∃ log,
    Step split (2*n+6) (fun _=>0) ![CompareMachine.word n,CompareMachine.word w,[],[],[]]
      (fun _=>0) ![CompareMachine.word n,CompareMachine.word w,List.replicate (min n w) true,
        List.replicate (n-w) true,List.replicate log false] ∧ log ≤ n+2 := by
  obtain ⟨r,hr,_,ht,hs⟩:=PCJ6e421fabe2aa4155_SourceLiveMin.run n w
  have h:=CloseoutFinalC10ColdCacheRewind.rewind_run PCJ6e421fabe2aa4155_SourceLiveMin.machine (n+2)
    (PCJ6e421fabe2aa4155_SourceLiveMin.data n w 0) r hr hs
  rw [ht] at h
  refine ⟨r.steps,?_,hs⟩
  convert h using 1 <;> first | rfl | omega | (funext i;fin_cases i <;> simp [PCJ6e421fabe2aa4155_SourceLiveMin.data,Fin.addCases])

end NearCubicWires.RepairOrdinary.PCJ6e421fabe2aa4155_SourceLiveMin
