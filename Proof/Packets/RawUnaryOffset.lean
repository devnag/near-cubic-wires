import Proof.PCP.PCPUnaryCopy
import Proof.Rows.PhysicalFocusBoundary

/-! Physically prepend a fixed unary offset, then copy the runtime raw unary
value. The literal64 instance completes the graded-window counter; both heads
are returned by the actual masked-reset program. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.RawUnaryOffset
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open RecoveryExecution NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def copyCfg (q : Fin 2) (n k : Nat) (pre : List Bool) : Configuration 2 2 :=
  ⟨q,![k,pre.length+k],![List.replicate n true,pre++List.replicate k true]⟩

theorem copy_step (n k : Nat) (pre : List Bool) (hk : k<n) :
    step PCPUnaryCopy.raw (copyCfg 0 n k pre)=some (copyCfg 0 n (k+1) pre) := by
  have hn : readTapeBit (List.replicate n true) k=true := by simp [readTapeBit,List.getD,hk]
  simp [step,PCPUnaryCopy.raw,copyCfg,Configuration.scanned,hn]
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>simp [applyAction,HeadMove.apply];omega
  · funext i;fin_cases i
    · rfl
    · change writeTapeBit (pre++List.replicate k true) (pre.length+k) true=pre++List.replicate (k+1) true
      have h:=Streaming.write_append (pre++List.replicate k true) true
      simpa only [List.length_append,List.length_replicate,List.replicate_add,List.replicate_one,List.append_assoc] using h

theorem stop (n : Nat) (pre : List Bool) :
    step PCPUnaryCopy.raw (copyCfg 0 n n pre)=some (copyCfg 1 n n pre) := by
  simp [step,PCPUnaryCopy.raw,copyCfg,Configuration.scanned,readTapeBit,List.getD]
  rfl

theorem loop (n k rest : Nat) (pre : List Bool) (h:k+rest=n) :
    Timed PCPUnaryCopy.raw (rest+1) (copyCfg 0 n k pre) (copyCfg 1 n n pre) := by
  induction rest generalizing k with
  | zero=>
    have he:k=n:=by omega
    subst k
    simpa using Timed.single (by rfl) (stop n pre)
  | succ rest ih=>
    exact Timed.step (by rfl) (copy_step n k pre (by omega)) (ih (k+1) (by omega))

theorem copy_run (n : Nat) (pre : List Bool) :
    Step PCPUnaryCopy.raw (n+1) (![0,pre.length]) (![List.replicate n true,pre])
      (![n,pre.length+n]) (![List.replicate n true,pre++List.replicate n true]) := by
  obtain ⟨r,rr,rf,_⟩:=(loop n 0 n pre (by omega)).run (by rfl)
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  simpa only [copyCfg,Nat.zero_add,Nat.add_zero,List.replicate_zero,List.append_nil] using h

def slot : Fin 1→Fin 2 := fun _=>1
def seed (offset : Nat) := RecoveryFocus.machine slot (HierarchyFixedWord.raw (CompareMachine.word offset))
def machine (offset : Nat) := Composition.machine (seed offset) PCPUnaryCopy.raw

theorem seed_run (offset n : Nat) :
    Step (seed offset) (offset+1) (fun _=>0) (![List.replicate n true,[]])
      (![0,offset+1]) (![List.replicate n true,CompareMachine.word offset]) := by
  let bits:=CompareMachine.word offset
  obtain ⟨r,rr,rf,_⟩:=(HierarchyFixedWord.write_prefix bits 0 bits.length (by omega)).run
    (by simp [HierarchyFixedWord.raw,HierarchyFixedWord.cfg])
  have h:=Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have h' : Step (HierarchyFixedWord.raw bits) (offset+1) (fun _=>0) (fun _=>[])
      (fun _=>offset+1) (fun _=>bits) := by
    simp only [HierarchyFixedWord.cfg,List.take_zero,List.take_length] at h
    simpa only [bits,CompareMachine.word,List.length_cons,List.length_replicate] using h
  exact PhysicalFocusBoundary.focus h' slot (by intro i j _;exact Subsingleton.elim i j)
    (fun _=>0) (![0,offset+1]) (![List.replicate n true,[]]) (![List.replicate n true,bits])
    (by intro i;rfl) (by intro i;rfl) (by intro i;rfl) (by intro i;rfl)
    (by intro i away;fin_cases i
        · exact ⟨rfl,rfl⟩
        · exact False.elim (away 0 rfl))

theorem run (offset n : Nat) :
    Step (machine offset) (n+offset+3) (fun _=>0) (![List.replicate n true,[]])
      (![n,offset+1+n]) (![List.replicate n true,CompareMachine.word (offset+n)]) := by
  have last:=copy_run n (CompareMachine.word offset)
  have he : CompareMachine.word offset++List.replicate n true=CompareMachine.word (offset+n) := by
    simp only [CompareMachine.word,List.replicate_add,List.cons_append]
  simp only [CompareMachine.word,List.length_cons,List.length_replicate] at last
  have ht : (false::List.replicate offset true)++List.replicate n true=CompareMachine.word (offset+n) := he
  rw [ht] at last
  have h:=(seed_run offset n).seq last
  have hf : (offset+1)+1+(n+1)=n+offset+3 := by omega
  rw [hf] at h
  exact h

def returned (offset : Nat) := MaskedReset.machine (machine offset) (fun _=>true)
def padded (R : Nat) (A : Fin 2→List Bool) : Fin 3→List Bool :=
  Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad R (A i)) (fun _=>List.replicate R false)

theorem ready (offset R n : Nat) (hr : n+offset+3≤R) :
    Step (returned offset) (2*n+2*offset+8) (fun _=>0)
      (padded R (![List.replicate n true,[]])) (fun _=>0)
      (padded R (![List.replicate n true,CompareMachine.word (offset+n)])) := by
  have h:=((run offset n).pad (fun _=>R)).mask (fun _=>true) (by intros;rfl) hr
  have hf : 2*(n+offset+3)+2=2*n+2*offset+8 := by omega
  rw [hf] at h
  exact (h.congr_in (by funext i;fin_cases i <;>rfl) rfl).congr
    (by funext i;fin_cases i <;>rfl) rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.RawUnaryOffset
