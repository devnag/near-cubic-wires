import Proof.MachineModel.Runs

/-! Exact maximum from two physically present raw unary words. The output is
written one bit per step; rewind restores all three heads and retains inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.UnaryMaximum
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def raw : Machine 3 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun s bs=>if s.val=0 then some (if bs 0 || bs 1 then
    ⟨0,![none,none,some true],fun _=>.right⟩ else
    ⟨1,fun _=>none,fun _=>.stay⟩) else none

def cfg (s : Fin 2) (n m pos : Nat) : Configuration 3 2:=
  ⟨s,fun _=>pos,![List.replicate n true,List.replicate m true,List.replicate pos true]⟩

theorem read_raw (n p : Nat):readTapeBit (List.replicate n true) p=decide (p<n):=by
  simp [readTapeBit,List.getD,List.getElem?_replicate]
  split <;>simp_all

theorem copy_step (n m pos : Nat) (hp:pos < max n m):
    step raw (cfg 0 n m pos)=some (cfg 0 n m (pos+1)):=by
  have test:pos < n ∨ pos < m:=by omega
  simp [step,raw,cfg,Configuration.scanned,read_raw,test]
  apply configuration_ext
  · rfl
  · rfl
  · funext i;fin_cases i
    · rfl
    · rfl
    · change writeTapeBit (List.replicate pos true) pos true=List.replicate (pos+1) true
      have h:=Streaming.write_append (List.replicate pos true) true
      calc
        _ = List.replicate pos true++[true]:=by simpa only [List.length_replicate] using h
        _ = List.replicate (pos+1) true:=by rw [List.replicate_add];rfl

theorem stop_step (n m : Nat):step raw (cfg 0 n m (max n m))=some (cfg 1 n m (max n m)):=by
  simp [step,raw,cfg,Configuration.scanned,read_raw]
  apply configuration_ext <;>rfl

theorem scan (n m p k : Nat) (h:p+k ≤ max n m):
    Timed raw k (cfg 0 n m p) (cfg 0 n m (p+k)):=by
  induction k generalizing p with
  | zero=>simpa using Timed.refl raw (cfg 0 n m p)
  | succ k ih=>
    have hstep:=Timed.step (by rfl) (copy_step n m p (by omega)) (ih (p+1) (by omega))
    simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hstep

def machine:=Rewind.machine raw
def input (n m : Nat) : Fin 4→List Bool:=![List.replicate n true,List.replicate m true,[],[]]
def output (n m : Nat) : Fin 4→List Bool:=
  ![List.replicate n true,List.replicate m true,List.replicate (max n m) true,List.replicate (max n m+1) false]

theorem run (n m : Nat):Step machine (2*max n m+4)
    (fun _=>0) (input n m) (fun _=>0) (output n m):=by
  have path:Timed raw (max n m+1) (cfg 0 n m 0) (cfg 1 n m (max n m)):=by
    have first:Timed raw (max n m) (cfg 0 n m 0) (cfg 0 n m (max n m)):=by
      simpa using scan n m 0 (max n m) (by omega)
    exact first.trans (Timed.single (by rfl) (stop_step n m))
  obtain ⟨r,hr,hf,hs⟩:=path.run (by rfl)
  have hi:cfg 0 n m 0=initialConfiguration raw
      (![List.replicate n true,List.replicate m true,[]]):=rfl
  rw [hi] at hr
  obtain ⟨f,he,keep,log,heads,steps,_⟩:=Rewind.Workspace.reset_workspace raw _ _ r hr 0
  have inp:(Fin.addCases (m:=3) (n:=1)
      (![List.replicate n true,List.replicate m true,[]]:Fin 3→List Bool)
      (fun _ : Fin 1=>[]))=input n m:=by funext i;fin_cases i <;>rfl
  change LocalBitMultitape.run machine (2*r.steps+2) _=some f at he
  simp only [List.replicate_zero] at he
  rw [inp,hs,show 2*(max n m+1)+2=2*max n m+4 by omega] at he
  refine ⟨f,he,funext heads,?_,by omega⟩
  funext i;fin_cases i
  · simpa [hf,cfg,output] using keep 0
  · simpa [hf,cfg,output] using keep 1
  · simpa [hf,cfg,output] using keep 2
  · simpa [hs,output] using log

end Completion.UnaryMaximum
