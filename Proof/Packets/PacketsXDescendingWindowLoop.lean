import Proof.Packets.PacketsXDescendingWindowOuter

/-! Both actual nested runtime loops of the exact-order window source.
The outer physical count is width+1; metadata changes and every inner cursor
return are included in the charged finite execution. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowScalar

def block (v M offset target d : Nat) :=
  (List.range (d+1)).flatMap (DescendingWindow.emit v M offset d target)
def output (v M offset target : Nat) (out : List Bool) (j : Nat) :=
  out++(List.range j).flatMap (block v M offset target)
def oldScratch (u offset old j : Nat) := if j=0 then old else CloseoutRowsModeShift.top u offset (j-1)
def oldNonzero (offset j : Nat) (old : Bool) := if j=0 then old else decide (offset+(j-1)≠0)
def oldGuard (offset target j : Nat) (old : Bool) := if j=0 then old else coefficient offset (j-1) (j-1) target
noncomputable def A (v u M offset target C old : Nat) (nonzero guard : Bool) (out : List Bool) (j : Nat) :=
  DescendingWindowSetup.A v u M 0 offset j (oldScratch u offset old j) j target C j
    (oldNonzero offset j nonzero) (oldGuard offset target j guard) (output v M offset target out j)
def H (v M offset target : Nat) (out : List Bool) (j : Nat) :=
  DescendingWindowSetup.H (output v M offset target out j)
noncomputable def machine := RepeatMachine.machine DescendingWindowOuter.machine (fun _ _=>true)
def budget (u width C : Nat) := (width+1)*(DescendingWindowOuter.budget u width C+3)+3

theorem output_succ (v M offset target : Nat) (out : List Bool) (j : Nat) :
    output v M offset target out (j+1)=
      DescendingWindow.output v M offset j target (output v M offset target out j) (j+1) := by
  simp only [output,DescendingWindow.output,block,List.range_succ,List.flatMap_append,
    List.flatMap_singleton,List.append_assoc]

theorem iterationBudget_mono (u d width C : Nat) (hd : d≤width) :
    DescendingWindowOuter.budget u d C≤DescendingWindowOuter.budget u width C := by
  have hm : (d+1)*(DescendingWindow.iterationBudget u d C+3)≤
      (width+1)*(DescendingWindow.iterationBudget u width C+3) :=
    Nat.mul_le_mul (by omega) (by unfold DescendingWindow.iterationBudget;omega)
  unfold DescendingWindowOuter.budget DescendingWindow.budget
  omega

theorem iteration_run (v u M offset target width C old : Nat) (nonzero guard : Bool)
    (out : List Bool) (j : Nat) (hj : j≤width)
    (hfit : offset+width<2^u) (hd : width+1<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hMv : M≤2^v) (hmeta : 2*v+width+3≤C)
    (hC : ∀k≤width,CloseoutRowsModeElementary.budget v k M+1≤C) :
    Step DescendingWindowOuter.machine (DescendingWindowOuter.budget u width C)
      (H v M offset target out j) (A v u M offset target C old nonzero guard out j)
      (H v M offset target out (j+1)) (A v u M offset target C old nonzero guard out (j+1)) := by
  have actual := (DescendingWindowOuter.run v u M 0 offset j (oldScratch u offset old j) j target C
    (oldNonzero offset j nonzero) (oldGuard offset target j guard) (output v M offset target out j)
    (by omega) (by omega) (by omega) ht hscalar hMv (by omega)
    (fun k hk=>hC k (by omega))).enlarge (iterationBudget_mono u j width C hj)
  simpa only [H,A,oldScratch,oldNonzero,oldGuard,show j+1≠0 by omega,if_false,
    Nat.add_sub_cancel,output_succ] using actual

theorem run (v u M offset target width C old : Nat) (nonzero guard : Bool) (out : List Bool)
    (hfit : offset+width<2^u) (hd : width+1<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hMv : M≤2^v) (hmeta : 2*v+width+3≤C)
    (hC : ∀k≤width,CloseoutRowsModeElementary.budget v k M+1≤C) :
    Step machine (budget u width C)
      (Fin.addCases (H v M offset target out 0) (fun _ : Fin 1=>1))
      (Fin.addCases (A v u M offset target C old nonzero guard out 0)
        (fun _ : Fin 1=>CompareMachine.word (width+1)))
      (Fin.addCases (H v M offset target out (width+1)) (fun _ : Fin 1=>1))
      (Fin.addCases (A v u M offset target C old nonzero guard out (width+1))
        (fun _ : Fin 1=>CompareMachine.word (width+1))) := by
  apply PhysicalRepeatStep.run DescendingWindowOuter.machine (width+1)
    (DescendingWindowOuter.budget u width C) (H v M offset target out)
    (A v u M offset target C old nonzero guard out)
  intro j hj
  exact iteration_run v u M offset target width C old nonzero guard out j (by omega)
    hfit hd ht hscalar hMv hmeta hC

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowLoop
