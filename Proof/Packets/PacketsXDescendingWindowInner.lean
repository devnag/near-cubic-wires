import Proof.Packets.PacketsXDescendingWindowBody
import Proof.Packets.PhysicalRepeatStep

/-! Executed descending antidiagonal loop, including its actual unary loop
driver and exact native output append order. No body call is required at the
terminal counter value. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowLayout CloseoutRowsModeWindowScalar

def emit (v M offset d target j : Nat) :=
  CloseoutRowsModeWindowEmit.word v (d-j) M (coefficient offset j d target)
def scratch (u offset old j : Nat) := if j=0 then old else CloseoutRowsModeShift.top u offset (j-1)
def nonzero (offset j : Nat) (old : Bool) := if j=0 then old else decide (offset+(j-1)≠0)
def guard (offset d target j : Nat) (old : Bool) := if j=0 then old else coefficient offset (j-1) d target

def output (v M offset d target : Nat) (out : List Bool) (j : Nat) :=
  out++(List.range j).flatMap (emit v M offset d target)
noncomputable def A (v u M offset d target C old : Nat) (oldNonzero oldGuard : Bool)
    (out : List Bool) (j : Nat) :=
  data v u M (d-j) offset j (scratch u offset old j) d target C
    (nonzero offset j oldNonzero) (guard offset d target j oldGuard) (output v M offset d target out j)
def H (v M offset d target : Nat) (out : List Bool) (j : Nat) :=
  heads (output v M offset d target out j)
noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)
def iterationBudget (u d C : Nat) := 2*d+20*u+39+16*(C+1)
def budget (u d C : Nat) := (d+1)*(iterationBudget u d C+3)+3

theorem output_succ (v M offset d target : Nat) (out : List Bool) (j : Nat) :
    output v M offset d target out (j+1)=output v M offset d target out j++emit v M offset d target j := by
  simp only [output,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.append_assoc]

theorem iteration_run (v u M offset d target C old : Nat) (oldNonzero oldGuard : Bool)
    (out : List Bool) (j : Nat) (hj : j≤d)
    (hfit : offset+d<2^u) (hd : d+1<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hMv : M≤2^v) (hmeta : 2*v+d+3≤C)
    (hC : CloseoutRowsModeElementary.budget v (d-j) M+1≤C) :
    Step body (iterationBudget u d C) (H v M offset d target out j)
      (A v u M offset d target C old oldNonzero oldGuard out j)
      (H v M offset d target out (j+1))
      (A v u M offset d target C old oldNonzero oldGuard out (j+1)) := by
  have raw:=body_run v u M (d-j) offset j (scratch u offset old j) d target C
    (nonzero offset j oldNonzero) (guard offset d target j oldGuard) (output v M offset d target out j)
    (by omega) (by omega) ht hscalar (by omega) hMv (by omega) hC
  have fit:=CloseoutRowsModeElementaryReusable.budget_le v (d-j) M C (by omega) hC
  have more:=raw.enlarge (show bodyBudget v u M (d-j) C ≤ iterationBudget u d C by
    unfold bodyBudget iterationBudget;omega)
  simpa only [A,H,scratch,nonzero,guard,show j+1≠0 by omega,if_false,Nat.add_sub_cancel,
    output_succ,emit,show d-j-1=d-(j+1) by omega] using more

theorem run (v u M offset d target C old : Nat) (oldNonzero oldGuard : Bool) (out : List Bool)
    (hfit : offset+d<2^u) (hd : d+1<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hMv : M≤2^v) (hmeta : 2*v+d+3≤C)
    (hC : ∀k≤d,CloseoutRowsModeElementary.budget v k M+1≤C) :
    Step machine (budget u d C)
      (Fin.addCases (H v M offset d target out 0) (fun _ : Fin 1=>1))
      (Fin.addCases (A v u M offset d target C old oldNonzero oldGuard out 0)
        (fun _ : Fin 1=>CompareMachine.word (d+1)))
      (Fin.addCases (H v M offset d target out (d+1)) (fun _ : Fin 1=>1))
      (Fin.addCases (A v u M offset d target C old oldNonzero oldGuard out (d+1))
        (fun _ : Fin 1=>CompareMachine.word (d+1))) := by
  apply PhysicalRepeatStep.run body (d+1) (iterationBudget u d C)
    (H v M offset d target out) (A v u M offset d target C old oldNonzero oldGuard out)
  intro j hj
  exact iteration_run v u M offset d target C old oldNonzero oldGuard out j (by omega)
    hfit hd ht hscalar hMv hmeta (hC (d-j) (by omega))

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindow
