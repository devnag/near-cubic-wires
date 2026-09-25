import Proof.Packets.PacketsXDescendingWindowReady
import Proof.Packets.PacketsXDescendingWindowDegree

/-! One complete physical outer-window iteration: paid preparation,
descending inner antidiagonal, then retained binary-degree advance. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowScalar
open DescendingWindowSetup (H A)

noncomputable def machine := Composition.machine
  (Composition.machine DescendingWindowSetup.machine DescendingWindowReady.machine) DescendingWindowDegree.machine
def budget (u d C : Nat) := 4*C+8*u+2*d+29+DescendingWindow.budget u d C

theorem run (v u M a offset b old d target C : Nat) (oldNonzero oldGuard : Bool) (out : List Bool)
    (ha : a+1≤C) (hfit : offset+d<2^u) (hd : d+1<2^u) (ht : target<2^u) (hscalar : 2*u≤C)
    (hMv : M≤2^v) (hmeta : 2*v+d+3≤C)
    (hC : ∀k≤d,CloseoutRowsModeElementary.budget v k M+1≤C) :
    Step machine (budget u d C) (H out)
      (A v u M a offset b old d target C d oldNonzero oldGuard out)
      (H (DescendingWindow.output v M offset d target out (d+1)))
      (A v u M 0 offset (d+1) (CloseoutRowsModeShift.top u offset d) (d+1) target C (d+1)
        (decide (offset+d≠0)) (coefficient offset d d target)
        (DescendingWindow.output v M offset d target out (d+1))) := by
  have first := DescendingWindowSetup.run v u M a offset b old d target C oldNonzero oldGuard out
    ha (by omega) hscalar
  have middle := DescendingWindowReady.run v u M offset d target C old oldNonzero oldGuard out
    hfit hd ht hscalar hMv hmeta hC
  have middle' : Step DescendingWindowReady.machine (DescendingWindowReady.budget u d C)
      (H out) (A v u M d offset 0 old d target C (d+1) oldNonzero oldGuard out)
      (H (DescendingWindow.output v M offset d target out (d+1)))
      (A v u M 0 offset (d+1) (CloseoutRowsModeShift.top u offset d) d target C (d+1)
        (decide (offset+d≠0)) (coefficient offset d d target)
        (DescendingWindow.output v M offset d target out (d+1))) := by
    simpa only [DescendingWindowReady.H,DescendingWindowReady.A,H,A,DescendingWindow.H,
      DescendingWindow.A,DescendingWindow.scratch,DescendingWindow.nonzero,DescendingWindow.guard,
      Nat.sub_zero,if_true,show d+1≠0 by omega,if_false,Nat.add_sub_cancel,
      show d-(d+1)=0 by omega,DescendingWindow.output,List.range_zero,List.flatMap_nil,List.append_nil]
      using middle
  have last := DescendingWindowDegree.run v u M offset (d+1) (CloseoutRowsModeShift.top u offset d) d target C (d+1)
    (decide (offset+d≠0)) (coefficient offset d d target)
    (DescendingWindow.output v M offset d target out (d+1)) hd hscalar
  have whole := (first.seq middle').seq last
  convert whole using 1 <;> first | rfl | (unfold budget DescendingWindowReady.budget;omega)

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowOuter
