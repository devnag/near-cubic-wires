import Proof.Packets.ScalarFromCounter

/-! The delta window's actual binary width2W, obtained by two counted passes
on the retained W counter, with no precomputed doubled scalar. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarTwice
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine := Composition.machine ScalarFromCounter.machine ScalarFromCounter.count
def budget (u N : Nat) := 2*N*(4*u+5)+4*u+12

theorem add_run (u R base N : Nat) (hn : base+N<2^u) (hr : 2*u≤R) :
    Step ScalarFromCounter.count (N*(4*u+5)+3) ScalarFromCounter.heads
      (ScalarFromCounter.data u base R N) ScalarFromCounter.heads (ScalarFromCounter.data u (base+N) R N) := by
  have h:=PhysicalRepeatStep.run FramedIncrement.machine N (4*u+2)
    (fun _ _=>0) (fun i=>ScalarFromCounter.pair u (base+i) R)
    (fun i hi=>by
      have hh:=ScalarFromCounter.increment_run u (base+i) R (by omega) hr
      simpa only [Nat.add_assoc] using hh)
  have hf : N*((4*u+2)+3)+3=N*(4*u+5)+3 := by ring
  simpa only [hf,Nat.add_zero,ScalarFromCounter.count,ScalarFromCounter.heads,ScalarFromCounter.data] using h

theorem run (u old R N : Nat) (hn : 2*N<2^u) (hr : 2*u+1≤R) :
    Step machine (budget u N) ScalarFromCounter.heads (ScalarFromCounter.data u old R N)
      ScalarFromCounter.heads (ScalarFromCounter.data u (2*N) R N) := by
  have first:=ScalarFromCounter.run u old R N (by omega) hr
  have last:=add_run u R N N (by omega) (by omega)
  rw [show N+N=2*N by omega] at last
  have h:=first.seq last
  have hf : ScalarFromCounter.budget u N+1+(N*(4*u+5)+3)=budget u N := by
    unfold ScalarFromCounter.budget budget;ring
  rw [hf] at h
  exact h

theorem padded_run (u old R N : Nat) (hn : 2*N<2^u) (hr : 2*u+1≤R) :
    Step machine (budget u N) ScalarFromCounter.heads
      (fun i=>ZeroPadding.pad ((![R,0,R] : Fin 3→Nat) i) (ScalarFromCounter.data u old R N i)) ScalarFromCounter.heads
      (fun i=>ZeroPadding.pad ((![R,0,R] : Fin 3→Nat) i) (ScalarFromCounter.data u (2*N) R N i)) :=
  (run u old R N hn hr).pad (![R,0,R] : Fin 3→Nat)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarTwice
