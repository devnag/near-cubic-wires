import Proof.MachineModel.OrdinaryTransitionTapeZero
import Proof.Packets.PhysicalRepeatStep

/-! A reusable fixed-width scalar producer. It physically zeroes the existing
framed binary allocation and increments it once for every mark of the actual
unary count driver. Scalar/count cursors and the rewind log are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarFromCounter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def pair (u n R : Nat) : Fin 2→List Bool := ![frame (binary u n),List.replicate R false]
def heads : Fin 3→Nat := Fin.addCases (m:=2) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>1)
def data (u n R N : Nat) : Fin 3→List Bool := Fin.addCases (m:=2) (n:=1) (motive:=fun _=>List Bool)
  (pair u n R) (fun _=>CompareMachine.word N)
def count := RepeatMachine.machine FramedIncrement.machine (fun _ _=>true)
def clear := TapeEmbedding.machine 1 TransitionTapeZero.machine
def machine := Composition.machine clear count
def budget (u N : Nat) := N*(4*u+5)+4*u+8

theorem binary_zero (u : Nat) : binary u 0=List.replicate u false := by
  induction u with
  | zero=>rfl
  | succ u ih=>simpa [binary,List.replicate_succ] using congrArg (List.cons false) ih

theorem increment_run (u n R : Nat) (hn : n+1<2^u) (hr : 2*u≤R) :
    Step FramedIncrement.machine (4*u+2) (fun _=>0) (pair u n R) (fun _=>0) (pair u (n+1) R) := by
  obtain ⟨r,hh,h0,h1,hheads,htime,_⟩:=FramedIncrement.increment_run u n R hn hr
  refine ⟨r,?_,?_,?_,htime⟩
  · have he : pair u n R = Fin.addCases (m:=1) (n:=1) (motive:=fun _=>List Bool)
        (fun _=>frame (binary u n)) (fun _=>List.replicate R false) := by
      funext i;fin_cases i <;>rfl
    simpa only [he, run, initialConfiguration] using hh
  · funext i;exact hheads i
  · funext i;fin_cases i
    · exact h0
    · exact h1

theorem count_run (u R N : Nat) (hn : N<2^u) (hr : 2*u≤R) :
    Step count (N*(4*u+5)+3) heads (data u 0 R N) heads (data u N R N) := by
  have h:=PhysicalRepeatStep.run FramedIncrement.machine N (4*u+2)
    (fun _ _=>0) (fun i=>pair u i R)
    (fun i hi=>increment_run u i R (by omega) hr)
  have he : N*((4*u+2)+3)+3=N*(4*u+5)+3 := by ring
  rw [he] at h
  exact h

theorem clear_run (u old R N : Nat) (hr : 2*u+1≤R) :
    Step clear (4*u+4) heads (data u old R N) heads (data u 0 R N) := by
  have h:=Step.of_ready (TransitionTapeZero.zero_ready (binary u old) R (by simpa [binary_length] using hr))
  simp only [binary_length] at h
  rw [←binary_zero u] at h
  exact h.embed (fun _ : Fin 1=>1) (fun _=>CompareMachine.word N)

theorem run (u old R N : Nat) (hn : N<2^u) (hr : 2*u+1≤R) :
    Step machine (budget u N) heads (data u old R N) heads (data u N R N) := by
  have h:=(clear_run u old R N hr).seq (count_run u R N hn (by omega))
  have he : (4*u+4)+1+(N*(4*u+5)+3)=budget u N := by unfold budget;omega
  rw [he] at h
  exact h

/-- Padded form accepts and returns the existing common-R scalar/count slots. -/
theorem padded_run (u old R N : Nat) (hn : N<2^u) (hr : 2*u+1≤R) :
    Step machine (budget u N) heads
      (fun i=>ZeroPadding.pad ((![R,0,R] : Fin 3→Nat) i) (data u old R N i)) heads
      (fun i=>ZeroPadding.pad ((![R,0,R] : Fin 3→Nat) i) (data u N R N i)) :=
  (run u old R N hn hr).pad (![R,0,R] : Fin 3→Nat)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarFromCounter
