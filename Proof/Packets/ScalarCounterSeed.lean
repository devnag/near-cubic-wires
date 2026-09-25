import Proof.Packets.ScalarFromCounter
import Proof.Rows.PhysicalFocusBoundary

/-! Runtime scalar width physically allocates a zero binary frame. The width
counter and rewind reserve are retained; the output begins as blank capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarCounterSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def slots : Fin 2→Fin 3 := ![1,2]
def machine := Composition.machine (TapeEmbedding.machine 1 UnaryFrameMachine.machine)
  (RecoveryFocus.machine slots TransitionTapeZero.machine)
def heads : Fin 3→Nat := ![1,0,0]
def data (u R : Nat) (out : List Bool) : Fin 3→List Bool :=
  ![CompareMachine.word u,out,List.replicate R false]
def budget (u : Nat) := 8*u+7

theorem run (u R : Nat) (hr : 2*u+1≤R) :
    Step machine (budget u) heads (data u R []) heads
      (data u R (frame (SignedSortKey.binary u 0))) := by
  obtain ⟨r,rr,rf,_,_⟩:=UnaryFrameMachine.unary_frame_run u
  have first:= (Step.of_run rr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)).embed
    (fun _ : Fin 1=>0) (fun _=>List.replicate R false)
  have first' : Step (TapeEmbedding.machine 1 UnaryFrameMachine.machine) (4*u+2)
      heads (data u R []) heads (data u R (frame (List.replicate u true))) := by
    convert first using 1 <;> (funext i;fin_cases i <;>rfl)
  have hz:=Step.of_ready (TransitionTapeZero.zero_ready (List.replicate u true) R (by simpa using hr))
  simp only [List.length_replicate,←ScalarFromCounter.binary_zero u] at hz
  have last:=PhysicalFocusBoundary.focus hz slots (by decide) heads heads
    (data u R (frame (List.replicate u true))) (data u R (frame (SignedSortKey.binary u 0)))
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
    (by intro i away;fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl))
  have h:=first'.seq last
  have he : (4*u+2)+1+(4*u+4)=budget u := by unfold budget;omega
  rw [he] at h
  exact h

theorem padded_run (u R : Nat) (hr : 2*u+1≤R) :
    Step machine (budget u) heads
      (fun i=>ZeroPadding.pad ((![R,R,0] : Fin 3→Nat) i) (data u R [] i)) heads
      (fun i=>ZeroPadding.pad ((![R,R,0] : Fin 3→Nat) i) (data u R (frame (SignedSortKey.binary u 0)) i)) :=
  (run u R hr).pad (![R,R,0] : Fin 3→Nat)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarCounterSeed
