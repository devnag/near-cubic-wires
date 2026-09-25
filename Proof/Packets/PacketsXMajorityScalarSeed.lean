import Proof.Packets.PacketsXCycleTableSeed
import Proof.Rows.PhysicalDriverMoves
import Proof.Packets.PhysicalRewind
import Proof.Packets.MajorityThreshold

/-! Scalar seeds for majority are executed from their unary inputs and empty
scratch tapes. The exponential driver and binary counter are not supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Completion.MajorityScalarSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed.Materializer Theorem25Completion
noncomputable section

def powerMachine:=Composition.machine CycleTableSeed.machine (PhysicalDriverMoves.machine 21 .left)
def powerBudget (N : Nat):=CycleTableSeed.budget N+2

theorem power_run (N : Nat) : ∃ out,
    Step powerMachine (powerBudget N) (fun _=>0) (CycleTableSeed.input N) (fun _=>0) out ∧
    out 2=frame (SignedSortKey.binary N 0) ∧
    out 19=CompareMachine.word (2^N-1) ∧ out 17=UnaryTemplate.tape (2^N) := by
  obtain ⟨out,h,ha,_,hb,hc⟩:=CycleTableSeed.run N
  have ret:=PhysicalDriverMoves.run HeadMove.left CycleTableSeed.heads out
  have hz : (fun i=>HeadMove.left.apply (CycleTableSeed.heads i))=(fun _=>0) := by
    funext i
    by_cases hi : i=19 <;>simp [CycleTableSeed.heads,HeadMove.apply,hi]
  refine ⟨out,?_,ha,hb,hc⟩
  simpa only [powerMachine,powerBudget,Nat.add_assoc] using (h.seq ret).congr hz rfl

def thresholdMachine:=Rewind.machine MajorityThreshold.machine
theorem threshold_run (N : Nat) : ∃ k≤N+2,
    Step thresholdMachine (2*N+6) (fun _=>0) ![CompareMachine.word N,[],[]]
      (fun _=>0) ![CompareMachine.word N,CompareMachine.word ((N+1)/2),List.replicate k false] := by
  obtain ⟨k,hk,h⟩:=PhysicalColdRewind.run (MajorityThreshold.run N)
  refine ⟨k,hk,?_⟩
  have hb : 2*(N+2)+2=2*N+6 := by omega
  rw [hb] at h
  exact (h.congr_in rfl (by funext i;fin_cases i <;>rfl)).congr rfl
    (by funext i;fin_cases i <;>rfl)

end
end Completion.MajorityScalarSeed
