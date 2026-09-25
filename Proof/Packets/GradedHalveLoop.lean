import Proof.Packets.GradedHalveRound

/-! Physical iteration of the reusable ceiling-halver with the actual unary
quotient driver. Its zero case executes the same fixed Repeat machine. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine := RepeatMachine.machine GradedHalveRound.round (fun _ _=>true)
def heads : Fin 7→Nat := Fin.addCases (m:=6) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>1)
def data (R n Q : Nat) : Fin 7→List Bool :=
  Fin.addCases (m:=6) (n:=1) (motive:=fun _=>List Bool) (GradedHalveRound.layout R n)
    (fun _=>CompareMachine.word Q)
def budget (R Q : Nat) := Q*(8*R+22)+3

theorem run (R n Q : Nat) (hr : n+1≤R) :
    Step machine (budget R Q) heads (data R n Q) heads
      (data R (GradedHalveRound.halve^[Q] n) Q) := by
  have round (i : Nat) : Step GradedHalveRound.round (GradedHalveRound.roundBudget R)
      (fun _=>0) (GradedHalveRound.layout R (GradedHalveRound.halve^[i] n))
      (fun _=>0) (GradedHalveRound.layout R (GradedHalveRound.halve^[i+1] n)) := by
    obtain ⟨r,rr,rt,rh,rs⟩:=GradedHalveRound.round_run R (GradedHalveRound.halve^[i] n)
      (GradedHalveRound.round_iterate_capacity R n i hr)
    refine ⟨r,rr,funext rh,?_,rs⟩
    simpa only [Function.iterate_succ_apply'] using rt
  have h:=PhysicalRepeatStep.run GradedHalveRound.round Q (GradedHalveRound.roundBudget R)
    (fun _ _=>0) (fun i=>GradedHalveRound.layout R (GradedHalveRound.halve^[i] n)) (fun i _=>round i)
  simpa only [machine,budget,heads,data,GradedHalveRound.roundBudget,show 8*R+19+3=8*R+22 by omega,
    Function.iterate_zero,Function.id_def] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedHalveLoop
