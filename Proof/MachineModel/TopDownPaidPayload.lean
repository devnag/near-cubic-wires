import Proof.CaseAnalysis.RowsEstimatorPaidOwnedRun
import Proof.MachineModel.ClosureRawRowState

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidPayload
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount
open MatrixScoreBatch CompetitorCountMask
open CompetitorCrossScheduler (producer)
open P1Closure RecoveryRootRound
attribute [local irreducible] CompetitorCrossScheduler.producer Paid.warmMachine Paid.driver Paid.warm
  RawRowJoin.machine

def estimate : CompetitorValidity.Estimate := ⟨0,0,1⟩
noncomputable def tapes (a : WilliamsAlgorithm) := Paid.tapes a (producer a)
noncomputable def port (a : WilliamsAlgorithm) : Fin (tapes a) :=
  Paid.old a (producer a) (WarmPrepare.spare (producer a))
noncomputable def input (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  Paid.input a (producer a) row C (WarmFields.words row Q estimate 1 select) []

theorem empty_heads (a : WilliamsAlgorithm) :
    Paid.heads a (producer a) [] = (fun _=>0) := by
  funext i
  refine Fin.addCases (m:=WarmPrepare.tapes (producer a))
    (n:=ScannedClean.tapes a) (fun j=>?_) (fun j=>?_) i
  · simp [Paid.heads,WarmPrepare.heads]
  · simp only [Paid.heads,Fin.addCases_right]

theorem warm_budget_le (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : Nat)
    (hC : (Header.stream row).length≤C) (hQ : Q≤(EquationRow.request row).p) :
    Paid.warmBudget a row C Q ≤ ScannedClean.budget a row C+1+
      (8*Driver.value a row.d row.p row.cuts.length C+
        40*scalarWidth (EquationRow.request row) Q+74) := by
  have hf := Driver.fuel_bound a row C Q hC hQ
  have he := Warm.split_budget a row C Q
  unfold Paid.warmBudget WarmPrepared.budget WarmActual.budget Reuse.budget Reuse.afterBudget
  omega

end NearCubicWires.P1TopDownPaidPayload
