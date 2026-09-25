import Proof.SourceAssembly.SourcePhaseLater

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceParent
namespace NearCubicWires.SourceSteps
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

/-- A middle body tape `278 ≤ j < P` is the prologue's own port `j` (at `t+2+j`). -/
theorem body_mid {t P extra : Nat} (ht : 2 ≤ t) (hP : 302 ≤ P) (hsp : P+1155 ≤ extra) (j : Fin (t+2+extra-4))
    (h278 : 278 ≤ j.val) (hjP : j.val < P) :
    (ControllerSelectedLayout.body ht hP hsp j).val = t+2+j.val := by
  simp only [ControllerSelectedLayout.body, ControllerSelectedLayout.location]
  split_ifs <;> omega

/-- The continuation part of `finalBank` is blank. -/
theorem finalBank_fresh {t : Nat} (A : Fin t → List Bool) (L extra : Nat) (i : Fin (t+1+1+extra)) (hi : t + 2 ≤ i.val) :
    WorkspaceSelectedProgram.finalBank A L extra i = [] := by
  have he : i = Fin.natAdd (t+1+1) ⟨i.val - (t+1+1), by omega⟩ := Fin.ext (by simp only [Fin.natAdd]; omega)
  rw [he]
  simp only [WorkspaceSelectedProgram.finalBank, Fin.addCases_right]

section penalty

end penalty

end
end NearCubicWires.SourceSteps
end
