import Proof.Packets.BudgetSiteOrder
import Proof.SourceAssembly.SourceSkelLoop

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- **THE J5 HOLE** for any code family. -/
def FitsHoleG (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (res : ResChoice) (f : FreeChoices) (code : SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res f)) (sf : SiteFuelFam) : Prop :=
  ∀ (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) (n : Nat) (x : BitInput n) (bits : List Bool),
    let ch := forcedChoices mask packets rows res f
    let C := ControllerCappedRuntime.continuation sources p (ch.capIndex sources gamma hg hh p+1)
      (ch.remainingDegree sources gamma hg hh p) (ch.r sources gamma hg hh p)
      (ch.base sources gamma hg hh p) (ch.scratch sources gamma hg hh p)
      (code.site sources gamma hg hh p) (ch.remainingFuel sources gamma hg hh p)
    (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).onset ≤ n →
    (ControllerCappedSelected.workerData sources p (ch.capIndex sources gamma hg hh p+1)
      (Nat.succ_pos (ch.capIndex sources gamma hg hh p))
      (ControllerCappedSelected.programData (ch.capIndex sources gamma hg hh p+1) C)).passed n x bits = true →
    PCJ374c44bb8b7f47d9_.branchFuel
      (costOf sources p (ch.capIndex sources gamma hg hh p+1) C.k (ch.r sources gamma hg hh p) n x bits
        (sf sources gamma hg hh p n x bits))
      (ch.widths sources gamma hg hh p n x bits) + 2 ≤ ch.remainingFuel sources gamma hg hh p n

section j5

end j5

end
end NearCubicWires.SourceSkeleton
end
