import Proof.SourceAssembly.SourceStepsV5Inst
import Proof.SourceAssembly.SourceStepsV5b

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSteps
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- **THE STEPS HOLE at the V5 fill, generic in the onset**, from its per-instance facts. -/
def stepsV5At4 (selector : PCJ9eff70d512234a4c_Fixed.CyclicChoice.Laws) (compiler : PCJ9eff70d512234a4c_Fixed.Packets.CompilerLaws)
    (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector)
    (hxF : ∀ (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
      (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma),
      XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (G7 : FirstW.G7W selector xtra)
    (E : ∀ mask packets rows, SiteFam mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows) (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows)) (ParamsV4.fPW selector xtra mask packets rows) (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _ (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)))
    (EF : ∀ mask packets rows, EFFam mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows) (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows)) (ParamsV4.fPW selector xtra mask packets rows) (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _ (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)))
    (hsteps : ∀ mask packets rows, StepsFam4 mask packets rows compiler (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows) (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows)) (ParamsV4.fPW selector xtra mask packets rows) (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _ (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)) (ParamsV4.sfPW selector mask packets rows) (E mask packets rows) (EF mask packets rows))
    (hpen0 : ∀ mask packets rows, Pen0Fam4 mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows) (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows)) (ParamsV4.fPW selector xtra mask packets rows) (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _ (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)) (E mask packets rows) (EF mask packets rows))
    (hbridge : ∀ mask packets rows, BridgeFam4 mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows) (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows)) (ParamsV4.fPW selector xtra mask packets rows) (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _ (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)) (E mask packets rows) (EF mask packets rows)) :
    FillV5.StepsHoleV5 selector compiler xtra (FirstW.g7OfW selector xtra G7)
      (FirstW.firstW selector xtra G7) :=
  fun mask packets rows => stepsG2_of4 mask packets rows compiler (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows) (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows)) (ParamsV4.fPW selector xtra mask packets rows) (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _ (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)) (ParamsV4.sfPW selector mask packets rows) (E mask packets rows) (EF mask packets rows)
    (hsteps mask packets rows) (hpen0 mask packets rows) (hbridge mask packets rows)

end
end NearCubicWires.SourceSteps
end

