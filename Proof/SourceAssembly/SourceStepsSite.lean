import Proof.Packets.SrcEntryWFam
import Proof.SourceAssembly.SourceStepsV5At4
import Proof.SourceAssembly.SourceStepsC2v5Hyps

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSteps
open NearCubicWires.SourceSkeleton.FirstW NearCubicWires.SourceStart.EntryW
noncomputable section

section site
variable (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector)
  (G7 : FirstW.G7W selector xtra)

set_option hygiene false in
local notation "CODE" => skelFamilyR mask packets rows (FillV5.resPV5 selector mask packets rows)
  (resChoiceX_ge (restDataOf (ParamsR.gWR selector mask packets rows)) (FillV5.xRV5 selector mask packets rows))
  (ParamsV4.fPW selector xtra mask packets rows)
  (refillFam3 mask packets rows (ParamsR.gWR selector mask packets rows) (FillV5.xRV5 selector mask packets rows) (FillV5.hxRV5 selector mask packets rows) _
    (FirstW.g7OfW selector xtra G7 mask packets rows)) (FirstW.firstW selector xtra G7 mask packets rows)
set_option hygiene false in
local notation "𝔉" => forcedChoices mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows)
set_option hygiene false in
local notation "denI" => (𝔉).capIndex sources gamma hg hh p + 1
set_option hygiene false in
local notation "modeI" => PCJ374c44bb8b7f47d9_.S.mode sources p (denI) (Nat.succ_pos _) (kSite selector xtra mask packets rows sources gamma hg hh p)
  (rSite selector xtra mask packets rows sources gamma hg hh p) (scrSite selector mask packets rows sources gamma hg hh p) n x bits hp

/-- **The site's phase entry lists** (`EFFam`): the clause entries at the live scale `LW`. -/
def EFSite (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) :
    EFFam mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (CODE) :=
  fun sources gamma hg hh p n x bits hp => fun ph' =>
    phaseE sources p (denI) (kSite selector xtra mask packets rows sources gamma hg hh p) x bits (modeI) ph' (ParamsV4.LW selector mask packets rows sources gamma hg hh p)

noncomputable def stepsHoleSite
    (hxF : ∀ (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
      (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma),
      XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (hx : ∀ (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
      (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma),
      res284W selector mask packets rows sources gamma hg hh p ≤ xtra mask packets rows sources gamma hg hh p)
    (hsteps : ∀ (mask : MaskProducer) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector),
      StepsFam4 mask packets rows compiler (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (CODE)
        (ParamsV4.sfPW selector mask packets rows) (EWFam selector xtra mask packets rows (CODE)) (EFSite selector xtra G7 mask packets rows)) :
    FillV5.StepsHoleV5 selector compiler xtra (FirstW.g7OfW selector xtra G7) (FirstW.firstW selector xtra G7) :=
  stepsV5At4 selector compiler xtra hxF G7 (fun mask packets rows => EWFam selector xtra mask packets rows (CODE))
    (fun mask packets rows => EFSite selector xtra G7 mask packets rows) hsteps
    (fun mask packets rows => pen0Fam4_siteX selector xtra mask packets rows (CODE) (EFSite selector xtra G7 mask packets rows) (hx mask packets rows))
    (fun mask packets rows => bridgeFam4_of mask packets rows (FillV5.resPV5 selector mask packets rows) (ParamsV4.fPW selector xtra mask packets rows) (CODE)
      (EWFam selector xtra mask packets rows (CODE)) (EFSite selector xtra G7 mask packets rows)
      (bridgeFam_site selector xtra mask packets rows (CODE) (EFSite selector xtra G7 mask packets rows)))

end site

end
end NearCubicWires.SourceSteps
end

