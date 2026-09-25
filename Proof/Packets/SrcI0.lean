import Proof.Packets.SrcYSite0
import Proof.SourceAssembly.SourceSkelXtraF

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest NearCubicWires.SourceConstruction.Bridge
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase

namespace NearCubicWires.SourceStart.YSite
noncomputable section

/-! ## 1. I0 -/

section i0
open NearCubicWires.SourceConstruction.InitRun
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

theorem i0_site (n : ℕ) (hn : XtraF.xtraF selector mask packets rows sources gamma hg hh p ≤ n) (mode : Bool) (ph : Phase)
    {d : Dims} {eX pX gW X T : ℕ}
    (pl : Place d eX pX gW (ClassV4.hRx4 selector mask packets rows sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p) X T)
    (b : ℕ) (hb : b ≤ (C10PartsSchedule.thresholdFloor sources + 1) *
        (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n + 1) ^ SourceBudget.Params.rB sources gamma hg hh p) :
    ((ClassV4.siteI4 selector mask packets rows).at sources gamma hg hh p (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p)
        (ParamsV4.kW selector mask packets rows sources gamma hg hh p)).In 4 (ClassV4.siteL4 selector mask packets rows sources gamma hg hh p) n
      (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)
      (InitS.initAllXCostE pl (ParamsV4.LW selector mask packets rows sources gamma hg hh p) 1
          (SourceBudget.Params.cVcN selector sources gamma hg hh p) (Params.sC sources gamma hg hh p) (Params.rC sources gamma hg hh p)
          (Params.pE sources gamma hg hh p) (Params.pC sources gamma hg hh p) 3 1 (Params.ldE sources gamma hg hh p) (Params.ldC sources gamma hg hh p)
          mode (SourceBudget.Params.tgOf sources gamma hg hh p)
          (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n) b
          (Params.dE sources gamma hg hh p) (Params.dC sources gamma hg hh p) (Params.cwE sources gamma hg hh p) (Params.cwC sources gamma hg hh p)
          (NearCubicWires.SourceStart.MetaStepGF.metaCostG selector sources p packets (ParamsV4.LW selector mask packets rows sources gamma hg hh p)
            (C10PartsSchedule.widthAt sources (ParamsV4.kW selector mask packets rows sources gamma hg hh p) n)) + 2) :=
  SourceBudget.Params.IFam_site (ClassV4.siteR4 selector mask packets rows) (ClassV4.IKc4 selector mask packets rows)
    (ClassV4.siteL4 selector mask packets rows) sources gamma hg hh p _ n _
    (XtraF.xtraF_H7 selector mask packets rows sources gamma hg hh p n hn mode ph pl b hb)

end i0

/-! ## 2. `layF_hMB` -/

section hmb
variable (selector : CyclicChoice.Laws) (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
  (ph : Phase)
  (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
  (L : Nat)

set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity

theorem layF_hMB (C degree den' : ℕ) (hden0 : SourceSkeleton.layDen0 sources degree tgtC L ≤ den')
    (hq0 : SourceSkeleton.layOnset sources degree tgtC L ≤ vQ)
    (hA : ∀ j, Admission.Admitted den' degree (SourceRequest.FactorLoop.factorsAt coordC ph ci j))
    (h201 : 201 * normalizedLiveCount vQ L ≤ vQ) (capsAt : ℕ → RowCaps)
    (hcapsE : ∀ m, capsAt m = SourceSkeleton.capsU (SourceBudget.Pow2.hFOf2 selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.cCOf2 selector sources p L (C10PartsSchedule.widthAt sources k n))
      (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.rROf2 selector sources p packets (C10PartsSchedule.widthAt sources k n)))
    (hCe : C = SourceBudget.Params.COf selector sources p (C10PartsSchedule.widthAt sources k n)) (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n) (m : ℕ) :
    SLoad.Setup.metaBits
        (SourceSkeleton.layoutAtOf sources selector coordC ph ci L tgtC modeC
          (LayRP.layF selector sources coordC ph ci L tgtC modeC C degree den' hden0 hq0 hA h201) m).w
        (SourceSkeleton.layoutAtOf sources selector coordC ph ci L tgtC modeC
          (LayRP.layF selector sources coordC ph ci L tgtC modeC C degree den' hden0 hq0 hA h201) m).degree
        (SourceSkeleton.layoutAtOf sources selector coordC ph ci L tgtC modeC
          (LayRP.layF selector sources coordC ph ci L tgtC modeC C degree den' hden0 hq0 hA h201) m).C (capsAt m) =
      NearCubicWires.SourceStart.MetaRun.MBof selector sources p packets L (C10PartsSchedule.widthAt sources k n) := by
  rw [layoutAtOf_w, layoutAtOf_degree, layoutAtOf_C, hcapsE m, LayRP.layF_w, LayRP.layF_degree, LayRP.layF_C, hCe]
  show SLoad.Setup.metaBits (SourceBudget.wA vQ L) (Admission.uniformDeg vQ L) (SourceBudget.Params.COf selector sources p (C10PartsSchedule.widthAt sources k n))
      (SourceSkeleton.capsU (SourceBudget.Pow2.hFOf2 selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.cCOf2 selector sources p L (C10PartsSchedule.widthAt sources k n))
        (SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n)) (SourceBudget.Pow2.rROf2 selector sources p packets (C10PartsSchedule.widthAt sources k n))) = _
  rw [Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x oracleC hcut]
  rfl

end hmb

end
end NearCubicWires.SourceStart.YSite
end

