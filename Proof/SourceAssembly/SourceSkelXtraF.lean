import Proof.SourceAssembly.SourceSkelKeptW2
import Proof.SourceAssembly.SourceSkelWinW
import Proof.Packets.SrcInitFitV4

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
namespace NearCubicWires.SourceSkeleton.XtraF
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
open NearCubicWires.SourceSkeleton.Fill (XtraW)
open NearCubicWires.SourceSkeleton.FillV5 NearCubicWires.SourceSkeleton.FirstW
noncomputable section

def h7q (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (mode : Bool) (ph : Phase) : ℕ :=
  Classical.choose (NearCubicWires.SourceStart.InitFitV4.H7_IKc4 selector mask packets rows sources gamma hg hh p
    (plSite selector (ResWin.xtraW selector) mask packets rows sources gamma hg hh p mode ph)
    (LW selector mask packets rows sources gamma hg hh p) mode (SourceBudget.Params.tgOf sources gamma hg hh p))

/-- The H7 onset over all six `(mode, ph)`. -/
def q0H7 (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) : ℕ :=
  max (max (h7q selector mask packets rows sources gamma hg hh p false .penalty)
      (max (h7q selector mask packets rows sources gamma hg hh p false .moment)
        (h7q selector mask packets rows sources gamma hg hh p false .clause)))
    (max (h7q selector mask packets rows sources gamma hg hh p true .penalty)
      (max (h7q selector mask packets rows sources gamma hg hh p true .moment)
        (h7q selector mask packets rows sources gamma hg hh p true .clause)))

theorem h7q_le (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (mode : Bool) (ph : Phase) :
    h7q selector mask packets rows sources gamma hg hh p mode ph ≤ q0H7 selector mask packets rows sources gamma hg hh p := by
  unfold q0H7
  cases mode <;> cases ph
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

def xtraF (selector : CyclicChoice.Laws) : XtraW selector := fun mask packets rows s g hg hh p =>
  max (ResWin.xtraW selector mask packets rows s g hg hh p)
    (Classical.choose (SourceBudget.widthAt_ge_eventually s (kW selector mask packets rows s g hg hh p)
      (q0H7 selector mask packets rows s g hg hh p)))

theorem xtraF_residue (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (n : ℕ) (hn : xtraF selector mask packets rows sources gamma hg hh p ≤ n) :
    WorkspaceSelectedEntryBudget.envelope sources p (kW selector mask packets rows sources gamma hg hh p)
        (SourceSteps.rBsel sources p) n + 1 ≤
      2 ^ (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n -
        normalizedLiveCount (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)
          (LW selector mask packets rows sources gamma hg hh p)) :=
  ResWin.xtraW_spec selector mask packets rows sources gamma hg hh p n (le_trans (le_max_left _ _) hn)

theorem xtraF_width (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (n : ℕ) (hn : xtraF selector mask packets rows sources gamma hg hh p ≤ n) :
    q0H7 selector mask packets rows sources gamma hg hh p ≤
      C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n :=
  Classical.choose_spec (SourceBudget.widthAt_ge_eventually sources (kW selector mask packets rows sources gamma hg hh p)
    (q0H7 selector mask packets rows sources gamma hg hh p)) n (le_trans (le_max_right _ _) hn)

theorem xtraF_H7 (selector : CyclicChoice.Laws) (mask : MaskProducer)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)
    (n : ℕ) (hn : xtraF selector mask packets rows sources gamma hg hh p ≤ n) (mode : Bool) (ph : Phase)
    {d : Dims} {eX pX gW X T : ℕ}
    (pl : Place d eX pX gW (hRx4 selector mask packets rows sources gamma hg hh p)
      (SourceBudget.Params.hVN selector sources gamma hg hh p) X T) :
    ∀ b, b ≤ (C10PartsSchedule.thresholdFloor sources + 1) *
        (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n + 1) ^
          SourceBudget.Params.rB sources gamma hg hh p →
      InitS.initAllXCostE pl (LW selector mask packets rows sources gamma hg hh p) 1
          (SourceBudget.Params.cVcN selector sources gamma hg hh p) (sC sources gamma hg hh p) (rC sources gamma hg hh p)
          (pE sources gamma hg hh p) (pC sources gamma hg hh p) 3 1 (ldE sources gamma hg hh p) (ldC sources gamma hg hh p)
          mode (SourceBudget.Params.tgOf sources gamma hg hh p)
          (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n) b
          (dE sources gamma hg hh p) (dC sources gamma hg hh p) (cwE sources gamma hg hh p) (cwC sources gamma hg hh p)
          (NearCubicWires.SourceStart.MetaStepGF.metaCostG selector sources p packets (LW selector mask packets rows sources gamma hg hh p)
            (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n)) + 2 ≤
        (IKc4 selector mask packets rows sources gamma hg hh p (LW selector mask packets rows sources gamma hg hh p)).iT *
            RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p)
              (hRx4 selector mask packets rows sources gamma hg hh p + 1)
              (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n) +
          (IKc4 selector mask packets rows sources gamma hg hh p (LW selector mask packets rows sources gamma hg hh p)).iP *
            (C10PartsSchedule.widthAt sources (kW selector mask packets rows sources gamma hg hh p) n + 1) ^
              (IKc4 selector mask packets rows sources gamma hg hh p 0).iE :=
  Classical.choose_spec (NearCubicWires.SourceStart.InitFitV4.H7_IKc4 selector mask packets rows sources gamma hg hh p
    (plSite selector (ResWin.xtraW selector) mask packets rows sources gamma hg hh p mode ph)
    (LW selector mask packets rows sources gamma hg hh p) mode (SourceBudget.Params.tgOf sources gamma hg hh p))
    _ (le_trans (h7q_le selector mask packets rows sources gamma hg hh p mode ph)
      (xtraF_width selector mask packets rows sources gamma hg hh p n hn))

end
end NearCubicWires.SourceSkeleton.XtraF
end

