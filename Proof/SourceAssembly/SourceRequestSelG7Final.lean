import Proof.SourceAssembly.SourceRequestSelLoopSite
import Proof.SourceAssembly.SourceFactorSelFields

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open NearCubicWires.SourceRequest.SelLocal (resW resWS)
open NearCubicWires.SourceRequest.CurContract (curBig rhoW)
open NearCubicWires.SourceRequest.TermReader (rawTerms)
open NearCubicWires.SourceRequest.LitInfo (litCost)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
namespace NearCubicWires.SourceRequest.SelG7Final
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
open NearCubicWires.SourceRequest.SelWinCore NearCubicWires.SourceRequest.SelWinSite NearCubicWires.SourceRequest.SelWinLoop
open NearCubicWires.SourceRequest.SelLoopSite
open NearCubicWires.SourceRequest.SelG7Spec (g7costW)
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes P1TopDown.WorkspaceSelectedAdmission.originalTapes
  P1TopDown.WorkspaceSelectedEntry.size RepairSource.SelectedRecoveryIntegration.outer

section v5
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p

theorem hF_site (L target tg den n : Nat) (x : BitInput n) (bits : List Bool) (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
    (ci : Fin (2 ^ ((RepairSource.CloseoutLanguage.selectedPCPP sources).output
      (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauseBits))
    (hden : 1 ≤ den) (m : Nat)
    (hr : Admission.RequestAdmitted den p.clauseDegree tg (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m))
    (hqm : (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).q = C10PartsSchedule.widthAt sources 𝔨 n)
    (hL : (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).liveScale = L) :
    Fields.cost (header mode (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits)).arity L target (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m).length)
        (Fields.nSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) (Fields.sSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m))
        (Fields.tSlots (decompositionOf sources) mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) ≤ 1000 * (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n) + 1) := by
  have hY := YbFit.Yb_le_meta selector sources p packets L (decompositionOf sources) hden _ hr hL
  rw [hqm] at hY
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := sqv_ge selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg (C10PartsSchedule.widthAt sources 𝔨 n)
  exact NearCubicWires.SourceFactorSel.FieldsGF.fields_le (decompositionOf sources) L target mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)
    (FactorLoop.factorsAt_le (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m) _ _ (hY.trans s9)

theorem g7_windows_final (L target tg den n : Nat)
    (hn : g7OnsetF selector mask packets rows sources gamma hg hh p L target tg ≤ n)
    (x : BitInput n) (bits : List Bool) (hlen : 16 * bits.length ≤ n) (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
    (ci : Fin (2 ^ ((RepairSource.CloseoutLanguage.selectedPCPP sources).output
      (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauseBits))
    (hden : 1 ≤ den)
    (hread : SourceRequest.CoordBridge.CoordReads mode
      (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) bits)
    (hadm : ∀ m, m ≤ (monomials (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci).length →
      Admission.RequestAdmitted den p.clauseDegree tg (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨
        (PolynomialClock.ordinaryClock 𝔨) p den x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits)
        ph ci L target mode m) ∧
      (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).q =
          C10PartsSchedule.widthAt sources 𝔨 n ∧
      (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).liveScale = L)
    (Rc : Nat) (hRc : RuntimeShape.tableClass L 0 (C10PartsSchedule.widthAt sources 𝔨 n) ≤ Rc) :
    G7Win sources mask (NearCubicWires.SourceStart.MetaRun.MBof selector sources p packets L (C10PartsSchedule.widthAt sources 𝔨 n))
      (RepairSource.CloseoutLanguage.selectedPCPP sources)
      (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))
      (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits)
      bits ph ci L target mode Rc (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)
      (NearCubicWires.SourceSkeleton.InitS.cwidOf mode (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)))
      (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
        NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p)
      (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
        NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p)
      (20 * sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n) + 50)
      (SelCoefV.VbF sources 𝔨 p n)
      (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
        NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p)
      (SourceBudget.wCap (C10PartsSchedule.widthAt sources 𝔨 n))
      (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) :=
  g7_windows_siteF selector xtra mask packets rows sources gamma hg hh p L target tg den n hn x bits hlen mode ph ci hden hread hadm
    (fun m hm => hF_site selector xtra mask packets rows sources gamma hg hh p L target tg den n x bits mode ph ci hden m (hadm m hm).1 (hadm m hm).2.1 (hadm m hm).2.2) Rc hRc

theorem g7cost_final (L target tg den n : Nat)
    (hn : g7OnsetF selector mask packets rows sources gamma hg hh p L target tg ≤ n)
    (x : BitInput n) (bits : List Bool) (hlen : 16 * bits.length ≤ n) (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
    (ci : Fin (2 ^ ((RepairSource.CloseoutLanguage.selectedPCPP sources).output
      (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauseBits))
    (hden : 1 ≤ den) (m : Nat)
    (hr : Admission.RequestAdmitted den p.clauseDegree tg (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨
        (PolynomialClock.ordinaryClock 𝔨) p den x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits)
        ph ci L target mode m))
    (hqm : (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).q =
          C10PartsSchedule.widthAt sources 𝔨 n)
    (hL : (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).liveScale = L) :
    g7costW sources mask (NearCubicWires.SourceStart.MetaRun.MBof selector sources p packets L (C10PartsSchedule.widthAt sources 𝔨 n))
        (RepairSource.CloseoutLanguage.selectedPCPP sources)
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))
        ci (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
          (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) bits ph L target
        (NearCubicWires.SourceSkeleton.InitS.cwidOf mode (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)))
        (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p)
        (C10PartsSchedule.entryWidthSchedule sources 𝔨 𝔯 n)
        (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p)
        (SourceBudget.wCap (C10PartsSchedule.widthAt sources 𝔨 n))
        (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) mode m ≤
      RuntimeShape.tableClass L 0 (C10PartsSchedule.widthAt sources 𝔨 n) :=
  g7cost_tableF selector xtra mask packets rows sources gamma hg hh p L target tg den n hn x bits hlen mode ph ci hden m hr hqm hL
    (hF_site selector xtra mask packets rows sources gamma hg hh p L target tg den n x bits mode ph ci hden m hr hqm hL)

end v5

end
end NearCubicWires.SourceRequest.SelG7Final
end
