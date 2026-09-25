import Proof.SourceAssembly.SourceRequestSelWinOnsetW
import Proof.SourceAssembly.SourceRequestSelLoopCost
import Proof.SourceAssembly.SourceFactorSelH5

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
namespace NearCubicWires.SourceRequest.SelLoopSite
open NearCubicWires.SourceFactorSel NearCubicWires.SourceFactorSel.AtS
open NearCubicWires.SourceRequest.SelWinCore NearCubicWires.SourceRequest.SelWinSite NearCubicWires.SourceRequest.SelWinLoop
open NearCubicWires.SourceRequest.SelG7Spec (g7costW)
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes P1TopDown.WorkspaceSelectedAdmission.originalTapes
  P1TopDown.WorkspaceSelectedEntry.size RepairSource.SelectedRecoveryIntegration.outer

theorem le_capacity (N : Nat) : N ≤ RepairOrdinary.CloseoutRowsCircuitCapacity.capacity N := by
  unfold RepairOrdinary.CloseoutRowsCircuitCapacity.capacity
  have h : N + 2 ≤ (N + 2) ^ 26 := Nat.le_self_pow (by decide) (N + 2)
  omega

/-! ## The xtra-free onset at the loop's constants -/

section w
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

def g7OnsetF (L target tg : Nat) : Nat :=
  SelWinOnsetW.g7OnsetW selector mask packets rows sources gamma hg hh p L target tg 0 0 (SelLoopCost.loopC (decompositionOf sources)) (SelLoopCost.slotE (decompositionOf sources)) (SelWinOnsetW.hkW selector mask packets rows sources gamma hg hh p 0 (by decide))

end w

section v5
variable (selector : CyclicChoice.Laws) (xtra : NearCubicWires.SourceSkeleton.Fill.XtraW selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

set_option hygiene false in
local notation "𝔨" => NearCubicWires.SourceSkeleton.FirstW.kSite selector xtra mask packets rows sources gamma hg hh p
set_option hygiene false in
local notation "𝔯" => NearCubicWires.SourceSkeleton.FirstW.rSite selector xtra mask packets rows sources gamma hg hh p

theorem g7_windows_siteS (L target tg cL dL wCs wEs : Nat) (hk : max 25 dL + 1 ≤ 𝔨 + 2) (den n : Nat)
    (hn : g7OnsetQ selector xtra mask packets rows sources gamma hg hh p L target tg cL dL wCs wEs hk ≤ n)
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
    (hloop : ∀ m, m ≤ (monomials (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci).length →
      loopW sources (RepairSource.CloseoutLanguage.selectedPCPP sources)
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))
        ci (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
          (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph L target
        (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p)
        (SourceBudget.wCap (C10PartsSchedule.widthAt sources 𝔨 n))
        (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) mode m ≤ cL * (n + 1) ^ dL + wCs * (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n) + 1) ^ wEs)
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
        (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) := by
  have hE := (g7OnsetQ_spec selector xtra mask packets rows sources gamma hg hh p L target tg cL dL wCs wEs hk n hn).trans hRc
  have hdw := SelDWin.dwin_site sources gamma hg hh p (C10PartsSchedule.widthAt sources 𝔨 n) mode
  have h4L : 4 ≤ SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
      (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n) := by
    unfold SourceBudget.ldCap
    exact (NearCubicWires.SourceSkeleton.Params.ldC_ge sources gamma hg hh p).trans
      (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))
  have hcap := cap_le_site sources 𝔨 p n x bits
  have hb := b_le_site sources 𝔨 n 𝔯
  have hvb := vb_le_site sources 𝔨 p n
  have hcw1 : 1 ≤ NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p * ((C10PartsSchedule.widthAt sources 𝔨 n) + 1) ^
      NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p :=
    Nat.mul_pos (cwC_pos sources gamma hg hh p) (Nat.one_le_pow _ _ (by omega))
  have hJL := coord_len_site sources 𝔨 p den n x bits
    (NearCubicWires.ComponentwiseBranchExtraction.literalIndex
      (((RepairSource.CloseoutLanguage.selectedPCPP sources).output
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
          (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauses ci).left)
  have hJR := coord_len_site sources 𝔨 p den n x bits
    (NearCubicWires.ComponentwiseBranchExtraction.literalIndex
      (((RepairSource.CloseoutLanguage.selectedPCPP sources).output
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
          (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauses ci).right)
  have hsq := sqv_ge selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg (C10PartsSchedule.widthAt sources 𝔨 n)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hsq
  have hcwid := le_trans (show NearCubicWires.SourceSkeleton.InitS.cwidOf mode (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) ≤ NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p *
        ((C10PartsSchedule.widthAt sources 𝔨 n) + 1) ^ NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p by have := hdw.2.2.2.2; omega) s4
  have h4D : 4 ≤ NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p * ((C10PartsSchedule.widthAt sources 𝔨 n) + 1) ^
      NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p := by
    have := hdw.2.2.2.1; omega
  have hqS := q_le_sqv selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg (C10PartsSchedule.widthAt sources 𝔨 n)
  refine winCoreQ sources mask _ _ _ _ bits ph ci L target mode Rc _ _ _ _ _ _ _ _ n (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n)) cL dL wCs wEs hread (by omega)
    s10 (hcap.trans s1) (le_trans (Nat.add_le_add_right (Nat.add_le_add hJL hJR) 1) (le_trans (by omega) s2)) hcwid
    s3 s4 h4D s5 s6 (hb.trans s7) (hvb.trans s8) hcw1
    (SelCoefV.hcoef_site sources 𝔨 p den n x bits _ (NearCubicWires.SourceSkeleton.Params.coefficientAt_le_cw sources gamma hg hh p (C10PartsSchedule.widthAt sources 𝔨 n)))
    (SelCoefV.hcoefV_site sources 𝔨 p den n x bits) ?_ hloop hE
  intro m hm
  obtain ⟨hr, hqm, hL⟩ := hadm m hm
  have hY := YbFit.Yb_le_meta selector sources p packets L (decompositionOf sources) hden _ hr hL
  rw [hqm] at hY
  exact hY.trans s9

theorem g7cost_tableS (L target tg cL dL wCs wEs : Nat) (hk : max 25 dL + 1 ≤ 𝔨 + 2) (den n : Nat)
    (hn : g7OnsetQ selector xtra mask packets rows sources gamma hg hh p L target tg cL dL wCs wEs hk ≤ n)
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
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).liveScale = L)
    (hloop : loopW sources (RepairSource.CloseoutLanguage.selectedPCPP sources)
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))
        ci (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
          (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph L target
        (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p)
        (SourceBudget.wCap (C10PartsSchedule.widthAt sources 𝔨 n))
        (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) mode m ≤ cL * (n + 1) ^ dL + wCs * (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n) + 1) ^ wEs) :
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
      RuntimeShape.tableClass L 0 (C10PartsSchedule.widthAt sources 𝔨 n) := by
  have hE := g7OnsetQ_spec selector xtra mask packets rows sources gamma hg hh p L target tg cL dL wCs wEs hk n hn
  have hdw := SelDWin.dwin_site sources gamma hg hh p (C10PartsSchedule.widthAt sources 𝔨 n) mode
  have hcap := cap_le_site sources 𝔨 p n x bits
  have hb := b_le_site sources 𝔨 n 𝔯
  have hvb := vb_le_site sources 𝔨 p n
  have hcw1 : 1 ≤ NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p * ((C10PartsSchedule.widthAt sources 𝔨 n) + 1) ^
      NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p :=
    Nat.mul_pos (cwC_pos sources gamma hg hh p) (Nat.one_le_pow _ _ (by omega))
  have hJL := coord_len_site sources 𝔨 p den n x bits
    (NearCubicWires.ComponentwiseBranchExtraction.literalIndex
      (((RepairSource.CloseoutLanguage.selectedPCPP sources).output
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
          (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauses ci).left)
  have hJR := coord_len_site sources 𝔨 p den n x bits
    (NearCubicWires.ComponentwiseBranchExtraction.literalIndex
      (((RepairSource.CloseoutLanguage.selectedPCPP sources).output
        (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
          (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauses ci).right)
  have hY := YbFit.Yb_le_meta selector sources p packets L (decompositionOf sources) hden _ hr hL
  rw [hqm] at hY
  have hsq := sqv_ge selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg (C10PartsSchedule.widthAt sources 𝔨 n)
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hsq
  have hcwid := le_trans (show NearCubicWires.SourceSkeleton.InitS.cwidOf mode (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) ≤ NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p *
        ((C10PartsSchedule.widthAt sources 𝔨 n) + 1) ^ NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p by have := hdw.2.2.2.2; omega) s4
  have hqS := q_le_sqv selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg (C10PartsSchedule.widthAt sources 𝔨 n)
  have hc := winCostQ sources mask _ _ _ ci _ bits ph L target _ _ _ _ _ _ _ _ n (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n)) cL dL wCs wEs mode m (by omega)
    (hcap.trans s1) (le_trans (Nat.add_le_add_right (Nat.add_le_add hJL hJR) 1) (le_trans (by omega) s2)) hcwid s3 s4 s5 s6
    (hb.trans s7) (hvb.trans s8) hcw1
    (SelCoefV.hcoef_site sources 𝔨 p den n x bits _ (NearCubicWires.SourceSkeleton.Params.coefficientAt_le_cw sources gamma hg hh p (C10PartsSchedule.widthAt sources 𝔨 n)))
    (SelCoefV.hcoefV_site sources 𝔨 p den n x bits) (hY.trans s9) hloop
  have := hc.trans hE
  omega

theorem hloop_site (L target tg den n : Nat) (x : BitInput n) (bits : List Bool) (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
    (ci : Fin (2 ^ ((RepairSource.CloseoutLanguage.selectedPCPP sources).output
      (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits))).clauseBits))
    (hden : 1 ≤ den) (m : Nat)
    (hr : Admission.RequestAdmitted den p.clauseDegree tg (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m))
    (hqm : (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).q = C10PartsSchedule.widthAt sources 𝔨 n)
    (hL : (requestAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).liveScale = L)
    (hF : Fields.cost (header mode (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits)).arity L target (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m).length)
        (Fields.nSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) (Fields.sSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m))
        (Fields.tSlots (decompositionOf sources) mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) ≤ 1000 * (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n) + 1)) :
    loopW sources (RepairSource.CloseoutLanguage.selectedPCPP sources) (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits)) ci (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph L target (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p) (SourceBudget.wCap (C10PartsSchedule.widthAt sources 𝔨 n)) (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) mode m ≤
      0 * (n + 1) ^ 0 + (SelLoopCost.loopC (decompositionOf sources)) * ((sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n)) + 1) ^ (SelLoopCost.slotE (decompositionOf sources)) := by
  have hY := YbFit.Yb_le_meta selector sources p packets L (decompositionOf sources) hden _ hr hL
  rw [hqm] at hY
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := sqv_ge selector sources p packets (NearCubicWires.SourceSkeleton.Params.cwC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.cwE sources gamma hg hh p) (NearCubicWires.SourceSkeleton.Params.dC sources gamma hg hh p)
    (NearCubicWires.SourceSkeleton.Params.dE sources gamma hg hh p) 𝔯 L target p.clauseDegree tg (C10PartsSchedule.widthAt sources 𝔨 n)
  have hports := NearCubicWires.SourceFactorSel.H5.ports_le_D sources gamma hg hh p (C10PartsSchedule.widthAt sources 𝔨 n)
  have hP : (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p) ≤ (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n)) := hports.2.1.trans s4
  have hsum := NearCubicWires.SourceSkeleton.Params.pSum_le_P sources gamma hg hh p (C10PartsSchedule.widthAt sources 𝔨 n)
  have hpT : RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.ThrSwitch.codeWidth (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n))) ≤
      NearCubicWires.SourceSkeleton.Params.pSum (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n) := by
    unfold NearCubicWires.SourceSkeleton.Params.pSum SourceBudget.pCap; exact Nat.le_add_right _ _
  have hpS : RepairOrdinary.CloseoutRowsCircuitCapacity.capacity (SourceRequest.SymOriginal.symCodeWidth (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n))) ≤
      NearCubicWires.SourceSkeleton.Params.pSum (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
        (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n) := by
    unfold NearCubicWires.SourceSkeleton.Params.pSum SourceBudget.pCap; exact Nat.le_add_left _ _
  have h := SelLoopCost.loop_le sources (RepairSource.CloseoutLanguage.selectedPCPP sources) (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits)) ci (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph L target (NearCubicWires.SourceSkeleton.Params.pC sources gamma hg hh p * (C10PartsSchedule.widthAt sources 𝔨 n + 1) ^
          NearCubicWires.SourceSkeleton.Params.pE sources gamma hg hh p) (SourceBudget.wCap (C10PartsSchedule.widthAt sources 𝔨 n)) (SourceBudget.ldCap (NearCubicWires.SourceSkeleton.Params.ldC sources gamma hg hh p)
          (NearCubicWires.SourceSkeleton.Params.ldE sources gamma hg hh p) (C10PartsSchedule.widthAt sources 𝔨 n)) mode m
    (NearCubicWires.SourceStart.MetaRun.MBof selector sources p packets L (C10PartsSchedule.widthAt sources 𝔨 n)) (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n)) (hY.trans s9) hP
    ((le_capacity _).trans (hpT.trans (hsum.trans hP))) ((le_capacity _).trans (hpS.trans (hsum.trans hP))) hF
  exact h.trans (Nat.le_add_left _ _)

theorem g7_windows_siteF (L target tg den n : Nat)
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
    (hF : ∀ m, m ≤ (monomials (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci).length →
      Fields.cost (header mode (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits)).arity L target (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m).length)
        (Fields.nSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) (Fields.sSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m))
        (Fields.tSlots (decompositionOf sources) mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) ≤ 1000 * (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n) + 1))
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
  g7_windows_siteS selector xtra mask packets rows sources gamma hg hh p L target tg 0 0 (SelLoopCost.loopC (decompositionOf sources)) (SelLoopCost.slotE (decompositionOf sources)) (SelWinOnsetW.hkW selector mask packets rows sources gamma hg hh p 0 (by decide)) den n
    ((SelWinOnsetW.g7OnsetQ_eq selector xtra mask packets rows sources gamma hg hh p L target tg 0 0 (SelLoopCost.loopC (decompositionOf sources)) (SelLoopCost.slotE (decompositionOf sources)) (SelWinOnsetW.hkW selector mask packets rows sources gamma hg hh p 0 (by decide))).trans_le hn)
    x bits hlen mode ph ci hden hread hadm
    (fun m hm => hloop_site selector xtra mask packets rows sources gamma hg hh p L target tg den n x bits mode ph ci hden m (hadm m hm).1 (hadm m hm).2.1 (hadm m hm).2.2 (hF m hm))
    Rc hRc

theorem g7cost_tableF (L target tg den n : Nat)
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
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci L target mode m).liveScale = L)
    (hF : Fields.cost (header mode (req sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) x (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits)).arity L target (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m).length)
        (Fields.nSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) (Fields.sSlots mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m))
        (Fields.tSlots (decompositionOf sources) mode (FactorLoop.factorsAt (PCJd04de0277f804fcc_.coordinate sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p den x
        (C10TotalDecode.oracleOf sources 𝔨 (PolynomialClock.ordinaryClock 𝔨) p.degree n bits) bits) ph ci m)) ≤ 1000 * (sqS selector xtra mask packets rows sources gamma hg hh p L target tg (C10PartsSchedule.widthAt sources 𝔨 n) + 1)) :
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
  g7cost_tableS selector xtra mask packets rows sources gamma hg hh p L target tg 0 0 (SelLoopCost.loopC (decompositionOf sources)) (SelLoopCost.slotE (decompositionOf sources)) (SelWinOnsetW.hkW selector mask packets rows sources gamma hg hh p 0 (by decide)) den n
    ((SelWinOnsetW.g7OnsetQ_eq selector xtra mask packets rows sources gamma hg hh p L target tg 0 0 (SelLoopCost.loopC (decompositionOf sources)) (SelLoopCost.slotE (decompositionOf sources)) (SelWinOnsetW.hkW selector mask packets rows sources gamma hg hh p 0 (by decide))).trans_le hn)
    x bits hlen mode ph ci hden m hr hqm hL
    (hloop_site selector xtra mask packets rows sources gamma hg hh p L target tg den n x bits mode ph ci hden m hr hqm hL hF)

end v5

end
end NearCubicWires.SourceRequest.SelLoopSite
end
