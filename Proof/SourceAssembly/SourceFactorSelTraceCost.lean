import Proof.Packets.SrcSeamFamH
import Proof.SourceAssembly.SourceFactorSelClauseCost
import Proof.SourceAssembly.SourceFactorSelTraceNums2

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
open NearCubicWires.SourceSteps
open NearCubicWires.SourceBudget NearCubicWires.SourceSkeleton.ClassR
namespace NearCubicWires.SourceFactorSel.TraceCostGF
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section clause
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma) (capIndex : ParNat)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (ph : Phase)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)
    (lay : TraceData.LayoutFamily (PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits) ph ci sources L (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)) (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) selector) (deg : Nat → Nat) (V : Nat)
    (dflt : P1TopDownPaidReusable.Datum) (old : Nat → List Bool)
    (H : Nat → Fin (code ph).sourceTapes → Nat) (A : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)

set_option hygiene false in
local notation "𝒷" => C10PartsSchedule.entryWidthSchedule sources k r n
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity
set_option hygiene false in
local notation "vdI" => clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt
  (InitRun.D0 𝒷) (InitRun.cap0 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷)
  old H A Rc familyCost refillCost firstCost counterReserve

set_option hygiene false in
local notation "𝔅4" => SourceSkeleton.ClassV4.siteBP4 selector mask packets rows
set_option hygiene false in
local notation "𝔏4" => SourceSkeleton.ClassV4.siteL4 selector mask packets rows sources gamma hg hh p

/-- `D0 b + 1 ≤ 22·(b + 1)` at `r = rBsel` (the family class's `dC = 22`). -/
theorem hDw_site (hr : r = (selR sources p k).exponent) :
    InitRun.D0 𝒷 + 1 ≤ 22 * (C10PartsSchedule.entryWidthSchedule sources k (selR sources p k).exponent n + 1) := by
  have hb1 : 1 ≤ 𝒷 := by
    unfold C10PartsSchedule.entryWidthSchedule C10PartsSchedule.widthPower
    have := Nat.one_le_pow r (C10PartsSchedule.widthAt sources k n + 1) (Nat.succ_pos _)
    omega
  rw [← hr]
  unfold InitRun.D0 InitEnc.rr
  omega

/-- The site family class lies in `B` (first member of the join). -/
theorem fam_le_B :
    (famClsAt (printerOf sources) sources p k (selR sources p k).exponent (SourceBudget.Params.cVcN selector sources gamma hg hh p)
      (SourceBudget.Params.hVN selector sources gamma hg hh p) 22).Le ((𝔅4).at sources gamma hg hh p 𝔏4 k) := by
  have e : (𝔅4).at sources gamma hg hh p 𝔏4 k =
      (((famSiteR printerOf (SourceBudget.Params.cVcN selector) (SourceBudget.Params.hVN selector)).at sources gamma hg hh p 𝔏4 k).join
        ((refFam (SourceSkeleton.ClassV4.siteR4 selector mask packets rows) (SourceSkeleton.ClassV4.siteY4 selector mask packets rows)).at
          sources gamma hg hh p 𝔏4 k)).join
        ((firstFam (SourceSkeleton.ClassV4.siteR4 selector mask packets rows)
          ((SourceSkeleton.ClassV4.siteYF04 selector mask packets rows).join (SourceSkeleton.ClassV4.siteI4 selector mask packets rows))).at
          sources gamma hg hh p 𝔏4 k) := rfl
  have e2 : (famSiteR printerOf (SourceBudget.Params.cVcN selector) (SourceBudget.Params.hVN selector)).at sources gamma hg hh p 𝔏4 k =
      famClsAt (printerOf sources) sources p k (selR sources p k).exponent (SourceBudget.Params.cVcN selector sources gamma hg hh p)
        (SourceBudget.Params.hVN selector sources gamma hg hh p) 22 := rfl
  rw [e, ← e2]
  exact (CostCls.le_join_left _ _).trans (CostCls.le_join_left _ _)

theorem hcost_gf (hk : k = ClauseCost.kS selector mask packets rows sources gamma hg hh p capIndex)
    (hLe : L = 𝔏4) (hVe : V = SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n))
    (hden1 : 1 ≤ den) (hn : (selR sources p k).onset ≤ n) (hr : r = (selR sources p k).exponent)
    (hdeg : ∀ j, deg j ≤ C10PartsSchedule.widthAt sources k n) (ha : (code ph).a = printerOf sources)
    (hfam : familyCost = ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n) :
    ∀ j < (vdI).entries.length,
      f_budget (code ph).a ((vdI).S j) ((vdI).rowWidth j) 𝒷 ((vdI).xs j).length + 1 +
        (2 * (vdI).D j + 4 + 1 + (2 * e_emitCost 𝒷 + 2) + 1 +
          CloseoutFinalC10AppendPositioning.budget 𝒷 ((vdI).phasePrefix ++ (vdI).entries.take j).length) ≤ (vdI).familyCost := by
  have hcut := selR_cutoff sources p k hn
  have hVc : V ≤ SourceBudget.Params.cVcN selector sources gamma hg hh p *
      RuntimeShape.tableClass L (SourceBudget.Params.hVN selector sources gamma hg hh p) (C10PartsSchedule.widthAt sources k n) := by
    rw [hVe]; exact le_rfl
  have hfamAll := SourceStart.SeamRP.family_hcost_all sources p den k hden1 (selR sources p k) hn hcut x bits modeC ph L ci selector compiler lay
    deg hdeg (printerOf sources) V (SourceBudget.Params.cVcN selector sources gamma hg hh p) (SourceBudget.Params.hVN selector sources gamma hg hh p)
    hVc (InitRun.D0 𝒷) 22 (hDw_site sources p k r n hr) 4 ((𝔅4).at sources gamma hg hh p 𝔏4 k) (fam_le_B mask selector packets rows sources hg hh p k)
  rw [← hr] at hfamAll
  intro j _
  have h1 := hfamAll j
  show f_budget (code ph).a (P1TopDownPaidReusableReserves.workspace (code ph).a V) _ 𝒷 _ + 1 + _ ≤ familyCost
  rw [ha, hfam]
  subst hLe hk
  exact h1

theorem hbudget_gf (hn : (selR sources p k).onset ≤ n)
    (hfam : familyCost = ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (href : refillCost = ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hfst : firstCost = ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n) (siteFuel : ℕ)
    (hsf : siteFuel = SourceBudget.siteRHS sources k (selR sources p k).exponent
      ((baseR 𝔅4).dS sources gamma hg hh p) ((baseR 𝔅4).hT sources gamma hg hh p) ((baseR 𝔅4).hS sources gamma hg hh p)
      ((baseR 𝔅4).m sources gamma hg hh p) ((baseR 𝔅4).L sources gamma hg hh p) ((baseR 𝔅4).cP sources gamma hg hh p k)
      ((baseR 𝔅4).cT sources gamma hg hh p k) ((baseR 𝔅4).cS sources gamma hg hh p k) n (C10PartsSchedule.widthAt sources k n)) :
    (vdI).firstCost + 1 + ((vdI).entries.length * ((vdI).familyCost + 1 + (vdI).refillCost + 3) + 3) ≤ siteFuel := by
  have hE : (vdI).entries.length ≤ (C10PartsSchedule.widthAt sources k n + 1) ^ (selR sources p k).exponent := by
    show (TraceData.entriesOf coordC ph ci sources L tgtC modeC).length ≤ _
    rw [TraceData.hlen]
    exact calls_le_pow sources k p (selR sources p k) den hn x bits ph ci
  have hW1 : 1 ≤ C10PartsSchedule.widthConst sources k ^ (selR sources p k).exponent :=
    Nat.one_le_pow _ _ (one_le_widthConst sources k)
  have hEq : (vdI).entries.length ≤ C10PartsSchedule.widthConst sources k ^ (selR sources p k).exponent *
      (C10PartsSchedule.widthAt sources k n + 1) ^ (selR sources p k).exponent := hE.trans (Nat.le_mul_of_pos_left _ hW1)
  have hEn : (vdI).entries.length ≤ C10PartsSchedule.widthConst sources k ^ (selR sources p k).exponent * (n + 1) ^ (selR sources p k).exponent :=
    hE.trans (width_pow_le sources k n (selR sources p k).exponent)
  show firstCost + 1 + ((vdI).entries.length * (familyCost + 1 + refillCost + 3) + 3) ≤ siteFuel
  rw [hsf, hfam, href, hfst]
  exact Admission.siteFuel_inClasses hEn hEq le_rfl le_rfl le_rfl

end clause

end
end NearCubicWires.SourceFactorSel.TraceCostGF
end

