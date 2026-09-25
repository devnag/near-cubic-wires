import Proof.SourceAssembly.SourceFactorSelTraceCost
import Proof.Packets.SrcLayRows

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
namespace NearCubicWires.SourceFactorSel.TraceSiteGF
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

theorem traceNums_site (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
    (Hv : Nat → Fin (code ph).sourceTapes → Nat) (Av : Nat → Fin (code ph).sourceTapes → List Bool)
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (siteFuel N : ℕ)
    (hk : k = ClauseCost.kS selector mask packets rows sources gamma hg hh p capIndex)
    (hLe : L = 𝔏4) (hVe : V = SourceBudget.Params.VvOf selector sources p L (C10PartsSchedule.widthAt sources k n))
    (hden1 : 1 ≤ den) (hn : (selR sources p k).onset ≤ n) (hr : r = (selR sources p k).exponent)
    (hdegE : deg = degOf sources selector coordC ph ci L tgtC modeC lay)
    (hlayD : ∀ j, (lay j).degree = Admission.uniformDeg vQ L)
    (hlayC : ∀ j, (lay j).C = SourceBudget.Params.COf selector sources p (C10PartsSchedule.widthAt sources k n))
    (h201 : 201 * normalizedLiveCount (C10PartsSchedule.widthAt sources k n) L ≤ C10PartsSchedule.widthAt sources k n)
    (ha : (code ph).a = printerOf sources)
    (hold0 : (old 0).length ≤ InitRun.D0 𝒷) (hold : ∀ j, old (j+1) = oldAt coordC ph ci sources L tgtC modeC 𝒷 (InitRun.D0 𝒷) (j+1))
    (hfam : familyCost = ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (href : refillCost = ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hfst : firstCost = ClauseCost.Bsplit selector mask packets rows sources gamma hg hh p k n)
    (hsf : siteFuel = SourceBudget.siteRHS sources k (selR sources p k).exponent
      ((ClassR.baseR 𝔅4).dS sources gamma hg hh p) ((ClassR.baseR 𝔅4).hT sources gamma hg hh p) ((ClassR.baseR 𝔅4).hS sources gamma hg hh p)
      ((ClassR.baseR 𝔅4).m sources gamma hg hh p) ((ClassR.baseR 𝔅4).L sources gamma hg hh p) ((ClassR.baseR 𝔅4).cP sources gamma hg hh p k)
      ((ClassR.baseR 𝔅4).cT sources gamma hg hh p k) ((ClassR.baseR 𝔅4).cS sources gamma hg hh p k) n (C10PartsSchedule.widthAt sources k n)) :
    TraceNums mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt
      (InitRun.D0 𝒷) (InitRun.cap0 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷)
      old H A Rc familyCost refillCost firstCost counterReserve H0 A0 siteFuel N { vdI with H := Hv, A := Av } := by
  have hcut := selR_cutoff sources p k hn
  have hq : vQ = C10PartsSchedule.widthAt sources k n :=
    Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) hcut
  have hdegv : ∀ j, deg j ≤ vQ := by
    subst hdegE
    exact degOf_le_arity selector sources p den hden k r scratch n x bits hp ph ci L lay hlayD
  have hdegw : ∀ j, deg j ≤ C10PartsSchedule.widthAt sources k n := fun j => (hdegv j).trans (le_of_eq hq)
  obtain ⟨t1, t2, t3⟩ := SourceStart.LayRP.traceLayRows selector sources p den hden k r scratch n x bits hp ph ci L code lay deg V hcut h201
    hlayD hlayC hdegE hVe ha
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := TraceNumsGF2.traceNums_gf2 mask selector packets rows compiler sources p den hden k r scratch n x bits hp site
    code ph ci L lay deg V dflt old H A Rc familyCost refillCost firstCost counterReserve semantics hold0 hold hn hr hdegv
  have hc := TraceCostGF.hcost_gf mask selector packets rows compiler sources hg hh p capIndex den hden k r scratch n x bits hp site code ph ci L lay
    deg V dflt old H A Rc familyCost refillCost firstCost counterReserve hk hLe hVe hden1 hn hr hdegw ha hfam
  have hb := TraceCostGF.hbudget_gf mask selector packets rows compiler sources hg hh p den hden k r scratch n x bits hp site code ph ci L lay
    deg V dflt old H A Rc familyCost refillCost firstCost counterReserve hn hfam href hfst siteFuel hsf
  exact ⟨t1, t2, t3, c1, c2, c3, c4, c5, c6, hc, hb⟩

end clause

end
end NearCubicWires.SourceFactorSel.TraceSiteGF
end

