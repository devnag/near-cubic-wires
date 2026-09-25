import Proof.SourceAssembly.SourceFactorSelTraceNums

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
namespace NearCubicWires.SourceFactorSel.TraceNumsGF2
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section clause
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
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

theorem traceNums_gf2 (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
    (hold0 : (old 0).length ≤ InitRun.D0 𝒷) (hold : ∀ j, old (j+1) = oldAt coordC ph ci sources L tgtC modeC 𝒷 (InitRun.D0 𝒷) (j+1))
    (hn : (selR sources p k).onset ≤ n) (hr : r = (selR sources p k).exponent) (hdeg : ∀ j, deg j ≤ vQ) :
    4 * 𝒷 + 5 ≤ InitRun.cap0 𝒷 ∧
    20 * 𝒷 + 27 ≤ CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷 ∧
    (∀ j < (vdI).entries.length, (vdI).rowWidth j ≤ 𝒷) ∧
    (∀ j < (vdI).entries.length, (vdI).total j < 2 ^ 𝒷) ∧
    (∀ j < (vdI).entries.length, ((vdI).old j).length ≤ (vdI).D j) ∧
    (∀ j < (vdI).entries.length,
      CloseoutFinalC10AppendPositioning.rawBudget 𝒷 ((vdI).phasePrefix ++ (vdI).entries.take j).length ≤ (vdI).resetSize j) := by
  refine ⟨hcap_init 𝒷, hlog_init 𝒷, ?_, ?_, ?_, ?_⟩
  · exact hw_selR mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt
      (InitRun.D0 𝒷) (InitRun.cap0 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷)
      old H A Rc familyCost refillCost firstCost counterReserve hn hr hdeg
  · exact hfit_clause mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt
      (InitRun.D0 𝒷) (InitRun.cap0 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷) (CloseoutFinalC10AppendWorkspaceInit.capacity 𝒷)
      old H A Rc familyCost refillCost firstCost counterReserve semantics
      (selR sources p k) hn hr
  · intro j _
    show (old j).length ≤ InitRun.D0 𝒷
    cases j with
    | zero => exact hold0
    | succ j =>
      rw [hold j]
      exact oldAt_length coordC ph ci sources L tgtC modeC 𝒷 (j + 1)
  · exact hr_clause mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt
      𝒷 H A Rc familyCost refillCost firstCost counterReserve (selR sources p k) hn (by rw [hr])

end clause

end
end NearCubicWires.SourceFactorSel.TraceNumsGF2
end

