import Proof.SourceAssembly.SourceStepsSelect
import Proof.SourceAssembly.SourceStepsData

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

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
    (dflt : P1TopDownPaidReusable.Datum) (Dw capw logw resetw : Nat) (old : Nat → List Bool)
    (H : Nat → Fin (code ph).sourceTapes → Nat) (A : Nat → Fin (code ph).sourceTapes → List Bool)
    (Rc familyCost refillCost firstCost counterReserve : Nat)

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
set_option hygiene false in
local notation "vdH" => clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old H A Rc familyCost refillCost firstCost counterReserve

/-- **`traceOfChain`'s `h_hw`** at any Selection whose exponent covers the row-width exponent `βE + 3`. -/
theorem hw_clause (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hr : r = S.exponent)
    (hβ : SourceBudget.betaE (decompositionOf sources) p.clauseDegree + 3 ≤ S.exponent)
    (hcut : CloseoutWitnessPolicy.inputCutoff sources ≤ n)
    (hwid : 2 * SourceBudget.betaC (decompositionOf sources) p.clauseDegree + 10 ≤ C10PartsSchedule.widthAt sources k n)
    (hdeg : ∀ j, deg j ≤ vQ) :
    ∀ j < (vdH).entries.length, (vdH).rowWidth j ≤ C10PartsSchedule.entryWidthSchedule sources k r n := by
  intro j hj
  have hjo : j < (TraceData.order coordC ph ci).length := by
    have hl := TraceData.hlen coordC ph ci sources L tgtC modeC
    have hj' : j < (TraceData.entriesOf coordC ph ci sources L tgtC modeC).length := hj
    omega
  have hadm := Admission.trace_atoms_admitted sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits hcut ph ci
    (TraceData.order coordC ph ci) (List.Perm.refl _) j
  have hadm' : Admission.Admitted den p.clauseDegree (SourceRequest.FactorLoop.factorsAt coordC ph ci j) :=
    (congrArg (Admission.Admitted den p.clauseDegree) (TraceData.factors_getD coordC ph ci j hjo)).mp hadm
  have hrw := SourceBudget.call_rowWidth_le sources L modeC (target := tgtC) (Nat.succ_le_of_lt hden)
    (SourceRequest.FactorLoop.factorsAt coordC ph ci j) hadm' (deg j) (hdeg j)
  have hq : vQ = C10PartsSchedule.widthAt sources k n :=
    Admission.req_arity sources k (PolynomialClock.ordinaryClock k) x oracleC hcut
  have hq1 : 2 * SourceBudget.betaC (decompositionOf sources) p.clauseDegree + 10 ≤ vQ + 1 := by omega
  have hpow : (2 * SourceBudget.betaC (decompositionOf sources) p.clauseDegree + 10) *
      (vQ + 1) ^ (SourceBudget.betaE (decompositionOf sources) p.clauseDegree + 2) ≤
      (vQ + 1) ^ S.exponent := by
    calc (2 * SourceBudget.betaC (decompositionOf sources) p.clauseDegree + 10) *
          (vQ + 1) ^ (SourceBudget.betaE (decompositionOf sources) p.clauseDegree + 2)
        ≤ (vQ + 1) * (vQ + 1) ^ (SourceBudget.betaE (decompositionOf sources) p.clauseDegree + 2) :=
          Nat.mul_le_mul_right _ hq1
      _ = (vQ + 1) ^ (SourceBudget.betaE (decompositionOf sources) p.clauseDegree + 3) :=
          (pow_succ' (vQ + 1) (SourceBudget.betaE (decompositionOf sources) p.clauseDegree + 2)).symm
      _ ≤ (vQ + 1) ^ S.exponent := Nat.pow_le_pow_right (Nat.succ_pos _) hβ
  have hwp : (vQ + 1) ^ S.exponent = C10PartsSchedule.widthPower sources k r n := by
    rw [hr, hq]
    rfl
  have hb : C10PartsSchedule.widthPower sources k r n ≤ C10PartsSchedule.entryWidthSchedule sources k r n :=
    Nat.le_add_left _ _
  show TraceData.rowWidthOf coordC ph ci sources L tgtC modeC deg j ≤ _
  exact hrw.trans (hpow.trans (hwp.le.trans hb))

/-- SS's effective degree is at most the arity, at AD's uniform layout degree. -/
theorem degOf_le_arity
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg vQ L) (j : Nat) :
    degOf sources selector coordC ph ci L tgtC modeC lay j ≤ vQ := by
  refine (min_le_left _ _).trans ?_
  rw [hlay j]
  exact Admission.uniformDeg_le _ _

/-- **`h_hw` at the decision-77 Selection** `selR sources p k`, past its onset. -/
theorem hw_selR (hn : (selR sources p k).onset ≤ n) (hr : r = (selR sources p k).exponent) (hdeg : ∀ j, deg j ≤ vQ) :
    ∀ j < (vdH).entries.length, (vdH).rowWidth j ≤ C10PartsSchedule.entryWidthSchedule sources k r n :=
  hw_clause mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt
    Dw capw logw resetw old H A Rc familyCost refillCost firstCost counterReserve (selR sources p k) hr
    (selR_ge_beta sources p k) (selR_cutoff sources p k hn) (selR_width sources p k hn) hdeg

end clause

end
end NearCubicWires.SourceSteps
end
