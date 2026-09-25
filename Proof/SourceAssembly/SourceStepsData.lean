import Proof.SourceAssembly.SourceDegreeSlope
import Proof.SourceAssembly.SourceInitRun
import Proof.SourceAssembly.SourceSkelBridge

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
open NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section generic
variable (sources : EightSources) (selector : CyclicChoice.Laws)
  {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
    ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat) (mode : Bool)

/-- **The effective degree of call `j`**: `min (lay j).degree |pool j|` (the degree the native family's rows are printed at). -/
abbrev degOf (lay : SourceConstruction.TraceData.LayoutFamily coordinate ph ci sources L target mode selector) : Nat → Nat :=
  fun j => min (lay j).degree (Packets.pool (decompositionOf sources)
    (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j))
    (Packets.geometry selector
      (Packets.request sources L target mode (SourceRequest.FactorLoop.factorsAt coordinate ph ci j)))).length

/-- **The row width of call `m` in the seam's form, at the init's slopes and `U0`**: for a layout family carrying AD's uniform degree,
`rowWidthOf … (degOf lay) m = RowWidth.rw (if 3 < len m then InitRun.Mb L q else InitPost.Ms L q) (InitRun.U0 L q) (len m)`. -/
theorem rw_init (lay : SourceConstruction.TraceData.LayoutFamily coordinate ph ci sources L target mode selector)
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg q L) (hL : 1 ≤ L)
    (hu : 1 ≤ q / (200 * (normalizedLiveCount q L + 1 + 1))) (m : Nat) :
    SourceConstruction.TraceData.rowWidthOf coordinate ph ci sources L target mode
        (degOf sources selector coordinate ph ci L target mode lay) m =
      RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))).gs).length then InitRun.Mb L q else InitPost.Ms L q) (InitRun.U0 L q) (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))).gs).length := by
  refine rw_bridge sources coordinate ph ci L target mode (degOf sources selector coordinate ph ci L target mode lay)
    (InitRun.Mb L q) (InitPost.Ms L q) (InitRun.U0 L q) (fun j => ?_) ?_ m
  · exact slope_of_deg (normalizedLiveCount q L) (InitRun.Mb L q) (InitPost.Ms L q)
      (q / (200 * (normalizedLiveCount q L + 1 + 1))) _ _ rfl rfl
      (SourceConstruction.TraceData.deg_slope coordinate ph ci sources L target mode selector lay hlay hL hu j)
  · exact U0Of_eq q (normalizedLiveCount q L)

end generic

section clause
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
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
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vdC" => clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old H A Rc familyCost refillCost firstCost counterReserve

theorem hds_clause : ∀ j, (vdC).ds (j+1) = dataList (decompositionOf sources)
    ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))
    (geometryOf selector (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC (j+1)))
    (layoutAtOf sources selector coordC ph ci L tgtC modeC lay (j+1))
    (factsAtOf sources selector compiler coordC ph ci L tgtC modeC (j+1)) :=
  fun j => ds_bridge sources selector compiler coordC ph ci L tgtC modeC lay (j+1)

/-- **`hxs` at `clauseVals`** (`xs := map datumValue ds`). -/
theorem hxs_clause : ∀ j, ((vdC).xs (j+1)).length = ((vdC).ds (j+1)).length :=
  fun _ => List.length_map _

/-- **`hrw` at `clauseVals`** at `deg := degOf lay` with the init's `Mb`, `Ms`, `U0`, where `q` is the clause PCPP's arity
`(req sources k clock x oracle).arity` (the coordinate's own `q`; `= widthAt sources k n` past `inputCutoff`, AD's `req_arity`). -/
theorem hrw_clause
    (hlay : ∀ j, (lay j).degree = Admission.uniformDeg (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity L)
    (hL : 1 ≤ L)
    (hu : 1 ≤ (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity /
      (200 * (normalizedLiveCount (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity L + 1 + 1))) :
    ∀ j, (clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay
        (degOf sources selector coordC ph ci L tgtC modeC lay) V dflt Dw capw logw resetw old H A Rc familyCost refillCost firstCost
        counterReserve).rowWidth (j+1) =
      RowWidth.rw (if 3 < (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length
          then InitRun.Mb L (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity
          else InitPost.Ms L (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)
        (InitRun.U0 L (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)
        (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs (decompositionOf sources) ((requestAt coordC ph ci L tgtC modeC (j+1)).family (decompositionOf sources))).gs).length :=
  fun j => rw_init sources selector coordC ph ci L tgtC modeC lay hlay hL hu (j+1)

end clause

end
end NearCubicWires.SourceSteps
end
