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
open NearCubicWires.SourcePhase
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
local notation "vdH" => clauseVals mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci L lay deg V dflt Dw capw logw resetw old H A Rc familyCost refillCost firstCost counterReserve

theorem hfit_clause (semantics : PCJ9eff70d512234a4c_Fixed.Certificate)
    (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent) :
    ∀ j < (vdH).entries.length, (vdH).total j < 2 ^ C10PartsSchedule.entryWidthSchedule sources k r n := by
  intro j hj
  have hm : modeC = CloseoutWitness.BoundedFields.symmetric bits := (penalty_bank sources p den hden k r scratch n x bits hp).1
  have horder := phase_monomials_perm ph (pcppAt sources k (PolynomialClock.ordinaryClock k) x oracleC) coordC
    C10TotalDecode.Atom.systematic
  have hrec : List.Forall₂ (fun m e =>
      e.coefficient = CloseoutFinalC10SupplierCalls.coefficientEstimate m.coefficient ∧
      e.count = (LiveRows.fraction sources L tgtC modeC m.factors).1 ∧
      e.denominator = (LiveRows.fraction sources L tgtC modeC m.factors).2)
      (List.ofFn fun c => TraceData.order coordC ph c).flatten
      (List.ofFn fun c => TraceData.entriesOf coordC ph c sources L tgtC modeC).flatten := by
    apply flatten_ofFn_forall₂
    intro c
    apply forall₂_of_index _ _ _ (TraceData.hlen coordC ph c sources L tgtC modeC)
    intro i h1 h2
    rw [TraceData.hentries coordC ph c sources L tgtC modeC i h2]
    refine ⟨?_, ?_, ?_⟩
    · show CloseoutFinalC10SupplierCalls.coefficientEstimate
          (((TraceData.order coordC ph c).map (fun m => m.coefficient)).getD i 0) = _
      rw [List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_map]
    · show (LiveRows.fraction sources L tgtC modeC (SourceRequest.FactorLoop.factorsAt coordC ph c i)).1 = _
      rw [SourceRequest.FactorLoop.factorsAt_of_lt coordC ph c i h1]
    · show (LiveRows.fraction sources L tgtC modeC (SourceRequest.FactorLoop.factorsAt coordC ph c i)).2 = _
      rw [SourceRequest.FactorLoop.factorsAt_of_lt coordC ph c i h1]
  have hmode : ∀ m ∈ (List.ofFn fun c => TraceData.order coordC ph c).flatten, ∀ atom ∈ m.factors,
      C10NaturalModeAtoms.ModeAtom modeC atom := by
    intro m hm' atom hatom
    rw [hm]
    obtain ⟨l, hl, hml⟩ := List.mem_flatten.mp hm'
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
    exact site_mode sources p k den (PolynomialClock.ordinaryClock k) x oracleC bits ph c m hml atom hatom
  have hden' : ∀ m ∈ (List.ofFn fun c => TraceData.order coordC ph c).flatten,
      (LiveRows.fraction sources L tgtC modeC m.factors).2 ≤ 2 ^ CloseoutFinalC10ModeNativeEnvelope.nativeDenBits sources k p n := by
    intro m hm'
    rw [hm]
    obtain ⟨l, hl, hml⟩ := List.mem_flatten.mp hm'
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
    exact fraction_den_le sources k p den x oracleC bits L ph c m hml
  have hcoef := phase_hcoeff sources p k den S hn x bits ph
  rw [← hr] at hcoef
  have hdw := phase_hdenwidth sources p k S hn
  rw [← hr] at hdw
  obtain ⟨-, -, -, -, hvalid⟩ := semantics sources L tgtC modeC ph
    (Poly sources p k den (PolynomialClock.ordinaryClock k) n x oracleC bits ph)
    (C10PartsSchedule.entryWidthSchedule sources k r n) (CloseoutFinalC10ModeNativeEnvelope.nativeDenBits sources k p n)
    (CloseoutFinalC10StageFields.stageLimits sources p)
    (List.ofFn fun c => TraceData.order coordC ph c).flatten
    (List.ofFn fun c => TraceData.entriesOf coordC ph c sources L tgtC modeC).flatten
    horder hmode hrec
    (phase_hmass sources p k den (PolynomialClock.ordinaryClock k) x oracleC bits ph) hcoef
    (phase_htarget sources p ph) (phase_htargetpos sources p) hden' hdw
  have hmem : (TraceData.entriesOf coordC ph ci sources L tgtC modeC)[j]'hj ∈
      (List.ofFn fun c => TraceData.entriesOf coordC ph c sources L tgtC modeC).flatten :=
    List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨ci, rfl⟩, List.getElem_mem hj⟩
  have hv := (hvalid _ hmem).count
  rw [TraceData.hentries coordC ph ci sources L tgtC modeC j hj] at hv
  exact hv

end clause

end
end NearCubicWires.SourceSteps
end
