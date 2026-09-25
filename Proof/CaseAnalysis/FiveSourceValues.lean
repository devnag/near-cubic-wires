import Proof.CaseAnalysis.FiveSourceCode

section
/- Source body: PCJ38fbfed565f64139_Source.lean; adapted only for the paid mask load. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace RCFive.Source
open PCJc4297ab269d8423a_Source
attribute [local irreducible] P1TopDownPaidPayload.tapes

/- Per-call values for one already fixed SourceCode. -/
structure CallValues (Atom : Type) (sourceTapes : Nat) where
  order :
    List (CircuitMonomial Atom 4)
  L :
    Nat
  target :
    Nat
  dflt :
    P1TopDownPaidReusable.Datum
  ds :
    Nat → List P1TopDownPaidReusable.Datum
  xs :
    Nat → List Nat
  S :
    Nat → Nat
  R :
    Nat → Nat
  B :
    Nat → Nat
  rowWidth :
    Nat → Nat
  total :
    Nat → Nat
  denominator :
    Nat → Nat
  D :
    Nat → Nat
  cap :
    Nat → Nat
  logSize :
    Nat → Nat
  resetSize :
    Nat → Nat
  coefficient :
    Nat → CompetitorValidity.Estimate
  old :
    Nat → List Bool
  phasePrefix :
    List Stream.Entry
  entries :
    List Stream.Entry
  H :
    Nat → Fin sourceTapes → Nat
  A :
    Nat → Fin sourceTapes → List Bool
  reserveSize :
    Nat
  familyCost :
    Nat
  refillCost :
    Nat
  firstCost :
    Nat
  counterReserve :
    Nat



abbrev SourceValues  (mask : MaskProducer) (selector : CyclicChoice.Laws) (packets : PacketLibrary selector) (rows : RowLibrary selector) (compiler : Packets.CompilerLaws) (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n=>n^(k+2)))
 (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (ci : Fin (2^((CloseoutLanguage.selectedPCPP sources).output (req sources k clock x oracle)).clauseBits))
 (globalH globalHnext : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→Nat)
 (globalA globalAfter : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)→List Bool)
 (b siteFuel : Nat)
 (code : SourceCode mask selector packets rows sources p k r scratch ph) :=
  CallValues (C10TotalDecode.Atom (pcppAt sources k clock x oracle)) code.sourceTapes

end RCFive.Source
end
