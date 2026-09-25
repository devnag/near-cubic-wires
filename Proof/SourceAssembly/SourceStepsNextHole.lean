import Proof.SourceAssembly.SourceStepsPartsHoles

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSteps
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section nexthole
variable (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes)

def NextHole (d : SourceConstruction.Dims) {eX pX gW eR eV X : Nat}
    (pl : Phase → SourceConstruction.InitRun.Place d eX pX gW eR eV X ((code ph).sourceTapes + 1))
    (e : d.RestExt3 eX pX gW) (hV : d.U ≤ (code ph).sourceTapes) (Rc Rk Ce : Nat)
    (Kc : Fin ((code ph).sourceTapes + 1) → Prop) (K0 : Phase → Nat → Fin ((code ph).sourceTapes + 1) → List Bool) (KH0 : Fin ((code ph).sourceTapes + 1) → Nat)
    (cnt c15 q284 c17 c18 : Fin ((code ph).sourceTapes + 1)) (b q Mb Ms S Rw B U0 : Nat)
    (EF : Phase → Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)) → List Stream.Entry)
    (KU : Fin (code ph).sourceTapes → Prop) (K0U : Fin (code ph).sourceTapes → List Bool) (KH0U : Fin (code ph).sourceTapes → Nat) (fuel : Nat) : Prop :=
  -- the layout
  (∀ y, ((code ph).whole y).val = y.val) → d.F = PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 → d.U = (code ph).sourceTapes → cnt = Fin.last (code ph).sourceTapes →
  values.reserveSize = Rc → values.counterReserve = Rc → values.entries.length + 2 ≤ Rc →
  (CompareMachine.word values.entries.length).length ≤ Rc →
  
  Rest.InvR e hV Rc Rk KU K0U KH0U values.entries.length b q Mb Ms Rc Rc Rc Rc S Rw B b U0 fuel
    (values.H values.entries.length) (values.A values.entries.length) →
  EncWords hV Rc b (values.H values.entries.length) (values.A values.entries.length) →
  
  (∀ y : Fin (code ph).sourceTapes, Kc y.castSucc → KU y ∧ KH0 y.castSucc = KH0U y ∧
    ((∀ i, (code ph).whole y.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) → K0 ph (ci.val+1) y.castSucc = K0U y)) →
  (∀ y (i : Fin 19), Kc y → (code ph).whole y = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i →
    K0 ph (ci.val+1) y = cdAt sources p k n x bits (ci.val+1) i ∧ KH0 y = 0) →
  ¬ Kc (Fin.last (code ph).sourceTapes) →
  -- the query tapes
  (code ph).whole c15 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 15 → (code ph).whole c17 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 17 → (code ph).whole c18 = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) 18 →
  q284.val < d.F → (∀ i, (code ph).whole q284 ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) →
  (∃ y : Fin (code ph).sourceTapes, y.castSucc = q284 ∧ KU y ∧ (K0U y).length ≤ capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ∧ KH0U y = 0) →
  -- the entry's phase words at `ci`, the clause's entries, and the keep/append facts (`KeepHole`, `HappHole` conclusions)
  PhaseWords sources p k r scratch n x bits b EF ph ci.val A0 H0 →
  values.entries = EF ph ci → values.phasePrefix = prefixEntries (EF ph) ci.val →
  (∀ s : Fin (code ph).sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      (∀ i, (code ph).whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) →
      (code ph).whole s.castSucc ≠ Wd sources p k r scratch ph 81 →
      (code ph).whole s.castSucc ≠ Wd sources p k r scratch ph 90 →
      values.A values.entries.length s = A0 ((code ph).whole s.castSucc)) →
  (∀ s : Fin (code ph).sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      (∀ i, (code ph).whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) →
      values.H values.entries.length s = H0 ((code ph).whole s.castSucc)) →
  (A0 (Wd sources p k r scratch ph 81) = Stream.words (C10PartsSchedule.entryWidthSchedule sources k r n) values.phasePrefix →
      A0 (Wd sources p k r scratch ph 90) = CompareMachine.word values.phasePrefix.length →
      ∀ s81 s90 : Fin (code ph).sourceTapes,
        (code ph).whole s81.castSucc = Wd sources p k r scratch ph 81 →
        (code ph).whole s90.castSucc = Wd sources p k r scratch ph 90 →
        values.A values.entries.length s81 = Stream.words (C10PartsSchedule.entryWidthSchedule sources k r n) (values.phasePrefix ++ values.entries) ∧
        values.A values.entries.length s90 = CompareMachine.word (values.phasePrefix ++ values.entries).length) →
  entryInvAt3 sources p den hden k r scratch n x bits hp
    (⟨d, eX, pX, gW, eR, eV, X, (code ph).sourceTapes + 1, (code ph).whole, pl, e, Rc, Rk, Ce, Kc, K0, KH0, cnt, c15, q284, c17, c18, b, q, Mb, Ms, S, Rw, B, U0⟩ :
      EntrySite (ControllerSelectedContinuation.bodyTapes sources p k r scratch))
    EF ph (ci.val + 1)
    (install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp)) (finalA mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph ci A0 values)
      (CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) (ci.val + 1)))
    (finalH mask selector packets rows compiler sources p den hden k r scratch n x bits hp site code ph H0 values)

end nexthole

end
end NearCubicWires.SourceSteps
end

