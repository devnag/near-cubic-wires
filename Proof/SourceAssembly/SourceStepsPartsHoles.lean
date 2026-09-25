import Proof.SourceAssembly.SourceStepsStartHole

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

section holes
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

def KeepHole : Prop :=
  ∀ (A0c : Fin (code ph).sourceTapes → List Bool) (H0c : Fin (code ph).sourceTapes → Nat)
    (A1 : Fin ((code ph).sourceTapes + 1) → List Bool) (H1 : Fin ((code ph).sourceTapes + 1) → Nat),
  -- the code: `whole` is the identity on values; slots and `enc` tapes lie at or above `offset + 1155`; the `app` tapes below are `Wd ph 81/90`
  (∀ y, ((code ph).whole y).val = y.val) →
  (∀ i, PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ ((code ph).slots i).val) → (∀ i, PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ ((code ph).enc i).val) →
  (∀ i, ((code ph).app i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 →
    ((code ph).app i).val = (Wd sources p k r scratch ph 81).val ∨ ((code ph).app i).val = (Wd sources p k r scratch ph 90).val) →
  -- the chain's end = its start on the low tapes off `278/279` and off `app` (`Inv5` conjunct 2 at `N`), and the `app` heads (conjunct 3)
  (∀ z : Fin (code ph).sourceTapes, z.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 → z.val ≠ 278 → z.val ≠ 279 → (∀ i, (code ph).app i ≠ z) →
    values.A values.entries.length z = A0c z ∧ values.H values.entries.length z = H0c z) →
  (∀ i, ((code ph).app i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 → values.H values.entries.length ((code ph).app i) = H0c ((code ph).app i)) →
  -- the chain start = the first cycle's exit off the slots/`enc`/`app` (and on heads everywhere)
  (∀ z : Fin (code ph).sourceTapes, (∀ i, (code ph).slots i ≠ z) → (∀ i, (code ph).enc i ≠ z) → (∀ i, (code ph).app i ≠ z) →
    A0c z = A1 z.castSucc) →
  (∀ z : Fin (code ph).sourceTapes, H0c z = H1 z.castSucc) →
  -- the first cycle's exit = the site's original bank on the low tapes off the cache, `278..284` (`ChainStartP` (4))
  (∀ z : Fin (code ph).sourceTapes, z.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 → z.val ≠ 278 → z.val ≠ 279 →
    (∀ i, z.val ≠ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i).val) → (z.val < 278 ∨ 284 < z.val) →
    A1 z.castSucc = queriedAt sources p den hden k r scratch n x bits hp ci.val A0 ((code ph).whole z.castSucc) ∧
    H1 z.castSucc = H0 ((code ph).whole z.castSucc)) →
  (∀ s : Fin (code ph).sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      (∀ i, (code ph).whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) →
      (code ph).whole s.castSucc ≠ Wd sources p k r scratch ph 81 →
      (code ph).whole s.castSucc ≠ Wd sources p k r scratch ph 90 →
      values.A values.entries.length s = A0 ((code ph).whole s.castSucc)) ∧
  (∀ s : Fin (code ph).sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      (∀ i, (code ph).whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) →
      values.H values.entries.length s = H0 ((code ph).whole s.castSucc))

def CacheHole : Prop :=
  ∀ (Kc : Fin (code ph).sourceTapes → Prop) (K0 : Fin (code ph).sourceTapes → List Bool) (KH0 : Fin (code ph).sourceTapes → Nat),
  (∀ z, Kc z → values.A values.entries.length z = K0 z ∧ values.H values.entries.length z = KH0 z) →
  (∀ (i : Fin 19) (s : Fin (code ph).sourceTapes), (code ph).whole s.castSucc = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i →
    Kc s ∧ K0 s = CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ci.val i ∧ KH0 s = 0) →
  (∀ (i : Fin 19) (s : Fin (code ph).sourceTapes),
      (code ph).whole s.castSucc = PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i →
      values.H values.entries.length s = 0 ∧ values.A values.entries.length s = CD sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) ci.val i)

def HappHole : Prop :=
  (∀ y, ((code ph).whole y).val = y.val) →
  ((code ph).app 1).val = (Wd sources p k r scratch ph 81).val → ((code ph).app 3).val = (Wd sources p k r scratch ph 90).val →
  (∀ i, ((code ph).app i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 → i = 1 ∨ i = 3) →
  -- the chain's end on the low `app` tapes (`Inv5` conjunct 3 at `N`), or the entry bank when the clause has no call
  (0 < values.entries.length → ∀ i, ((code ph).app i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 →
    values.A values.entries.length ((code ph).app i) =
      Bridge.appTOf (C10PartsSchedule.entryWidthSchedule sources k r n) values (values.entries.length - 1) i) →
  (values.entries.length = 0 → ∀ i, ((code ph).app i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 →
    values.A values.entries.length ((code ph).app i) = A0 ((code ph).whole ((code ph).app i).castSucc)) →
  (∀ j, j < values.entries.length →
    values.entries[j]? = some (⟨values.coefficient j, values.total j, values.denominator j⟩ : Stream.Entry)) →
  (A0 (Wd sources p k r scratch ph 81) = Stream.words (C10PartsSchedule.entryWidthSchedule sources k r n) values.phasePrefix →
      A0 (Wd sources p k r scratch ph 90) = CompareMachine.word values.phasePrefix.length →
      ∀ s81 s90 : Fin (code ph).sourceTapes,
        (code ph).whole s81.castSucc = Wd sources p k r scratch ph 81 →
        (code ph).whole s90.castSucc = Wd sources p k r scratch ph 90 →
        values.A values.entries.length s81 = Stream.words (C10PartsSchedule.entryWidthSchedule sources k r n) (values.phasePrefix ++ values.entries) ∧
        values.A values.entries.length s90 = CompareMachine.word (values.phasePrefix ++ values.entries).length)

end holes

end
end NearCubicWires.SourceSteps
end

