import Proof.SourceAssembly.SourcePhaseFuel

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. The per-phase fuel `ofLoops` demands, at a fixed site-fuel function -/

section fuel
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den k r n : Nat)
  (x : BitInput n) (bits : List Bool)

/-- The fixed phase-entry fuel: `4b+23` for the penalty entry, `2C+4` for the later entries. -/
def entryFuelOf (ph : Phase) : Nat :=
  match ph with
  | .penalty => 4*(C10PartsSchedule.entryWidthSchedule sources k r n)+23
  | .moment => 2*(capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))+4
  | .clause => 2*(capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))+4

/-- The per-clause cost bound at site fuel `sf ph` (`ofLoops`'s `cp`, `hcp` with equality at the bound). -/
def cpOf (sf : Phase → Nat) (ph : Phase) : Nat :=
  4*(NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
    ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)+sf ph+21

/-- **The phase fuel** at site fuel `sf`: `entry + 1 + (N·(cp+3) + 3 + 1 + fold)`, with the fold's entry count the
phase polynomial's monomial count (every loop has exactly that many entries, `loop_entries_length`). -/
def costOf (sf : Phase → Nat) : Phase → Nat := fun ph =>
  entryFuelOf sources p k r n x bits ph+1+((NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))*(cpOf sources p k n x bits sf ph+3)+3+1+
    CloseoutFinalC10RetainedPhaseFold.fuel (C10PartsSchedule.entryWidthSchedule sources k r n) (Poly sources p k den (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length)

end fuel

theorem cost_eq {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool} {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states} {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (sf : Phase → Nat) (ph : Phase)
    (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph (C10PartsSchedule.entryWidthSchedule sources k r n) (code ph)) :
    costOf sources p den k r n x bits sf ph = entryFuelOf sources p k r n x bits ph+1+((NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))*(cpOf sources p k n x bits sf ph+3)+3+1+
      CloseoutFinalC10RetainedPhaseFold.fuel (C10PartsSchedule.entryWidthSchedule sources k r n) L.entries.length) := by
  unfold costOf
  rw [loop_entries_length L]

theorem width_eq {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool} {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states} {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (ph : Phase)
    (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph (C10PartsSchedule.entryWidthSchedule sources k r n) (code ph)) :
    CompetitorSumWidth.width (Poly sources p k den (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph).monomials.length (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) =
      CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width (C10PartsSchedule.entryWidthSchedule sources k r n)) L.entries := by
  unfold CloseoutFinalC10WorkerFold.foldWidth
  rw [CloseoutFinalC10WorkerJoin.contributions_length, loop_entries_length L]

theorem cp_le {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {den : Nat} {hden : 0 < den} {k r scratch n : Nat} {x : BitInput n} {bits : List Bool} {hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true} {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states} {code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph} (sf : Phase → Nat) (ph : Phase)
    (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph (C10PartsSchedule.entryWidthSchedule sources k r n) (code ph))
    (hsf : L.siteFuel ≤ sf ph) :
    4*(NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
      ((req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).circuit.size+(req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity)+L.siteFuel+21 ≤ cpOf sources p k n x bits sf ph := by
  unfold cpOf
  omega

/-! ## 2. The loop contract (THE HOLE) -/

/-- **One phase's clause loop from a given start bank** (owed by the per-clause cycle). Starts exactly at
`(A0, H0)`, uses one live scale and the phase's accuracy target at every clause (row D3), stays within the site
fuel `sf`, and ends in the exit invariant. -/
structure LoopOut (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (compiler : Packets.CompilerLaws)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (sf : Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat)
    (InvN : (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) → (Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) → Prop) where
  L : ClauseLoop mask selector packets rows compiler sources p k den r scratch (PolynomialClock.ordinaryClock k) n x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits site (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) ph (C10PartsSchedule.entryWidthSchedule sources k r n) (code ph)
  hA0 : L.A 0 = A0
  hH0 : L.H 0 = H0
  liveScale : Nat
  hL : ∀ c, (L.values c).L = liveScale
  hT : ∀ c, (L.values c).target = (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
  hsf : L.siteFuel ≤ sf
  hexit : InvN (L.A (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L.H (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))

/-! ## 3. The composition -/

end
end NearCubicWires.SourceSkeleton
end
