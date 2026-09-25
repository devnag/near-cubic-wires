import Proof.SourceAssembly.SourcePhaseRecords

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourcePhase
open NearCubicWires.SourceParent
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section mode
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (k den : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
  (bits : List Bool)

/-- Every capped coordinate is in the witness's mode. -/
theorem coord_mode (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j).FactorsSatisfy
      (C10NaturalModeAtoms.ModeAtom (CloseoutWitness.BoundedFields.symmetric bits)) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k clock p den x oracle bits hs j]
    refine C10SiteWireEnvelope.mapPolynomial_factorsSatisfy _ _ _ ?_
    intro monomial hmonomial atom hatom
    exact hs
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k clock p den x oracle bits hs j]
    refine C10SiteWireEnvelope.mapPolynomial_factorsSatisfy _ _ _ ?_
    intro monomial hmonomial atom hatom
    exact Bool.eq_false_iff.mpr hs

/-- Every clause's calls are in the witness's mode. -/
theorem site_mode (ph : Phase) (ci : Fin (2 ^ (pcppAt sources k clock x oracle).clauseBits)) :
    (CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k clock x oracle)
      (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) C10TotalDecode.Atom.systematic ci).FactorsSatisfy
      (C10NaturalModeAtoms.ModeAtom (CloseoutWitness.BoundedFields.symmetric bits)) :=
  C10SiteWireEnvelope.siteCalls_factorsSatisfy ph _ _ _ _ (coord_mode sources p k den clock x oracle bits)
    (fun _ => by trivial) ci

end mode

section loop
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
    {rows : PCJc4297ab269d8423a_Source.RowLibrary selector} {compiler : Packets.CompilerLaws}
    {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    {k den r scratch : Nat} {clock : OrdinaryClock (fun n => n^(k+2))} {n : Nat} {x : BitInput n}
    {oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n)}
    {bits : List Bool}
    {site : Bool → Phase → Σ states, Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states}
    {mode : Bool} {ph : Phase} {b : Nat}
    {code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph}

/-- **D2 (`hmode`).** -/
theorem loop_hmode (L : ClauseLoop mask selector packets rows compiler sources p k den r scratch clock n x oracle bits
      site mode ph b code) (hm : mode = CloseoutWitness.BoundedFields.symmetric bits) :
    ∀ m ∈ loopOrder L, ∀ atom ∈ m.factors, C10NaturalModeAtoms.ModeAtom mode atom := by
  intro m hm' atom hatom
  rw [hm]
  obtain ⟨l, hl, hml⟩ := List.mem_flatten.mp hm'
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
  have hcall := ((L.trace c)._horder).subset hml
  exact site_mode sources p k den clock x oracle bits ph c m hcall atom hatom

end loop

section mass
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (k den : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
  (bits : List Bool)

/-- **D4 (`hmass`)** at the frozen limits `stageLimits`. -/
theorem phase_hmass (ph : Phase) :
    (Poly sources p k den clock n x oracle bits ph).coefficientMass ≤
      C10FamilyMass.siteMassBound (CloseoutFinalC10StageFields.stageLimits sources p).coefficientMassCap ph := by
  apply C10FamilyMass.phasePolynomial_coefficientMass_le
  intro j
  have h := PCJd04de0277f804fcc_.coefficientMass_le sources k clock p den x oracle bits j
  have hs : (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).coefficientMassCap =
      (CloseoutFinalC10StageFields.stageLimits sources p).coefficientMassCap := rfl
  have ht : (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle).coefficientMassCap =
      (CloseoutFinalC10StageFields.stageLimits sources p).coefficientMassCap := rfl
  split_ifs at h
  · exact h.trans (le_of_eq hs)
  · exact h.trans (le_of_eq ht)

/-- **D6 (`htarget`).** -/
theorem phase_htarget (ph : Phase) :
    C10SupplierAccuracyChain.accuracyTarget (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p) ph ≤
      C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p) :=
  C10SupplierAccuracyChain.accuracyTarget_le_all _ _ ph

/-- **D6 (`htargetpos`).** -/
theorem phase_htargetpos :
    0 < C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p) :=
  C10ThresholdNaturalFit.accuracyTargetAll_pos _ _
    (CloseoutSampledWitness.mass_nonneg _ p.hd p.hh p.copies)

end mass

end
end NearCubicWires.SourcePhase
end
