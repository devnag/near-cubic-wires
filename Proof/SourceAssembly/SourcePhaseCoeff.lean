import Proof.CaseAnalysis.FinalModeNativeSchedule
import Proof.SourceAssembly.SourcePhaseMass

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

section fits
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (k den : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
  (bits : List Bool)

/-- Every capped coordinate fits the capped decoder's coefficient-bit cap. -/
theorem polynomialFits_capped (j : Fin (CloseoutWitnessPolicy.variableCount sources k clock x oracle)) :
    C10SiteCoefficientsFit.PolynomialFits
      (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).coefficientBitCap
      (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits j) := by
  by_cases hs : CloseoutWitness.BoundedFields.symmetric bits = true
  · rw [PCJd04de0277f804fcc_.coordinate_sym sources k clock p den x oracle bits hs j]
    exact C10SumFamilyTransport.polynomialFits_map_familyCoordinate _ rfl _ j
  · rw [PCJd04de0277f804fcc_.coordinate_thr sources k clock p den x oracle bits hs j]
    have ht : (P1Independent.CappedDecode.thrLimits sources k clock p den x oracle).coefficientBitCap =
        (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).coefficientBitCap := rfl
    rw [← ht]
    exact C10SumFamilyTransport.polynomialFits_map_familyCoordinate _ rfl _ j

/-- Every clause's calls fit. -/
theorem site_fits (ph : Phase) (ci : Fin (2 ^ (pcppAt sources k clock x oracle).clauseBits)) :
    C10SiteCoefficientsFit.PolynomialFits
      ((pcppAt sources k clock x oracle).clauseBits +
        4 * (P1Independent.CappedDecode.symLimits sources k clock p den x oracle).coefficientBitCap + 2)
      (CloseoutFinalC10SupplierCalls.siteCalls ph (pcppAt sources k clock x oracle)
        (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) C10TotalDecode.Atom.systematic ci) :=
  C10SiteCoefficientsFit.polynomialFits_siteCalls ph _ _ _ (polynomialFits_capped sources p k den clock x oracle bits) ci

/-- The phase polynomial fits any width above the capped `coefficientBound`. -/
theorem phase_fits (ph : Phase) (w : Nat)
    (hw : C10SiteCoefficientsFit.coefficientBound (P1Independent.CappedDecode.symLimits sources k clock p den x oracle)
      (pcppAt sources k clock x oracle) ≤ w) :
    CloseoutFinalC10SupplierCalls.CoefficientsFit w (Poly sources p k den clock n x oracle bits ph) := by
  intro m hm
  have hmem := (phase_monomials_perm ph (pcppAt sources k clock x oracle)
    (PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits) C10TotalDecode.Atom.systematic).subset hm
  obtain ⟨l, hl, hml⟩ := List.mem_flatten.mp hmem
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
  have hfit := C10SiteCoefficientsFit.coefficientsFit_of_polynomialFits (entryWidth := w) (site_fits sources p k den clock x oracle bits ph c)
    (by unfold C10SiteCoefficientsFit.coefficientBound at hw; omega)
  exact hfit m hml

end fits

section sched
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k den : Nat)

/-- **D5 (`hcoeff`)** at the schedule width, past the `Selection` onset. -/
theorem phase_hcoeff (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : Nat} (hn : S.onset ≤ n)
    (x : BitInput n) (bits : List Bool) (ph : Phase) :
    CloseoutFinalC10SupplierCalls.CoefficientsFit (C10PartsSchedule.entryWidthSchedule sources k S.exponent n)
      (Poly sources p k den (PolynomialClock.ordinaryClock k) n x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits ph) := by
  apply phase_fits
  have hb := CloseoutFinalC10ClauseBitsUniform.coefficientBound_le sources k p n x bits
  have hc := (S.caps hn).2.1
  exact hb.trans hc

/-- The capped worker's onset (the guard of `SourceObligations`) dominates the continuation's `base`. -/
theorem base_le_onset (hden : 0 < den) (C : SelectedAssembly.ContinuationData sources p) :
    C.base ≤ (ControllerCappedSelected.workerData sources p den hden
      (ControllerCappedSelected.programData den C)).onset := by
  unfold ControllerCappedSelected.workerData
  exact le_trans (le_max_left _ _) (le_max_left _ _)

end sched

end
end NearCubicWires.SourcePhase
end
