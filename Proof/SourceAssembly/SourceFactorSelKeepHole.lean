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
namespace NearCubicWires.SourceFactorSel.Keep
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

theorem keepHole_holds (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)))
    (H0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → Nat) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes) :
    KeepHole mask selector packets rows sources p den hden k r scratch n x bits hp code ph ci H0 A0 values := by
  intro A0c H0c A1 H1 hw hsl hen happ hchain happH hstart hstartH hfirst
  have hoff := offset_ge_300 sources p k r
  -- a region tape: below `L + 1155`, not `278/279`, below `278` or above `284`
  have reg : ∀ s : Fin (code ph).sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      s.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ∧ s.val ≠ 278 ∧ s.val ≠ 279 ∧ (s.val < 278 ∨ 284 < s.val) := by
    intro s hs
    unfold Region at hs
    omega
  -- `whole` is the identity on values
  have wval : ∀ s : Fin (code ph).sourceTapes, ((code ph).whole s.castSucc).val = s.val := by
    intro s
    rw [hw s.castSucc, Fin.val_castSucc]
  have ncache : ∀ s : Fin (code ph).sourceTapes,
      (∀ i, (code ph).whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) →
      ∀ i, s.val ≠ (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i).val := by
    intro s h i e
    exact h i (Fin.ext ((wval s).trans e))
  -- the first cycle's exit on a region tape off the cache
  have first_eq : ∀ s : Fin (code ph).sourceTapes, Region (PCJda54a286946142d3_BranchPhases.offset sources p k r) s.val →
      (∀ i, (code ph).whole s.castSucc ≠ PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp) i) →
      A1 s.castSucc = A0 ((code ph).whole s.castSucc) ∧ H1 s.castSucc = H0 ((code ph).whole s.castSucc) := by
    intro s hs hc
    obtain ⟨h1, h2, h3, h4⟩ := reg s hs
    obtain ⟨ha, hh⟩ := hfirst s h1 h2 h3 (ncache s hc) h4
    exact ⟨ha.trans (queriedAt_off sources p den hden k r scratch n x bits hp ci.val A0 _ hc), hh⟩
  -- a low tape is no slot and no `enc` tape
  have nslot : ∀ s : Fin (code ph).sourceTapes, s.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 →
      ∀ i, (code ph).slots i ≠ s := by
    intro s h1 i e
    have h := hsl i
    rw [e] at h
    omega
  have nenc : ∀ s : Fin (code ph).sourceTapes, s.val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 →
      ∀ i, (code ph).enc i ≠ s := by
    intro s h1 i e
    have h := hen i
    rw [e] at h
    omega
  refine ⟨?_, ?_⟩
  · intro s hs hc h81 h90
    obtain ⟨h1, h2, h3, _⟩ := reg s hs
    have napp : ∀ i, (code ph).app i ≠ s := by
      intro i e
      have hv : ((code ph).app i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 := by
        rw [e]
        exact h1
      have es : s.val = ((code ph).app i).val := (congrArg Fin.val e).symm
      rcases happ i hv with e81 | e90
      · exact h81 (Fin.ext ((wval s).trans (es.trans e81)))
      · exact h90 (Fin.ext ((wval s).trans (es.trans e90)))
    obtain ⟨hA, _⟩ := hchain s h1 h2 h3 napp
    rw [hA, hstart s (nslot s h1) (nenc s h1) napp, (first_eq s hs hc).1]
  · intro s hs hc
    obtain ⟨h1, h2, h3, _⟩ := reg s hs
    have hN : values.H values.entries.length s = H0c s := by
      by_cases ha : ∃ i, (code ph).app i = s
      · obtain ⟨i, e⟩ := ha
        have hv : ((code ph).app i).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 := by
          rw [e]
          exact h1
        have h := happH i hv
        rw [e] at h
        exact h
      · exact (hchain s h1 h2 h3 (fun i e => ha ⟨i, e⟩)).2
    rw [hN, hstartH s, (first_eq s hs hc).2]

end
end NearCubicWires.SourceFactorSel.Keep
end

