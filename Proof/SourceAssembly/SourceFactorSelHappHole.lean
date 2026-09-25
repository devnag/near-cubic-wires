import Proof.SourceAssembly.SourceFactorSelNextHole

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceFactorSel.Next
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- The appender's tape `1` is the stream. -/
theorem app_tapes_1 (w D l rs : Nat) (en : Stream.Entry) (xs : List Stream.Entry) :
    CloseoutFinalC10AppendPositioning.tapes w D l rs en xs 1 = Stream.words w xs := rfl

/-- The appender's tape `3` is the count word. -/
theorem app_tapes_3 (w D l rs : Nat) (en : Stream.Entry) (xs : List Stream.Entry) :
    CloseoutFinalC10AppendPositioning.tapes w D l rs en xs 3 = CompareMachine.word xs.length := rfl

/-- The last call's list is the whole clause's. -/
theorem take_last_eq (es : List Stream.Entry) (e : Stream.Entry) (hN : 0 < es.length) (he : es[es.length - 1]? = some e) :
    es.take (es.length - 1) ++ [e] = es := by
  have hne : es ≠ [] := List.ne_nil_of_length_pos hN
  rw [List.getElem?_eq_getElem (by omega : es.length - 1 < es.length)] at he
  have he' := Option.some.inj he
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  rw [List.dropLast_eq_take, List.getLast_eq_getElem, he']

theorem happHole_holds (mask : MaskProducer) (selector : CyclicChoice.Laws)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
    (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (code : (ph : Phase) → RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph)
    (ph : Phase) (A0 : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool)
    (values : RCFive.Source.CallValues (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (code ph).sourceTapes) :
    HappHole mask selector packets rows sources p k r scratch n x bits code ph A0 values := by
  intro hw h1 h3 _ hpos hzero hent hA81 hA90 s81 s90 hs81 hs90
  have f81 := wd_facts sources p k r scratch true ph 81 (Or.inl rfl)
  have f90 := wd_facts sources p k r scratch true ph 90 (Or.inr rfl)
  have e81 : s81 = (code ph).app 1 := by
    apply Fin.ext
    have hv := congrArg Fin.val hs81
    rw [hw, Fin.val_castSucc] at hv
    rw [hv, h1]
  have e90 : s90 = (code ph).app 3 := by
    apply Fin.ext
    have hv := congrArg Fin.val hs90
    rw [hw, Fin.val_castSucc] at hv
    rw [hv, h3]
  have l81 : ((code ph).app 1).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 := by
    rw [h1]; exact f81.2.1
  have l90 : ((code ph).app 3).val < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 := by
    rw [h3]; exact f90.2.1
  subst e81 e90
  by_cases hN : 0 < values.entries.length
  · have hlist : (values.phasePrefix ++ values.entries.take (values.entries.length - 1)) ++
        [(⟨values.coefficient (values.entries.length - 1), values.total (values.entries.length - 1),
          values.denominator (values.entries.length - 1)⟩ : Stream.Entry)] = values.phasePrefix ++ values.entries := by
      rw [List.append_assoc, take_last_eq _ _ hN (hent _ (by omega))]
    rw [hpos hN 1 l81, hpos hN 3 l90]
    exact ⟨by rw [Bridge.appTOf, app_tapes_1, hlist], by rw [Bridge.appTOf, app_tapes_3, hlist]⟩
  · have h0 : values.entries.length = 0 := by omega
    have hnil : values.entries = [] := List.eq_nil_of_length_eq_zero h0
    rw [hzero h0 1 l81, hzero h0 3 l90, hs81, hs90, hnil, List.append_nil]
    exact ⟨hA81, hA90⟩

end
end NearCubicWires.SourceFactorSel.Next
end

