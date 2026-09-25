import Proof.Packets.SrcRes284Ready
import Proof.SourceAssembly.SourceStepsResidue

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceParent
namespace NearCubicWires.SourceStart.Res284
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSteps
noncomputable section

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- **The penalty entry's tape 284 is the exponentiator's work word.** -/
theorem penalty_284 (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : j.val = 284) :
    penaltyA0 sources p den hden k r scratch n x bits hp j =
      expWork (RepairSource.CloseoutLanguage.clauseWidth p.clauseDegree (C10PartsSchedule.widthAt sources k n)) := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hP := size_302 sources p k r
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have hsp := PCJda54a286946142d3_BranchPhases.space sources p k r scratch
  have hA : penaltyA0 sources p den hden k r scratch n x bits hp j =
      PCJ374c44bb8b7f47d9_.S.bank sources p den hden k r scratch n x bits hp (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) := by
    have hvals : ∀ i, (fSlots sources p k r scratch i).val = 218 ∨
        PCJda54a286946142d3_BranchPhases.offset sources p k r + 124 ≤ (fSlots sources p k r scratch i).val := by
      intro i
      fin_cases i <;> simp [fSlots, CloseoutFinalC10FirstPhaseEntry.firstSlots]
    unfold penaltyA0
    refine install_other _ _ _ _ (fun i he => ?_)
    have hv := congrArg Fin.val he
    have hvi := hvals i
    omega
  have hb : (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j).val =
      WorkspaceSelectedAdmission.originalTapes sources p k + 2 + j.val :=
    body_mid ht hP hsp j (by omega) (by omega)
  rw [hA]
  unfold PCJ374c44bb8b7f47d9_.S.bank
  have hlt : WorkspaceSelectedAdmission.originalTapes sources p k + 2 + 284 <
      PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch := by
    have h := (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j).isLt
    rw [hb, hj] at h
    exact h
  have e : PCJda54a286946142d3_BranchPhases.body sources p k r scratch j =
      ⟨WorkspaceSelectedAdmission.originalTapes sources p k + 2 + 284, hlt⟩ :=
    Fin.ext (by rw [hb, hj])
  rw [e]
  exact readyBank_284 sources p den hden k r (ControllerSelectedContinuation.extra sources p k r scratch)
    (PCJ687b3b71abe848ce_.space sources p k r scratch) n x bits hp

/-- **Its length: `2·cw + 7`.** -/
theorem penalty_284_len (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : j.val = 284) :
    (penaltyA0 sources p den hden k r scratch n x bits hp j).length =
      2 * RepairSource.CloseoutLanguage.clauseWidth p.clauseDegree (C10PartsSchedule.widthAt sources k n) + 7 := by
  rw [penalty_284 sources p den hden k r scratch n x bits hp j hj, expWork_length]

end
end NearCubicWires.SourceStart.Res284

