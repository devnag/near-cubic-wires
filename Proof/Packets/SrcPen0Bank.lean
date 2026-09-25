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
namespace NearCubicWires.SourceStart.Pen0
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSteps
noncomputable section

theorem header_ne_one {t : Nat} (m offset O F V : Nat) (h : offset + t ≤ m) (i : Fin t) :
    (CloseoutWitness.HeaderDock.slots m offset O F V h i).val ≠ 1 := by
  unfold CloseoutWitness.HeaderDock.slots
  by_cases hF : i.val = F
  · rw [if_pos hF]; show 118 ≠ 1; decide
  rw [if_neg hF]
  by_cases hO : i.val = O
  · rw [if_pos hO]; show 78 ≠ 1; decide
  rw [if_neg hO]
  by_cases h2 : i.val = 2
  · rw [if_pos h2]; show 0 ≠ 1; decide
  rw [if_neg h2]
  by_cases hV : i.val = V
  · rw [if_pos hV]; show 150 ≠ 1; decide
  rw [if_neg hV]
  show 150 + (1 + offset + i.val) ≠ 1
  omega

theorem dock_old_ne_one {m t : Nat} (old : Fin m → Fin t) (x : Fin m) (h : (old x).val ≠ 1) :
    (CloseoutWitness.SupportDock.slots old (x.castAdd 1)).val ≠ 1 := by
  rw [CloseoutWitness.SupportDock.slots_old]; exact h

theorem ready_cache_ne_one (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k : Nat) (mode : Bool)
    (i : Fin 19) : (WorkspaceSelectedEntryReady.cache sources p k mode i).val ≠ 1 := by
  unfold WorkspaceSelectedEntryReady.cache CloseoutFinalC10ColdCacheAtAdmission.cacheSlot
    CloseoutWitness.BoundedFamilySupport.slots CloseoutWitness.ColdFamilySupport.cache
  exact dock_old_ne_one _ _ (header_ne_one _ _ _ _ _ _ _)

section penalty
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

theorem penalty_residue5 (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (h1 : 278 ≤ j.val) (h2 : j.val < 285) :
    (penaltyA0 sources p den hden k r scratch n x bits hp j).length ≤
        P1TopDown.WorkspaceSelectedEntryBudget.envelope sources p k r n + 1 ∧
      PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = 0 := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hP := size_302 sources p k r
  have ht := WorkspaceSelectedEntryReady.old_size sources p k
  have hsp := PCJda54a286946142d3_BranchPhases.space sources p k r scratch
  have hoff : PCJda54a286946142d3_BranchPhases.offset sources p k r =
      WorkspaceSelectedEntry.size sources k r p.clauseDegree + WorkspaceSelectedAdmission.originalTapes sources p k - 2 := rfl
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
  obtain ⟨-, -, -, -, -, -, -, -, hheads, -⟩ := penalty_bank sources p den hden k r scratch n x bits hp
  refine ⟨?_, hheads j (by omega)⟩
  rw [hA]
  have hstep := PCJ687b3b71abe848ce_.ready_step sources p den hden k r (ControllerSelectedContinuation.extra sources p k r scratch)
    (PCJ687b3b71abe848ce_.space sources p k r scratch) n x bits hp
  have hb : (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j).val =
      WorkspaceSelectedAdmission.originalTapes sources p k + 2 + j.val :=
    body_mid ht hP hsp j h1 (by omega)
  have h0 : (PCJ687b3b71abe848ce_.initialBank sources p den hden k (ControllerSelectedContinuation.extra sources p k r scratch) n x bits
      (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j)).length ≤ P1TopDown.WorkspaceSelectedEntryBudget.envelope sources p k r n + 1 := by
    unfold PCJ687b3b71abe848ce_.initialBank
    rw [finalBank_fresh _ _ _ _ (by omega)]
    exact Nat.zero_le _
  exact RepairOrdinary.CloseoutFinalC10BandRecycle.band_length_at_cost _ _ hstep _ rfl h0

/-- **The penalty entry's tape `1` is the witness frame** (head `0`). -/
theorem penalty_1 (j : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch)) (hj : j.val = 1) :
    penaltyA0 sources p den hden k r scratch n x bits hp j = RepairOrdinary.frame bits ∧
      PCJ374c44bb8b7f47d9_.S.heads sources p k r scratch (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j) = 0 := by
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  have hP := size_302 sources p k r
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
  obtain ⟨-, -, -, -, -, -, -, -, hheads, -⟩ := penalty_bank sources p den hden k r scratch n x bits hp
  refine ⟨?_, hheads j (by omega)⟩
  rw [hA]
  obtain ⟨A, L, _oracle0, w, out, -, -, -, -, hbank, -⟩ := ready_installed sources p den hden k r scratch n x bits hp
  rw [hbank]
  have hb1 : (PCJda54a286946142d3_BranchPhases.body sources p k r scratch j).val = 1 := by
    show ControllerSelectedLayout.location _ _ j.val = 1
    simp [ControllerSelectedLayout.location, hj]
  rw [install_other _ _ _ _ (fun i he => ?_)]
  · have e1 : PCJda54a286946142d3_BranchPhases.body sources p k r scratch j =
        WorkspaceSelectedEntry.slots (WorkspaceSelectedEntryReady.old_size sources p k) (size_fit sources p k r scratch)
          ⟨1, by omega⟩ := Fin.ext (by rw [hb1]; simp [WorkspaceSelectedEntry.slots])
    rw [e1, install_slot _ (WorkspaceSelectedEntry.slots_injective _ _)]
    unfold WorkspaceSelectedEntry.output
    rw [show (⟨1, by omega⟩ : Fin (WorkspaceSelectedEntry.size sources k r p.clauseDegree)) =
        Fin.castAdd 1 (⟨1, by omega⟩ :
          Fin (218 + (60 + (WorkspaceSelectedEntry.engineTapes sources k r p.clauseDegree + 23)))) from Fin.ext rfl,
      Fin.addCases_left]
    rfl
  · have hv := congrArg Fin.val he
    rw [hb1] at hv
    have hi := i.isLt
    by_cases hc : i.val < 19
    · simp only [WorkspaceSelectedEntryInit.ports, dif_pos hc, Fin.val_castAdd] at hv
      exact ready_cache_ne_one sources p k _ ⟨i.val, hc⟩ hv
    · simp only [WorkspaceSelectedEntryInit.ports, dif_neg hc] at hv
      split_ifs at hv <;> omega

end penalty

end
end NearCubicWires.SourceStart.Pen0

