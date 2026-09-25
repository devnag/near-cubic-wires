import Proof.SourceAssembly.SourceSkelSeam3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
namespace NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section code
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

/-- The code's `enc` placement (`seam3_spec`'s `hencP`). -/
theorem hencP_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) (i : Fin 11) :
    (𝔇).F ≤ ((skelCodeR mask packets rows sources res hres p k r ph refill preF).enc i).val ∧
      ((skelCodeR mask packets rows sources res hres p k r ph refill preF).enc i).val < (𝔇).G := by
  have hi := i.isLt
  have hrt : 19 ≤ r_tapes (printerOf sources) := by unfold r_tapes; omega
  show PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ _ ∧
    _ < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) + 13
  simp only [skelCodeR]
  split_ifs <;> constructor <;> omega

/-- The code's `app` placement (`seam3_spec`'s `happP`). -/
theorem happP_R (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) (i : Fin 6) :
    ((skelCodeR mask packets rows sources res hres p k r ph refill preF).app i).val < (𝔇).F ∨
      ((𝔇).F ≤ ((skelCodeR mask packets rows sources res hres p k r ph refill preF).app i).val ∧
        ((skelCodeR mask packets rows sources res hres p k r ph refill preF).app i).val < (𝔇).G) := by
  have h81 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 81
  have h90 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 90
  simp only [SourceParent.Wd] at h81 h90
  show appVal mask packets rows sources res p k r ph i < PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ∨
    (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 ≤ appVal mask packets rows sources res p k r ph i ∧
      appVal mask packets rows sources res p k r ph i <
        PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + r_tapes (printerOf sources) + 13)
  fin_cases i <;> simp [appVal] <;> omega

/-- A phase word slot other than the two width slots is NOT the counter (`phaseBank` puts it at `i < 278` or above `offset + 599`). -/
theorem wd_ne_terminal (ph : Phase) (i : Fin 278) (h4 : i.val ≠ 274) (h5 : i.val ≠ 275) :
    (SourceParent.Wd sources p k r (scratchOf mask packets rows sources res) ph i).val ≠
      PCJda54a286946142d3_BranchPhases.offset sources p k r + 53 := by
  have hi := i.isLt
  have hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
  simp only [SourceParent.Wd, CloseoutFinalC10RetainedPhaseFold.wordSlots, if_neg h4, if_neg h5]
  have hp := (C10TailUniformSlots.phaseIndex ph).isLt
  dsimp only [CloseoutFinalC10RetainedPhaseFold.phaseBank]
  split
  · simp only; omega
  · simp only; omega

end code

end
end NearCubicWires.SourceSkeleton
end
