import Proof.Packets.BudgetJ5Counts
import Proof.SourceAssembly.SourceSkelClause

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size

/-- A prefix of at most `j` blocks, each of length at most `s`, has length at most `j·s`. -/
theorem prefix_length_le {α : Type} {m : ℕ} (E : Fin m → List α) (s : ℕ) (hE : ∀ c, (E c).length ≤ s) (j : ℕ) :
    (((List.ofFn E).take j).flatten).length ≤ j * s := by
  rw [List.length_flatten]
  have h1 : ((List.map List.length ((List.ofFn E).take j))).sum ≤
      ((List.map List.length ((List.ofFn E).take j))).length • s := by
    apply List.sum_le_card_nsmul
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hl)
    exact hE c
  have h2 : ((List.map List.length ((List.ofFn E).take j))).length ≤ j := by
    rw [List.length_map, List.length_take]
    exact Nat.min_le_left _ _
  rw [smul_eq_mul] at h1
  exact h1.trans (Nat.mul_le_mul_right _ h2)

section count
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den k : ℕ)

/-- Every clause's entry list has at most `siteCap termAt` entries. -/
theorem clause_entries_le {n : ℕ} (x : BitInput n) (bits : List Bool) (mode : Bool) (ph : Phase) (L : ℕ)
    (c : Fin (NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) :
    (phaseE sources p den k x bits mode ph L c).length ≤
      CloseoutFinalC10CallCountCap.siteCap
        (CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n)) := by
  show (TraceData.entriesOf _ ph c sources L _ mode).length ≤ _
  rw [TraceData.hlen]
  exact calls_le_siteCap sources k p den x bits ph c

theorem entry_count_le (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) {n : ℕ} (hn : S.onset ≤ n)
    (x : BitInput n) (bits : List Bool) (mode : Bool) (ph : Phase) (L : ℕ)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (j : ℕ) :
    (prefixEntries (phaseE sources p den k x bits mode ph L) ci.val ++
        (phaseE sources p den k x bits mode ph L ci).take j).length ≤
      C10PartsSchedule.entryWidthSchedule sources k S.exponent n := by
  set s := CloseoutFinalC10CallCountCap.siteCap
    (CloseoutFinalC10ModeNativeSchedule.termAt sources p (C10PartsSchedule.widthAt sources k n)) with hs
  have hE := clause_entries_le sources p den k x bits mode ph L
  have h1 : (prefixEntries (phaseE sources p den k x bits mode ph L) ci.val).length ≤ ci.val * s :=
    prefix_length_le _ s hE ci.val
  have h2 : ((phaseE sources p den k x bits mode ph L ci).take j).length ≤ s :=
    by
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans (hE ci)
  have hci : ci.val + 1 ≤ NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) := ci.isLt
  have hNC := nc_le_clauseAt sources k p x bits
  have h3 : (ci.val + 1) * s ≤ CloseoutFinalC10ModeNativeSchedule.callAt sources p
      (C10PartsSchedule.widthAt sources k n) := by
    unfold CloseoutFinalC10ModeNativeSchedule.callAt
    exact Nat.mul_le_mul (hci.trans hNC) le_rfl
  have h4 := (callAt_le_jointCap sources p (C10PartsSchedule.widthAt sources k n)).trans
    (jointCap_le_pow sources k p S hn)
  have h5 : (C10PartsSchedule.widthAt sources k n + 1)^S.exponent ≤
      C10PartsSchedule.entryWidthSchedule sources k S.exponent n := by
    unfold C10PartsSchedule.entryWidthSchedule C10PartsSchedule.widthPower
    exact Nat.le_add_left _ _
  rw [List.length_append]
  have e : (ci.val + 1) * s = ci.val * s + s := by ring
  omega

end count

end
end NearCubicWires.SourceBudget
end

