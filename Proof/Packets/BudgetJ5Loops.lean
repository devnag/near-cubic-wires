import Proof.Packets.BudgetJ5Counts

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
open NearCubicWires.SourceParent NearCubicWires.SourcePhase
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size

section entry
variable (sources : EightSources) (k : ℕ) {gamma : Real} (p : Parameters sources gamma)

/-- The penalty entry (`4b+23`, `SourcePhaseEntry.penalty_entry`) below `(4·floor+23+4W^r)(n+1)^r`. -/
theorem penalty_entry_le (r n : ℕ) :
    4*C10PartsSchedule.entryWidthSchedule sources k r n + 23 ≤
      (4*C10PartsSchedule.thresholdFloor sources + 23 + 4*C10PartsSchedule.widthConst sources k^r)*(n+1)^r := by
  unfold C10PartsSchedule.entryWidthSchedule C10PartsSchedule.widthPower
  have h := width_pow_le sources k n r
  have h1 : 1 ≤ (n+1)^r := Nat.one_le_pow _ _ (by omega)
  have h2 : 4*C10PartsSchedule.thresholdFloor sources + 23 ≤
      (4*C10PartsSchedule.thresholdFloor sources + 23)*(n+1)^r := Nat.le_mul_of_pos_right _ h1
  have e : (4*C10PartsSchedule.thresholdFloor sources + 23 + 4*C10PartsSchedule.widthConst sources k^r)*(n+1)^r =
      (4*C10PartsSchedule.thresholdFloor sources + 23)*(n+1)^r +
        4*(C10PartsSchedule.widthConst sources k^r*(n+1)^r) := by ring
  omega

/-- The request-size coefficient at `k`. -/
abbrev sizeC : ℕ := (2*reqC sources p + 1) * C10PartsSchedule.widthConst sources k^reqE sources p

/-- The moment/clause entry (`2·capC+4`, `SourcePhaseEntry.later_entry`), source-polynomial. -/
theorem later_entry_le {n : ℕ} (x : BitInput n) (bits : List Bool) :
    2*capC sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) + 4 ≤
      (2*PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP sources)*
          sizeC sources k p^PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) + 4)*
        (n+1)^(reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources)) := by
  have h := SourcePhase.entry_later_inClasses_capC (dP := reqE sources p*PCPPQueryCachedBounds.degree
      (CloseoutLanguage.selectedPCPP sources)) (hT := 0) (hS := 0) (m := 2) (L := 0) (qn := 0)
    sources k (PolynomialClock.ordinaryClock k) x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)
    (sizeC sources k p) (reqE sources p) (req_size_poly sources k p x bits) le_rfl
  unfold Admission.InClasses Admission.splitRHS at h
  simpa using h

end entry

/-- **The J5 constants at the actual source**, from S's site class. Exponents: `r` (clause count), `reqE`
(request size), `r+r` (fold arguments), `r + reqE·deg` (entries), `(r+r)+r` (widths) — none depends on `k`
when `r = S.exponent` (`selected` chooses it before `k`); `W = widthConst sources k` enters coefficients only. -/
def sourceConsts (sources : EightSources) (k : ℕ) {gamma : Real} (p : Parameters sources gamma)
    (r dS hT hS m L cP cT cS : ℕ) : J5Consts where
  dS := dS
  hT := hT
  hS := hS
  m := m
  L := L
  cP := cP
  cT := cT
  cS := cS
  nC := C10PartsSchedule.widthConst sources k^r
  nE := r
  sC := sizeC sources k p
  sE := reqE sources p
  xC := C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^r +
    C10PartsSchedule.widthConst sources k^(r+r)
  xE := r + r
  eC := (4*C10PartsSchedule.thresholdFloor sources + 23 + 4*C10PartsSchedule.widthConst sources k^r) +
    (2*PCPPQueryCachedBounds.coefficient (CloseoutLanguage.selectedPCPP sources)*
      sizeC sources k p^PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources) + 4)
  eE := r + reqE sources p*PCPPQueryCachedBounds.degree (CloseoutLanguage.selectedPCPP sources)
  wC := 3*((C10PartsSchedule.widthConst sources k^(r+r) + 1)*
    (C10PartsSchedule.thresholdFloor sources + 1 + C10PartsSchedule.widthConst sources k^r)) + 1
  wE := (r + r) + r

section loops

end loops

end
end NearCubicWires.SourceBudget
end

