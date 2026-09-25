import Proof.SourceAssembly.SourceStepsSeamNum
import Proof.SourceAssembly.SourceStepsHfit

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
open NearCubicWires.SourceSkeleton NearCubicWires.SourceParent NearCubicWires.SourcePhase
open NearCubicWires.SourcePhase
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ModeNativeEnvelope
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section capped
variable (sources : EightSources) (k : Nat) {gamma : Real} (p : Parameters sources gamma) (den : Nat)
  {n : Nat} (x : BitInput n)
  (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k (PolynomialClock.ordinaryClock k)).result.pcp.nativeWidth n))
  (bits : List Bool)

/-- **The empty request's denominator** (the terminal call past the monomial count) is below `2^nativeDenBits`. -/
theorem fraction_den_le_nil (liveScale : Nat) :
    (LiveRows.fraction sources liveScale
      (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
      (CloseoutWitness.BoundedFields.symmetric bits)
      ([] : List (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x oracle)))).2 ≤
      2 ^ nativeDenBits sources k p n := by
  cases hs : CloseoutWitness.BoundedFields.symmetric bits
  · have hbound := thr_den_le (decompositionOf sources) liveScale
      (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
      ⟨_, ([] : List (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x oracle))).map
        C10NaturalModeAtoms.nativeThresholdAtom⟩
      (nativeWireCap sources k n) (nativeDescCap sources k p n) (by simp) (by simp) (by simp)
    exact hbound.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (le_max_right _ _) _))
  · have hbound := sym_den_le liveScale
      (C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p))
      ⟨_, ([] : List (C10TotalDecode.Atom (pcppAt sources k (PolynomialClock.ordinaryClock k) x oracle))).map
        C10NaturalModeAtoms.nativeSymmetricAtom⟩
      (nativeWireCap sources k n) (by simp) (by simp)
    exact hbound.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (le_max_left _ _) _))

end capped

section clause
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
    (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
    (hp : P1Independent.CappedLegalAdmission.passed sources p
      (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
      (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)
    (ph : Phase)
    (ci : Fin (NC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))) (L : Nat)

set_option hygiene false in
local notation "oracleC" => C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits
set_option hygiene false in
local notation "coordC" => PCJd04de0277f804fcc_.coordinate sources k (PolynomialClock.ordinaryClock k) p den x oracleC bits
set_option hygiene false in
local notation "tgtC" => C10SupplierAccuracyChain.accuracyTargetAll (constantsOf sources) (CloseoutFinalC10StageFields.stageLimits sources p)
set_option hygiene false in
local notation "modeC" => PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp
set_option hygiene false in
local notation "vQ" => (req sources k (PolynomialClock.ordinaryClock k) x oracleC).arity
set_option hygiene false in
local notation "reqM" => requestAt coordC ph ci L tgtC modeC m
set_option hygiene false in
local notation "vPm" => PacketsGlue.RequestMeta.primeCountOf (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC m)
set_option hygiene false in
local notation "vEm" => PacketsGlue.RequestMeta.seedCount (decompositionOf sources) (requestAt coordC ph ci L tgtC modeC m)

/-- **Every call's record denominator** (the terminal empty request included) is below `2^nativeDenBits`. -/
theorem den_le_at (m : Nat) :
    (TraceData.fractionOf coordC ph ci sources L tgtC modeC m).2 ≤ 2 ^ nativeDenBits sources k p n := by
  have hm : modeC = CloseoutWitness.BoundedFields.symmetric bits := (SourcePhase.penalty_bank sources p den hden k r scratch n x bits hp).1
  show (LiveRows.fraction sources L tgtC modeC (SourceRequest.FactorLoop.factorsAt coordC ph ci m)).2 ≤ _
  rw [hm]
  by_cases hlt : m < (monomials coordC ph ci).length
  · rw [SourceRequest.FactorLoop.factorsAt_of_lt coordC ph ci m hlt]
    exact SourcePhase.fraction_den_le sources k p den x oracleC bits L ph ci _ (List.getElem_mem hlt)
  · have hnil : SourceRequest.FactorLoop.factorsAt coordC ph ci m = [] := by
      unfold SourceRequest.FactorLoop.factorsAt
      rw [List.getElem?_eq_none (by omega)]
    rw [hnil]
    exact fraction_den_le_nil sources k p x oracleC bits L

theorem f6_den (m : Nat) :
    vPm * vEm * 2 ^ vQ = (TraceData.fractionOf coordC ph ci sources L tgtC modeC m).2 :=
  (SourceBudget.denominator_at sources coordC ph ci L tgtC modeC m).symm

/-- **`hsecond` at `w = b`**, every call. -/
theorem f6_hsecond (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent) (m : Nat) :
    vPm * vEm * 2 ^ (vQ + 1) < 2 ^ C10PartsSchedule.entryWidthSchedule sources k r n := by
  have hd := den_le_at sources p den hden k r scratch n x bits hp ph ci L m
  rw [← f6_den sources p den hden k r scratch n x bits hp ph ci L m] at hd
  have hb := SourcePhase.phase_hdenwidth2 sources p k S hn
  rw [← hr] at hb
  have h2 := SourcePhase.two_den_lt hd hb
  have he : vPm * vEm * 2 ^ (vQ + 1) = 2 * (vPm * vEm * 2 ^ vQ) := by rw [pow_succ]; ring
  rw [he]
  exact h2

/-- **`hfirst` at `w = b`**, every call. -/
theorem f6_hfirst (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent) (m : Nat) :
    vPm * 2 ^ (natBitLength vEm) < 2 ^ C10PartsSchedule.entryWidthSchedule sources k r n := by
  have hs := f6_hsecond sources p den hden k r scratch n x bits hp ph ci L S hn hr m
  have hE : 1 ≤ vEm := seedCount_pos _ _
  have hlog : 2 ^ Nat.log 2 vEm ≤ vEm := Nat.pow_log_le_self 2 (by omega)
  have hq : 1 ≤ 2 ^ vQ := Nat.one_le_two_pow
  have h1 : 2 ^ (natBitLength vEm) ≤ 2 * vEm := by
    unfold natBitLength
    rw [pow_succ]
    omega
  have h2 : vPm * 2 ^ (natBitLength vEm) ≤ vPm * vEm * 2 ^ (vQ + 1) := by
    calc vPm * 2 ^ (natBitLength vEm) ≤ vPm * (2 * vEm) := Nat.mul_le_mul_left _ h1
      _ = vPm * vEm * 2 := by ring
      _ ≤ vPm * vEm * 2 ^ (vQ + 1) := Nat.mul_le_mul_left _ (by rw [pow_succ]; omega)
  exact lt_of_le_of_lt h2 hs

/-- **`hpw` at `w = b`**, every call. -/
theorem f6_hpw (S : CloseoutFinalC10ModeNativeSchedule.Selection sources p k) (hn : S.onset ≤ n) (hr : r = S.exponent) (m : Nat) :
    (CloseoutRowsCountBinary.bits vPm).length ≤ C10PartsSchedule.entryWidthSchedule sources k r n := by
  have hd := den_le_at sources p den hden k r scratch n x bits hp ph ci L m
  rw [← f6_den sources p den hden k r scratch n x bits hp ph ci L m] at hd
  have hb := SourcePhase.phase_hdenwidth2 sources p k S hn
  rw [← hr] at hb
  have hE : 1 ≤ vEm := seedCount_pos _ _
  have hq : 1 ≤ 2 ^ vQ := Nat.one_le_two_pow
  have hP : vPm ≤ vPm * vEm * 2 ^ vQ := by
    calc vPm = vPm * 1 * 1 := by ring
      _ ≤ vPm * vEm * 2 ^ vQ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hE) hq
  have hP2 : vPm < 2 ^ (nativeDenBits sources k p n + 1) :=
    lt_of_le_of_lt (hP.trans hd) (Nat.pow_lt_pow_right (by decide) (by omega))
  unfold CloseoutRowsCountBinary.bits
  split_ifs with h0
  · exact Nat.zero_le _
  · rw [SignedSortKey.binary_length]
    unfold natBitLength
    have hl : Nat.log 2 vPm < nativeDenBits sources k p n + 1 := Nat.log_lt_of_lt_pow (by omega) hP2
    omega

end clause

end
end NearCubicWires.SourceSteps
end
