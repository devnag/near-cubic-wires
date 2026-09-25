import Proof.SourceAssembly.SourceSkelFillV5

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
open NearCubicWires.Admission
namespace NearCubicWires.SourceSkeleton.WinW
open NearCubicWires.SourceSkeleton.ClassR NearCubicWires.SourceSkeleton.Params NearCubicWires.SourceSkeleton.ClassV4
open NearCubicWires.SourceSkeleton.ParamsV4
noncomputable section

section win
variable (selector : CyclicChoice.Laws) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)
  (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2) (p : Parameters sources gamma)

/-- **The master window at v4/v5.** -/
theorem master_windowW (q : ℕ) (hq : qOnW selector mask packets rows sources gamma hg hh p ≤ q) (C hR : ℕ) (hC : 1 ≤ C) :
    aMW selector mask packets rows sources gamma hg hh p * (q+1)^eMW selector mask packets rows sources gamma hg hh p ≤
      C * RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) hR q := by
  have h4 : Classical.choose (SourceBudget.poly_le_Rc (aMW selector mask packets rows sources gamma hg hh p)
      (eMW selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p)) ≤ q := by
    refine le_trans ?_ hq
    unfold qOnW
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  exact Classical.choose_spec (SourceBudget.poly_le_Rc (aMW selector mask packets rows sources gamma hg hh p)
    (eMW selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p)) q h4 C hR hC

theorem ext_windowsW (q : ℕ) (hq : qOnW selector mask packets rows sources gamma hg hh p ≤ q) :
    2 * normalizedLiveCount q (LW selector mask packets rows sources gamma hg hh p) + 4 ≤
        Once.Rc (hRx4 selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p) 1 q ∧
      1 ≤ Once.Rc (hRx4 selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p) 1 q ∧
      ∀ b, b ≤ (C10PartsSchedule.thresholdFloor sources + 1) * (q+1)^(SourceSteps.rBsel sources p) →
        b + 2 ≤ Once.Rc (hRx4 selector mask packets rows sources gamma hg hh p) (LW selector mask packets rows sources gamma hg hh p) 1 q := by
  have hm := master_windowW selector mask packets rows sources gamma hg hh p q hq 1
    (hRx4 selector mask packets rows sources gamma hg hh p) le_rfl
  have ha : 2^20 + C10PartsSchedule.thresholdFloor sources ≤ aMW selector mask packets rows sources gamma hg hh p := by
    unfold aMW; omega
  have he : 8 + SourceSteps.rBsel sources p ≤ eMW selector mask packets rows sources gamma hg hh p := by
    unfold eMW; omega
  have hK : normalizedLiveCount q (LW selector mask packets rows sources gamma hg hh p) ≤ q := min_le_left _ _
  show 2 * normalizedLiveCount q (LW selector mask packets rows sources gamma hg hh p) + 4 ≤
      1 * RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (hRx4 selector mask packets rows sources gamma hg hh p) q ∧
    1 ≤ 1 * RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (hRx4 selector mask packets rows sources gamma hg hh p) q ∧
    ∀ b, b ≤ (C10PartsSchedule.thresholdFloor sources + 1) * (q+1)^(SourceSteps.rBsel sources p) →
      b + 2 ≤ 1 * RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p) (hRx4 selector mask packets rows sources gamma hg hh p) q
  generalize RuntimeShape.tableClass (LW selector mask packets rows sources gamma hg hh p)
    (hRx4 selector mask packets rows sources gamma hg hh p) q = T at hm ⊢
  generalize aMW selector mask packets rows sources gamma hg hh p = A at hm ha
  generalize eMW selector mask packets rows sources gamma hg hh p = E at hm he
  generalize C10PartsSchedule.thresholdFloor sources = tf at ha ⊢
  generalize SourceSteps.rBsel sources p = rB at he ⊢
  generalize normalizedLiveCount q (LW selector mask packets rows sources gamma hg hh p) = K at hK ⊢
  have hq1 : 1 ≤ q + 1 := by omega
  have hpe : (q+1)^1 ≤ (q+1)^E := Nat.pow_le_pow_right hq1 (by omega)
  have hpr : (q+1)^rB ≤ (q+1)^E := Nat.pow_le_pow_right hq1 (by omega)
  have hpos : 1 ≤ (q+1)^rB := Nat.one_le_pow _ _ (by omega)
  generalize (q+1)^E = X at hm hpe hpr
  generalize (q+1)^rB = Y at hpr hpos ⊢
  rw [pow_one] at hpe
  have hA1 : 2^20 * (q+1) ≤ A * X := Nat.mul_le_mul (by omega) hpe
  have hA2 : (tf + 3) * Y ≤ A * X := Nat.mul_le_mul (by omega) hpr
  have h3 : (tf + 1) * Y + 2 ≤ (tf + 3) * Y := by
    have e : (tf + 3) * Y = (tf + 1) * Y + 2 * Y := by ring
    omega
  refine ⟨by omega, by omega, fun b hb => by omega⟩

end win

end
end NearCubicWires.SourceSkeleton.WinW
end

