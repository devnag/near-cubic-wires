import Proof.SourceAssembly.SourceSkelParams

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.Params
noncomputable section

/-- A coefficient/exponent below the master's is below the master. -/
theorem poly_mono (c j A E q : ℕ) (hc : c ≤ A) (hj : j ≤ E) : c * (q+1)^j ≤ A * (q+1)^E :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (Nat.succ_pos q) hj)

/-- `a·Y + b ≤ Z·Y` from `a + b ≤ Z` and `1 ≤ Y`. -/
theorem lin_le (a b Y Z : ℕ) (hY : 1 ≤ Y) (h : a + b ≤ Z) : a * Y + b ≤ Z * Y := by
  have h1 : b ≤ b * Y := Nat.le_mul_of_pos_right _ hY
  have h2 : (a + b) * Y ≤ Z * Y := Nat.mul_le_mul_right _ h
  have e : (a + b) * Y = a * Y + b * Y := by ring
  omega

theorem initWin_eventually (eR eV L cVc cS cR CL DL target : ℕ) (h2 : 2 ≤ eR) (hVR : eV + 2 ≤ eR) :
    ∃ q0, ∀ q, q0 ≤ q → InitWin eR eV L cVc cS cR CL DL target q := by
  obtain ⟨q1, h1⟩ := Dimension.prefix_le_Rc eR eV L 1 cVc le_rfl h2 (by omega)
  set A := 2^20 + CL + (RepairOrdinary.frame (natWord L)).length + (RepairOrdinary.frame (natWord target)).length + 82472 with hA
  obtain ⟨q2, hq2⟩ := SourceBudget.poly_le_Rc A (DL + 2) L
  set M := cS * cVc + cR * cVc + 5 * cVc + cS + cR + 5 with hM
  refine ⟨max q1 (max q2 M), fun q hq => ?_⟩
  have hq1 : q1 ≤ q := le_of_max_le_left hq
  have hq2' : q2 ≤ q := le_of_max_le_left (le_of_max_le_right hq)
  have hqM : M ≤ q := le_of_max_le_right (le_of_max_le_right hq)
  have hP := hq2 q hq2' 1 eR le_rfl
  set T := 2^(q - normalizedLiveCount q L) with hT
  set X := (q+1)^eV with hX
  have hT1 : 1 ≤ T := Nat.one_le_two_pow
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (Nat.succ_pos q)
  have hY1 : 1 ≤ X * T := Nat.mul_le_mul hX1 hT1
  have hE : (q+1)^eR = (q+1)^2 * X * ((q+1)^(eR - eV - 2)) := by
    rw [hX, ← pow_add, ← pow_add]
    congr 1
    omega
  have hZ1 : 1 ≤ (q+1)^(eR - eV - 2) := Nat.one_le_pow _ _ (Nat.succ_pos q)
  -- the reserve dominates `(q+1)^2·X·T`
  have hRc : (q+1)^2 * (X * T) ≤ Once.Rc eR L 1 q := by
    show (q+1)^2 * (X * T) ≤ 1 * ((q+1)^eR * T)
    rw [hE, one_mul]
    have := Nat.mul_le_mul_left ((q+1)^2 * X * T) hZ1
    calc (q+1)^2 * (X * T) = (q+1)^2 * X * T * 1 := by ring
      _ ≤ (q+1)^2 * X * T * (q+1)^(eR - eV - 2) := this
      _ = (q+1)^2 * X * (q+1)^(eR - eV - 2) * T := by ring
  have hq1M : M ≤ (q+1)^2 := by
    have : q + 1 ≤ (q+1)^2 := Nat.le_self_pow (by omega) _
    omega
  -- a table window `a·(X·T) + b ≤ Rc` whenever `a + b ≤ M`
  have tab : ∀ a b : ℕ, a + b ≤ M → a * (X * T) + b ≤ Once.Rc eR L 1 q := fun a b hab =>
    (lin_le a b (X * T) ((q+1)^2) hY1 (hab.trans hq1M)).trans hRc
  have hV : RuntimeShape.tableClass L eV q = X * T := rfl
  -- every polynomial window below `A·(q+1)^(DL+2)`
  have pol : ∀ c j : ℕ, c ≤ A → j ≤ DL + 2 → c * (q+1)^j ≤ Once.Rc eR L 1 q := fun c j hc hj =>
    (poly_mono c j A (DL + 2) q hc hj).trans hP
  have hK : normalizedLiveCount q L ≤ q := normalizedLiveCount_le q L
  have hA20 : 2^20 ≤ A := by rw [hA]; omega
  have e1 : ∀ c : ℕ, c * (q+1)^1 = c * (q+1) := fun c => by rw [pow_one]
  have e0 : ∀ c : ℕ, c * (q+1)^0 = c := fun c => by rw [pow_zero, mul_one]
  refine ⟨h1 q hq1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- V ≤ Rc
    rw [hV]; have := tab cVc 0 (by omega); omega
  · -- VLog ≤ Rc
    show cVc * X * (2 * T + 3) + 2 ≤ Once.Rc eR L 1 q
    have h := tab (5 * cVc) 2 (by omega)
    have e : cVc * X * (2 * T + 3) + 2 ≤ 5 * cVc * (X * T) + 2 := by
      have : cVc * X * (2 * T + 3) = 2 * (cVc * (X * T)) + 3 * (cVc * X) := by ring
      have hh : cVc * X ≤ cVc * (X * T) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hT1)
      have e5 : 5 * cVc * (X * T) = 5 * (cVc * (X * T)) := by ring
      omega
    exact e.trans h
  · -- 2 ≤ Rc
    have := pol 2 0 (by omega) (by omega); rw [e0] at this; exact this
  · -- U0 ≤ Rc
    have := pol 16 1 (by omega) (by omega); rw [e1] at this
    show 3 * (Kc L q + 2 + 1) + ((q - Kc L q + 1) / 2 + (q - Kc L q + 1) / 2) ≤ _
    have hKc : Kc L q ≤ q := hK
    have : (q - Kc L q + 1) / 2 + (q - Kc L q + 1) / 2 ≤ q + 1 := by omega
    omega
  · -- workspace master
    rw [hV]
    have h := tab (cS * cVc) (cS + 2) (by omega)
    have e : cS * (X * T * cVc + 1) + 2 = cS * cVc * (X * T) + (cS + 2) := by ring
    rw [show cVc * (X * T) = X * T * cVc by ring, e]; exact h
  · -- rewind master
    rw [hV]
    have h := tab (cR * cVc) (cR + 2) (by omega)
    have e : cR * (X * T * cVc + 1) + 2 = cR * cVc * (X * T) + (cR + 2) := by ring
    rw [show cVc * (X * T) = X * T * cVc by ring, e]; exact h
  · -- buffer
    rw [hV]
    have h := tab cVc 3 (by omega)
    omega
  · -- the parity capacity
    show 256 * (q+1)^2 ≤ _
    exact pol 256 2 (by omega) (by omega)
  · -- q ≤ Rc
    have := pol 1 1 (by omega) (by omega); rw [e1] at this; omega
  · -- the framed live scale
    have := pol (RepairOrdinary.frame (natWord L)).length 0 (by omega) (by omega); rw [e0] at this; omega
  · -- the framed target
    have := pol (RepairOrdinary.frame (natWord target)).length 0 (by omega) (by omega); rw [e0] at this; omega
  · -- 5 ≤ Rc
    have := pol 5 0 (by omega) (by omega); rw [e0] at this; exact this
  · -- `Ld + 2 ≤ Rc`
    have h := pol (CL + 2) DL (by omega) (by omega)
    have h1' : 1 ≤ (q+1)^DL := Nat.one_le_pow _ _ (Nat.succ_pos q)
    have e : (CL + 2) * (q+1)^DL = CL * (q+1)^DL + 2 * (q+1)^DL := by ring
    omega
  · -- 82472 ≤ Rc
    have := pol 82472 0 (by omega) (by omega); rw [e0] at this; exact this
  · -- `2q+1 ≤ Rc`
    have := pol 2 1 (by omega) (by omega); rw [e1] at this; omega
  · -- `2·Ms + 5 ≤ Rc`
    have := pol 9 1 (by omega) (by omega); rw [e1] at this
    show 2 * (2 * (normalizedLiveCount q L + 1)) + 5 ≤ _
    omega
  · -- `Mb ≤ Rc`
    show q / InitSlopes.dv L q * InitPost.Ms L q ≤ _
    have hd : q / InitSlopes.dv L q ≤ q := Nat.div_le_self _ _
    have hMs : InitPost.Ms L q ≤ 2 * (q+1) := by show 2 * (normalizedLiveCount q L + 1) ≤ _; omega
    have hm : q / InitSlopes.dv L q * InitPost.Ms L q ≤ (q+1) * (2 * (q+1)) := Nat.mul_le_mul (by omega) hMs
    have h := pol 2 2 (by omega) (by omega)
    have e : (q+1) * (2 * (q+1)) = 2 * (q+1)^2 := by ring
    omega

end
end NearCubicWires.SourceSkeleton.Params
end

