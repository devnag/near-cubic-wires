import Proof.Packets.BudgetSiteAssembly

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
open NearCubicWires.SourceSkeleton NearCubicWires.RuntimeShape NearCubicWires.Admission
noncomputable section

/-- A `c`-cost plus a `d`-cost is a `(c ⊔ d)`-cost (exponents raised, coefficients summed once). -/
theorem CostCls.In.join_add {c d : CostCls} {m L n qn x z : ℕ} (hx : c.In m L n qn x) (hz : d.In m L n qn z) :
    (c.join d).In m L n qn (x + z) := by
  have h1 : InClasses (c.join d).dP (c.join d).hT (c.join d).hS m L n qn c.cP c.cT c.cS x :=
    InClasses.raise (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) hx
  have h2 : InClasses (c.join d).dP (c.join d).hT (c.join d).hS m L n qn d.cP d.cT d.cS z :=
    InClasses.raise (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) hz
  exact h1.add h2

theorem init_in {icost cT hI x cP dP m L n qn : ℕ} (hle : icost ≤ cT * tableClass L hI qn + x) (hx : x ≤ cP * (n+1)^dP) :
    (⟨dP, hI, 0, cP, cT, 0⟩ : CostCls).In m L n qn icost := by
  show InClasses dP hI 0 m L n qn cP cT 0 icost
  have h1 : InClasses dP hI 0 m L n qn 0 cT 0 (cT * tableClass L hI qn) := InClasses.table le_rfl
  have h2 : InClasses dP hI 0 m L n qn cP 0 0 x := InClasses.poly hx le_rfl
  have h := h1.add h2
  exact InClasses.mono hle (h.coeff_mono (by omega) (by omega) (by omega))

section site

end site

/-! ## Per call: S's `hcost0` and both window premises, EXACTLY -/

section seam

end seam

section windows

end windows

end
end NearCubicWires.SourceBudget
end

