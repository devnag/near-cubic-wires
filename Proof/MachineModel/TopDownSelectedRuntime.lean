import Proof.MachineModel.TopDownSelectedAssembly
import Proof.MachineModel.TopDownWorkspaceSelectedBudget
import Proof.CaseAnalysis.FinalLedgerAssembly

/-! Runtime of the actual selected guarded worker. Paper A.8:2249–2307
and C.10:4280–4330 keep polynomial-in-N admission separate from the single
residual table factor. The continuation's own fuel bound remains explicit.
Its polynomial degree must be fixed before choosing the hierarchy index. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.SelectedRuntime
open RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
noncomputable section

def sigma (sources : EightSources) : Nat := 6+(fixedProjection sources).degrees.proofLog

def width {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (n : Nat) : Nat :=
  (outer sources C.k C.clock).result.pcp.nativeWidth n

def logarithm {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (n : Nat) : Nat := Nat.log 2 (width C n)+1

/-- A fixed column coefficient enlarges only the finite onset. It does not
feed back into kappa; the supplier's q-exponent must be fixed before kappa. -/
theorem column_absorb (q tableCoefficient tableDegree sigma : Nat)
    (hq : max (C10LogFitFull.fullOnset (sigma+tableDegree+2)) tableCoefficient ≤ q) :
    tableCoefficient*(2^(q-(sigma+tableDegree+2)*(Nat.log 2 q+1))*
      (q+1)^tableDegree) ≤ 2^(q-sigma*(Nat.log 2 q+1)) := by
  have hw := (Nat.le_max_left _ _).trans hq
  have hc : tableCoefficient ≤ 2^(2*(Nat.log 2 q+1)) := by
    calc tableCoefficient ≤ q := (Nat.le_max_right _ _).trans hq
      _ ≤ 2^(Nat.log 2 q+1) := (Nat.le_succ _).trans (C10LogFitFull.hlog_of_onset _ _ hw)
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  exact C10SupplierFuel.hot_absorb
    (C10LogFitFull.hlog_of_onset _ _ hw) (C10LogFitFull.hfit_full _ _ hw) le_rfl hc

end
end NearCubicWires.P1TopDown.SelectedRuntime
