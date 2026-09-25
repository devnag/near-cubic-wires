import Proof.CaseAnalysis.FinalRuntimeBridge
import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalTailCompose

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierFuel

open SelectedRecoveryIntegration SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain (workerBudget)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam (stagedFuel dockedFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose (bodyThreeFuel)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Arithmetic: constants and the single residual factor -/

/-- The exponent arithmetic of A.8:2307, with every product an opaque atom. -/
theorem sub_exp_le {w a b d L : ℕ} (haw : a ≤ w) (h : b + d + 2 * L ≤ a) :
    2 * L + (w - a) + d ≤ w - b := by omega

/-- **Paper A.8:2298-2301 and A.8:2307.**  `m` copies of one residual table factor
`2 ^ (q - kappa * L_q)` times a fixed power `(q+1)^c` of the residual arity still fit
under the single damped factor `2 ^ (q - sigma * L_q)`, provided
`sigma + c + 2 <= kappa` (A.8:2307) and `m <= 2 ^ (2 * L_q)`.
There is exactly ONE residual factor on either side. -/
theorem hot_absorb {w L kappa sigma c m : ℕ}
    (hlog : w + 1 ≤ 2 ^ L) (hfit : kappa * L ≤ w)
    (hslack : sigma + c + 2 ≤ kappa) (hm : m ≤ 2 ^ (2 * L)) :
    m * (2 ^ (w - kappa * L) * (w + 1) ^ c) ≤ 2 ^ (w - sigma * L) := by
  have hpow : (w + 1) ^ c ≤ 2 ^ (c * L) := by
    calc (w + 1) ^ c ≤ (2 ^ L) ^ c := Nat.pow_le_pow_left hlog c
      _ = 2 ^ (L * c) := (pow_mul 2 L c).symm
      _ = 2 ^ (c * L) := by rw [Nat.mul_comm]
  have hmul : sigma * L + c * L + 2 * L ≤ kappa * L := by
    calc sigma * L + c * L + 2 * L = (sigma + c + 2) * L := by ring
      _ ≤ kappa * L := Nat.mul_le_mul hslack (Nat.le_refl L)
  have hexp : 2 * L + (w - kappa * L) + c * L ≤ w - sigma * L :=
    sub_exp_le hfit hmul
  calc m * (2 ^ (w - kappa * L) * (w + 1) ^ c)
      ≤ 2 ^ (2 * L) * (2 ^ (w - kappa * L) * 2 ^ (c * L)) :=
        Nat.mul_le_mul hm (Nat.mul_le_mul (Nat.le_refl _) hpow)
    _ = 2 ^ (2 * L + (w - kappa * L) + c * L) := by
        rw [pow_add, pow_add, mul_assoc]
    _ ≤ 2 ^ (w - sigma * L) := Nat.pow_le_pow_right (by norm_num) hexp

/-! ## 2. The supplier stage's fuel (paper A.8:2249-2307) -/

def stageExponent (driverCoeff driverExp tableCoeff tableExp rowExp : ℕ) : ℕ :=
  max (driverCoeff + driverExp) (max (rowExp + tableExp + tableCoeff) 2) + 2

/-! ## 3. The A.8 split of the composed worker budget -/

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierFuel
