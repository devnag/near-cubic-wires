import Proof.Packets.BudgetTableOnset
import Proof.SourceAssembly.SourcePhaseFuel

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RuntimeShape NearCubicWires.Admission
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal

/-- **Lift the polynomial part** from the arity `qn` to any `n` with `qn + 1 ≤ W·(n+1)`. -/
theorem InClasses.lift_n {dP hT hS m L qn n W cP cT cS x : ℕ} (hW : qn + 1 ≤ W*(n+1))
    (hx : InClasses dP hT hS m L qn qn cP cT cS x) : InClasses dP hT hS m L n qn (cP*W^dP) cT cS x := by
  unfold InClasses splitRHS at *
  have h1 : (qn+1)^dP ≤ (W*(n+1))^dP := Nat.pow_le_pow_left hW dP
  have h2 : cP*(qn+1)^dP ≤ cP*W^dP*(n+1)^dP := by
    calc cP*(qn+1)^dP ≤ cP*(W*(n+1))^dP := Nat.mul_le_mul_left _ h1
      _ = cP*W^dP*(n+1)^dP := by rw [mul_pow]; ring
  omega

/-- **The source instance**: a call-level class at the width lifts to the site class at the input length. -/
theorem lift_width (sources : EightSources) (k : ℕ) {dP hT hS m L n cP cT cS x : ℕ}
    (hx : InClasses dP hT hS m L (C10PartsSchedule.widthAt sources k n) (C10PartsSchedule.widthAt sources k n) cP cT cS x) :
    InClasses dP hT hS m L n (C10PartsSchedule.widthAt sources k n)
      (cP*C10PartsSchedule.widthConst sources k^dP) cT cS x := by
  have hw := SourcePhase.widthAt_poly sources k n
  rw [pow_one] at hw
  exact InClasses.lift_n hw hx

end NearCubicWires.SourceBudget

