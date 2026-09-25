import Proof.Packets.WindowSeed
import Proof.Packets.CycleWindowScalars

/-! The actual cold/reentry metadata initializer is paid from the same
physically generated reserve. Its width master is the actual C+9 counter. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace Theorem25Completion.CycleWindowSeedCost
open PCJ9eff70d512234a4c_Fixed.Materializer

theorem budget_formula (R v u M W : Nat) :
    WindowSeed.budget R v u M W =
      16*R+8*u+14*v+4*M+(M-1)*(4*v+5)+8*W^2+14*W+117 := by
  simp only [WindowSeed.budget,WindowSeed.bodyBudget,ScalarFromCounter.budget,
    WindowWidthDriver.budget,WindowWidthDriver.loopBudget]
  ring

theorem budget_reserve (C w v M W : Nat) (hw : 1≤w) (hv : v≤C+1)
    (hM : M≤C) (hW : W≤64*(C+2)) :
    WindowSeed.budget (CycleCommonReserve.reserve C w) v (CycleWindowScalars.width C) M W
      ≤17*CycleCommonReserve.reserve C w := by
  have hprod := Nat.mul_le_mul (by omega : M-1≤C) (by omega : 4*v+5≤4*C+9)
  have hW' : W≤128*(C+1):=by omega
  have hW2:=Nat.pow_le_pow_left hW' 2
  have small : 8*(C+9)+14*v+4*M+(M-1)*(4*v+5)+8*W^2+14*W+117
      ≤262144*(C+1)^2 := by
    nlinarith only [hprod,hW2,hW',hv,hM,Nat.zero_le C,Nat.zero_le (C^2)]
  have hp : (C+1)^2≤(C+1)^4:=Nat.pow_le_pow_right (by omega) (by decide)
  have he : 256≤2^(8*w):=(by decide : 256≤2^8).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have reserve : 262144*(C+1)^2≤CycleCommonReserve.reserve C w := by
    unfold CycleCommonReserve.reserve
    nlinarith only [Nat.mul_le_mul hp he,Nat.zero_le ((C+1)^2)]
  rw [budget_formula]
  unfold CycleWindowScalars.width
  omega

end Theorem25Completion.CycleWindowSeedCost
