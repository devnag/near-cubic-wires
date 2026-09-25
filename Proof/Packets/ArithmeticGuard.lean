import Proof.Packets.ArithmeticCore

/-! Close the actual cold-engine capacity and fuel guards at the physically
constructed common reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open Theorem25Completion

theorem reserve_large (C w : Nat) :
    65536*(C+1) ≤ CycleCommonReserve.reserve C w := by
  have hp : C+1 ≤ (C+1)^4:=Nat.le_self_pow (by decide) _
  have he : 1 ≤ 2^(8*w):=Nat.one_le_two_pow
  have hm:=Nat.mul_le_mul hp he
  unfold CycleCommonReserve.reserve
  nlinarith only [hm]

theorem budget_reserve (C w : Nat) :
    budget C (CycleCommonReserve.reserve C w) ≤ 11*CycleCommonReserve.reserve C w := by
  have h:=reserve_large C w
  unfold budget
  omega

theorem run_common (C w : Nat) :
    Step machine (11*CycleCommonReserve.reserve C w) (fun _=>0)
      (input C (CycleCommonReserve.reserve C w)) heads
      (output C (CycleCommonReserve.reserve C w)) := by
  have h:=reserve_large C w
  exact (run C (CycleCommonReserve.reserve C w) (by omega)).enlarge (budget_reserve C w)

theorem common_core (C w : Nat) (i : Fin 34) :
    output C (CycleCommonReserve.reserve C w) (i.castAdd 12)=
      ReusableArithmetic.state C (CycleCommonReserve.reserve C w) [] [] i := by
  have h:=reserve_large C w
  exact output_core C (CycleCommonReserve.reserve C w) (by omega) i

end PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
