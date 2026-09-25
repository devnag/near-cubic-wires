import Proof.Packets.CycleNormalizerCost
import Proof.Packets.PacketsXCycleNormalizeTyped

/-! The actual native serializer, its selective reset, and every raw bank
fit a common reserve computed from measured pool width and policy width. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true
namespace Theorem25Completion.CycleBounds
open NearCubicWires NearCubicWires.RepairSource.ProjectionNormalization
open PCJ9eff70d512234a4c_Fixed.Materializer

def commonReserve (B w : Nat) := 65536*(B+1)^4*2^(8*w)

theorem packet_reserve_bound (B w M : Nat) (hM : M≤2^(2*w)) :
    8192*(M+1)^3*(B+1)^3≤commonReserve B w := by
  have hp : 1≤2^(2*w) := Nat.one_le_two_pow
  have hM1 : M+1≤2*2^(2*w) := by omega
  have hb : (B+1)^3≤(B+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have he : 2^(6*w)≤2^(8*w) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _≤8192*(2*2^(2*w))^3*(B+1)^3 := by gcongr
    _=65536*(B+1)^3*2^(6*w) := by rw [mul_pow,←pow_mul];ring_nf
    _≤65536*(B+1)^4*2^(8*w) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) he
    _=_ := rfl

end Theorem25Completion.CycleBounds
