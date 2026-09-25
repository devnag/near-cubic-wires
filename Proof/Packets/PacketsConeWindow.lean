import Proof.Packets.GradedWindowFromRoot
import Proof.Packets.PacketsMaskCoord

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.ConeWindow
open NearCubicWires NearCubicWires.CanonicalFourfoldRowProgram
open PCJ9eff70d512234a4c_Fixed.Materializer

/-- Iterated round-up halving is ceiling division by a power of two. -/
theorem halve_iterate (q n : ℕ) : GradedHalveRound.halve^[q] n = (n + 2 ^ q - 1) / 2 ^ q := by
  induction q generalizing n with
  | zero => simp
  | succ q ih =>
    rw [Function.iterate_succ_apply, ih]
    unfold GradedHalveRound.halve
    have hq : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    have hsplit : n + 2 * 2 ^ q - 1 = (n + 1) + 2 * (2 ^ q - 1) := by omega
    have hdiv : (n + 2 * 2 ^ q - 1) / 2 = (n + 1) / 2 + (2 ^ q - 1) := by
      rw [hsplit, Nat.add_mul_div_left _ _ (by norm_num)]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ q) 2, ← Nat.div_div_eq_div_mul, hdiv]
    congr 1
    omega

def root (B : ℕ) : ℕ := natCeilSqrt (64 ^ 2 * B)

/-- **The two windows agree at every level.** -/
theorem window_eq (B : ℕ) {depth : ℕ} (l : Fin depth) :
    GradedWindow.window (root B) l.val = executableGradedWindow B l := by
  unfold GradedWindow.window executableGradedWindow root
  rw [halve_iterate, Nat.ceilDiv_eq_add_pred_div]

end NearCubicWires.PacketsConstruction.ConeWindow
