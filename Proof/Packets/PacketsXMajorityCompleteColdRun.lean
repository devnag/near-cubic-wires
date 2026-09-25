import Proof.Packets.PacketsXMajorityCompleteReady

/-! Complete physical cold initializer for majority: lower resident source
heads, generate sample scalars, compute the square reserve, copy masters,
then fill and position all private arithmetic tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Theorem25Completion.CycleBounds
noncomputable section


theorem result_arena (C R n : Nat) (ps : List (Ring.Poly Nat)) (i : Fin 137) :
    result C R n ps (arenaSlots i)=Bootstrap.readyWith (masters C R (n+1) (R^2)) C R (R^2) ps i := by
  exact install_slot arenaSlots arena_injective _ _ i

theorem result_heads (i : Fin 137) : resultHeads (arenaSlots i)=Bootstrap.heads i :=
  dockH_slot arenaSlots arena_injective _ _ i

theorem ready_compatible (C w n : Nat) (ps : List (Ring.Poly Nat)) (hlen : ps.length=n+1)
    (hCodes : 2^(n+1)≤2^w) :
    Bootstrap.Compatible (masters C (commonReserve C w) (n+1) ((commonReserve C w)^2))
      C (commonReserve C w) ps.length ((commonReserve C w)^2) := by
  simpa only [hlen] using actual_compatible C w (n+1) hCodes

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
