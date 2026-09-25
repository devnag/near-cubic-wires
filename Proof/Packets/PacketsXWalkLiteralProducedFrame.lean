import Proof.Packets.PacketsXWalkLiteralProducedLayout
import Proof.Packets.PacketsXWalkLiteralProducedMasters

/-! Original scalar, mask and sample input words remain resident at the join. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralProduced
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer Completion
noncomputable section

theorem cold_lt (i : Fin 333) : (coldSlots i).val<428 := by
  unfold coldSlots
  split_ifs with h
  · have hp:=(paletteSlots ⟨i.val-15,by omega⟩).isLt
    dsimp
    omega
  · have hb:=i.isLt
    dsimp
    omega

end
end Theorem25Completion.WalkLiteralProduced
