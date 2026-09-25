import Proof.Packets.PacketsXCycleFlatCleanup

/-! The reusable final-packet adapter emits the exact already-normal
compiler polynomial, with no second normalization or order change. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
namespace Theorem25Completion.CycleFlatSerialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed
noncomputable section
variable {B : Nat}

theorem word_masks (P : Ring.Poly (Fin B)) (hP : ∀ m∈P,m.Pairwise (·<·)) :
    word (P.map PhysicalPacketMasks.mask)=ExtIncidence.stream (P.map (fun m=>m.map Fin.val)) := by
  unfold word
  rw [List.map_map]
  apply congrArg ExtIncidence.stream
  apply List.map_congr_left
  intro m hm
  exact PhysicalMaskIndices.selectedIndices_mask m (hP m hm)

end
end Theorem25Completion.CycleFlatSerialize
