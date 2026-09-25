import Proof.Packets.PacketsXCycleFlatDock

set_option autoImplicit false
set_option maxHeartbeats 750000
set_option warningAsError true
namespace Theorem25Completion.CycleFlatDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed
noncomputable section

theorem typed_run {B : Nat} (R : Nat) (left : List Bool) (leftN : Nat)
    (P : Ring.Poly (Fin B)) (out : List Bool) (hP : ∀ m∈P,m.Pairwise (·<·))
    (hB : B+3≤R) (hR : P.length*(B^2+8*B+9)+9≤R) :
    Step machine (2*(P.length*(B^2+8*B+9)+8)+2*R+7)
      (heads out) (bank B R left leftN (P.map PhysicalPacketMasks.mask) out)
      (heads (out++ExtIncidence.stream (P.map (fun m=>m.map Fin.val))))
      (bank B R left leftN [] (out++ExtIncidence.stream (P.map (fun m=>m.map Fin.val)))) := by
  have hr : CycleFlatSerialize.budget B (P.map PhysicalPacketMasks.mask)+1≤R := by
    simpa only [CycleFlatSerialize.budget,List.length_map,Nat.add_assoc] using hR
  have h:=run B R left leftN (P.map PhysicalPacketMasks.mask) out hB hr
    (CycleNormalize.masks_width P)
  rw [CycleFlatSerialize.word_masks P hP] at h
  simpa only [CycleFlatSerialize.transactionBudget,CycleFlatSerialize.budget,List.length_map] using h

end
end Theorem25Completion.CycleFlatDock
