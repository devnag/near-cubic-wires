import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.PacketsXNormalizerOperations

/-! The actual Cartesian producer and normalizer compute literal Ring.mul;
the theorem takes only resident operand banks and their runtime counts. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary
open PhysicalPacketMasks

variable {B : Nat}

theorem union_mask (m n : List (Fin B)) :
    MaskProduct.values ((mask m).zip (mask n))=mask (m++n) := by
  have hm : mask m=PhysicalSupportUnion.supportMask m.toFinset := by
    simp [mask,PhysicalSupportUnion.supportMask]
  have hn : mask n=PhysicalSupportUnion.supportMask n.toFinset := by
    simp [mask,PhysicalSupportUnion.supportMask]
  rw [hm,hn,MaskProduct.support_union]
  simp [mask,PhysicalSupportUnion.supportMask]

theorem unions_masks (P Q : Ring.Poly (Fin B)) :
    MaskProduct.unions (P.map mask) (Q.map mask)=
      (P.flatMap (fun m=>Q.map (fun n=>m++n))).map mask := by
  simp only [MaskProduct.unions,List.flatMap_map,List.map_flatMap,List.map_map]
  apply List.flatMap_congr
  intro m _
  apply List.map_congr_left
  intro n _
  exact union_mask m n

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizedMultiply
