import Proof.Packets.PacketsXVectorAccumulatorNat
import Proof.Packets.VectorChildTransaction

/-! Literal natural-code semantics of the actual vector-child transaction.
The order is child times delta, then accumulated sum plus that product. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildTransaction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport

theorem term_masks {C : Nat} (P Q : Ring.Poly (Fin C)) :
    VectorChildArithmetic.term (P.map PhysicalPacketMasks.mask) (Q.map PhysicalPacketMasks.mask)=
      (Ring.mul P Q).map PhysicalPacketMasks.mask := by
  simp only [VectorChildArithmetic.term,NormalizedMultiply.unions_masks,
    NormalizerOrder.normalized_masks,NormalizerOrder.mul_raw]

theorem term_nat (C : Nat) (P Q : Ring.Poly Nat) (hP : Fits C P) (hQ : Fits C Q) :
    VectorChildArithmetic.term (P.map (maskNat C)) (Q.map (maskNat C))=
      (Ring.mul P Q).map (maskNat C) := by
  have h:=term_masks (lift C P) (lift C Q)
  simpa only [masks_down,mul_down,lift_down C P hP,lift_down C Q hQ] using h

theorem term_fits (C : Nat) (P Q : Ring.Poly Nat) (hP : Fits C P) (hQ : Fits C Q) : Fits C (Ring.mul P Q) := by
  have hd : Fits C (down (Ring.mul (lift C P) (lift C Q))) := by
    intro m hm j hj
    obtain ⟨n,_,rfl⟩:=List.mem_map.mp hm
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hj
    exact i.isLt
  simpa only [mul_down,lift_down C P hP,lift_down C Q hQ] using hd

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorChildTransaction
