import Proof.Packets.PacketsXReusableArithmeticTyped
import Proof.Packets.VectorAccumulatorRight

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open PhysicalPacketMasks
variable {B : Nat}

theorem answer_masks (P Q : Ring.Poly (Fin B)) (hP : Ring.Normal P) (hQ : Ring.Normal Q) :
    answer (P.map mask) (Q.map mask)=(Ring.add P Q).map mask := by
  have he : (P.map mask).reverse++Q.map mask=(P.reverse++Q).map mask := by
    simp only [List.map_append,List.map_reverse]
  simp only [answer,he,NormalizerOrder.normalized_masks,NormalizerOrder.add_raw P Q hP hQ]

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
