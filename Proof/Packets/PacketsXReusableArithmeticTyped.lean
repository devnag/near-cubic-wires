import Proof.Packets.PacketsXNormalizedMultiplyTyped
import Proof.Packets.ReusableNormalizedArithmetic

/-! Exact literal ring operations on the reusable physical accumulator bank. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open PhysicalPacketMasks

variable {B : Nat}
def polyState (R : Nat) (P Q : Ring.Poly (Fin B)) := state B R (P.map mask) (Q.map mask)

theorem masks_width (P : Ring.Poly (Fin B)) : ∀ bits∈P.map mask,bits.length=B := by
  intro bits hb
  obtain ⟨m,_,rfl⟩ := List.mem_map.mp hb
  exact mask_length m

theorem typed_mul (R : Nat) (P Q : Ring.Poly (Fin B))
    (ha : ∀ i,(data B (P.map mask) (Q.map mask) i).length≤R)
    (hcap : NormalizedMultiply.budget B (P.map mask) (Q.map mask)+3≤R) :
    Step (machine NormalizedMultiply.machine)
      (budget (NormalizedMultiply.budget B (P.map mask) (Q.map mask)) R)
      heads (polyState R P Q) heads (polyState R P (Ring.mul P Q)) := by
  simpa only [polyState,NormalizedMultiply.unions_masks,NormalizerOrder.normalized_masks,
    NormalizerOrder.mul_raw] using mul_run B R (P.map mask) (Q.map mask)
      (masks_width P) (masks_width Q) ha hcap

theorem typed_add (R : Nat) (P Q : Ring.Poly (Fin B)) (hP : Ring.Normal P) (hQ : Ring.Normal Q)
    (ha : ∀ i,(data B (P.map mask) (Q.map mask) i).length≤R)
    (hcap : NormalizedAddition.budget B (P.map mask) (Q.map mask)+3≤R) :
    Step (machine NormalizedAddition.machine)
      (budget (NormalizedAddition.budget B (P.map mask) (Q.map mask)) R)
      heads (polyState R P Q) heads (polyState R P (Ring.add P Q)) := by
  have he : (P.map mask).reverse++Q.map mask=(P.reverse++Q).map mask := by
    simp only [List.map_append,List.map_reverse]
  simpa only [polyState,he,NormalizerOrder.normalized_masks,NormalizerOrder.add_raw P Q hP hQ]
    using add_run B R (P.map mask) (Q.map mask) (masks_width P) (masks_width Q) ha hcap

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
