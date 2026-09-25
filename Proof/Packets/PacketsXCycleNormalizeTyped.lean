import Proof.Packets.CycleNormalizeEntry
import Proof.Packets.CycleSerializerBoot
import Proof.Packets.NormalizerCold
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Packets.PacketsXPhysicalPolynomialSerialize

/-! Exact compiler semantics for the executed normalization-and-serialization
machine. Its emitted bytes use Ring.norm's literal monomial order. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace Theorem25Completion.CycleNormalize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section
variable {B : Nat}

theorem masks_width (P : Ring.Poly (Fin B)) :
    ∀ bits∈P.map PhysicalPacketMasks.mask,bits.length=B := by
  intro bits hb
  obtain ⟨m,_,rfl⟩ := List.mem_map.mp hb
  exact PhysicalPacketMasks.mask_length m

end
end Theorem25Completion.CycleNormalize
