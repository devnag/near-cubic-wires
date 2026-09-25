import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXReusableArithmeticTyped
import Proof.Packets.ReusableNormalizedArithmeticLeft

/-! Reusable arithmetic on the unchanged natural literal codes. The physical
finite alphabet is only a checked bound; no renumbering is performed. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport

def natState (C R : Nat) (P Q : Ring.Poly Nat) := state C R (P.map (maskNat C)) (Q.map (maskNat C))

variable (C R : Nat) (P Q : Ring.Poly Nat) (hP : Fits C P) (hQ : Fits C Q)
variable (ha : ∀ i,(data C (P.map (maskNat C)) (Q.map (maskNat C)) i).length≤R)

include hP hQ ha

theorem nat_mul (hcap : NormalizedMultiply.budget C (P.map (maskNat C)) (Q.map (maskNat C))+3≤R) :
    Step (machine NormalizedMultiply.machine)
      (budget (NormalizedMultiply.budget C (P.map (maskNat C)) (Q.map (maskNat C))) R)
      heads (natState C R P Q) heads (natState C R P (Ring.mul P Q)) := by
  have fits : ∀ i,(data C ((lift C P).map PhysicalPacketMasks.mask)
      ((lift C Q).map PhysicalPacketMasks.mask) i).length≤R := by
    simpa only [masks_lift C P hP,masks_lift C Q hQ] using ha
  have cap : NormalizedMultiply.budget C ((lift C P).map PhysicalPacketMasks.mask)
      ((lift C Q).map PhysicalPacketMasks.mask)+3≤R := by
    simpa only [masks_lift C P hP,masks_lift C Q hQ] using hcap
  simpa only [polyState,natState,masks_down,mul_down,lift_down C P hP,lift_down C Q hQ]
    using typed_mul R (lift C P) (lift C Q) fits cap

theorem nat_add (normalP : Ring.Normal P) (normalQ : Ring.Normal Q)
    (hcap : NormalizedAddition.budget C (P.map (maskNat C)) (Q.map (maskNat C))+3≤R) :
    Step (machine NormalizedAddition.machine)
      (budget (NormalizedAddition.budget C (P.map (maskNat C)) (Q.map (maskNat C))) R)
      heads (natState C R P Q) heads (natState C R P (Ring.add P Q)) := by
  have fits : ∀ i,(data C ((lift C P).map PhysicalPacketMasks.mask)
      ((lift C Q).map PhysicalPacketMasks.mask) i).length≤R := by
    simpa only [masks_lift C P hP,masks_lift C Q hQ] using ha
  have cap : NormalizedAddition.budget C ((lift C P).map PhysicalPacketMasks.mask)
      ((lift C Q).map PhysicalPacketMasks.mask)+3≤R := by
    simpa only [masks_lift C P hP,masks_lift C Q hQ] using hcap
  simpa only [polyState,natState,masks_down,add_down,lift_down C P hP,lift_down C Q hQ]
    using typed_add R (lift C P) (lift C Q) (normal_lift C P hP normalP)
      (normal_lift C Q hQ normalQ) fits cap

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
