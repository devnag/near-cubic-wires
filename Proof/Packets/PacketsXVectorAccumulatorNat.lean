import Proof.Packets.PacketsXVectorAccumulatorTyped
import Proof.Packets.PacketsXNormalizedFiniteTransport

/-! Exact accumulator order on unchanged natural literal codes. Finite masks
provide only a proved physical bound and never renumber the variables. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NormalizedFiniteTransport

theorem nat_masks_width (C : Nat) (P : Ring.Poly Nat) :
    ∀ bits∈P.map (maskNat C),bits.length=C := by
  intro bits hb
  obtain ⟨m,_,rfl⟩:=List.mem_map.mp hb
  simp [maskNat]

theorem answer_nat (C : Nat) (P Q : Ring.Poly Nat)
    (hP : NormalizedFiniteTransport.Fits C P) (hQ : NormalizedFiniteTransport.Fits C Q)
    (nP : Ring.Normal P) (nQ : Ring.Normal Q) :
    answer (P.map (maskNat C)) (Q.map (maskNat C))=(Ring.add P Q).map (maskNat C) := by
  have h:=answer_masks (lift C P) (lift C Q) (normal_lift C P hP nP) (normal_lift C Q hQ nQ)
  simpa only [masks_down,add_down,lift_down C P hP,lift_down C Q hQ] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
