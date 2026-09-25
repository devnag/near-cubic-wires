import Proof.Packets.PacketsXVectorWorkerChild
import Proof.Packets.PacketsXVectorChildTransactionNat

/-! Literal Ring semantics of the resident-vector transaction in the shared
provider arena. All list ordering and natural literal codes are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport

abbrev masks (C : Nat) (P : Ring.Poly Nat) := P.map (maskNat C)
def vectorBank (C R : Nat) (ps : List (Ring.Poly Nat)) := PacketVector.bank R (ps.map (masks C))

theorem child_vector_nat (C R pi li : Nat) (ps : List (Ring.Poly Nat)) (i : Fin ps.length)
    (delta acc : Ring.Poly Nat) (oldLeft : PacketVector.Packet) (next : List Bool)
    (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hps : ∀ P∈ps,VectorAccumulator.Fits R (masks C P)) (hold : VectorAccumulator.Fits R oldLeft)
    (hd : Fits C delta) (hc : Fits C ps[i.val]) (ha : Fits C acc) (na : Ring.Normal acc)
    (hmd : ∀ j,(ReusableArithmetic.data C (masks C ps[i.val]) (masks C delta) j).length≤R)
    (hmc : NormalizedMultiply.budget C (masks C ps[i.val]) (masks C delta)+3≤R)
    (had : ∀ j,(ReusableArithmetic.data C (masks C acc) (masks C (Ring.mul ps[i.val] delta)) j).length≤R)
    (hac : NormalizedAddition.budget C (masks C acc) (masks C (Ring.mul ps[i.val] delta))+3≤R) :
    Step child (VectorChildTransaction.budget C R i.val (masks C delta) (masks C ps[i.val]) (masks C acc))
      (H mh) (A C R i.val pi li oldLeft (masks C delta) (masks C acc) (vectorBank C R ps) next fields extra)
      (H mh) (A C R i.val pi li (masks C (Ring.add acc (Ring.mul ps[i.val] delta)))
        (masks C (Ring.mul ps[i.val] delta)) (masks C (Ring.add acc (Ring.mul ps[i.val] delta)))
        (vectorBank C R ps) next fields extra) := by
  let j : Fin (ps.map (masks C)).length:=⟨i.val,by rw [List.length_map];exact i.isLt⟩
  have hj : (ps.map (masks C))[j.val]=masks C ps[i.val] := List.getElem_map (masks C)
  have ht:=VectorChildTransaction.term_nat C ps[i.val] delta hc hd
  have hm:=VectorChildTransaction.term_fits C ps[i.val] delta hc hd
  have hs:=VectorAccumulator.answer_nat C acc (Ring.mul ps[i.val] delta) ha hm na (Ring.normal_mul _ _)
  have he : VectorChildArithmetic.term (ps.map (masks C))[j.val] (masks C delta)=masks C (Ring.mul ps[i.val] delta) := by
    rw [hj];exact ht
  have h:=child_vector_run C R pi li (ps.map (masks C)) j (masks C delta) oldLeft (masks C acc) next mh fields extra
    (by intro P hP;obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp hP;exact hps Q hQ) hold
    (VectorAccumulator.nat_masks_width C delta)
    (by rw [hj];exact VectorAccumulator.nat_masks_width C ps[i.val])
    (VectorAccumulator.nat_masks_width C acc)
    (by simpa only [hj] using hmd) (by simpa only [hj] using hmc)
    (by simpa only [he] using had) (by simpa only [he] using hac)
  simpa only [hj,ht,hs,vectorBank] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
