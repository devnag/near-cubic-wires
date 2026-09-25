import Proof.Packets.PacketsXVectorWorkerData
import Proof.Packets.PacketVector

/-! One exact vector-child transaction in the full provider arena. The bank
prefix and suffix are derived from the actual resident vector, so indexed
access requires no supplied packet-selection witness. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem packet_fits (R : Nat) (P : PacketVector.Packet) (h : VectorAccumulator.Fits R P) : PacketVector.Fits R P := by
  exact ⟨h.1,by simpa [CompareMachine.word] using h.2⟩

theorem child_vector_run (B R pi li : Nat) (ps : List PacketVector.Packet) (i : Fin ps.length)
    (delta oldLeft acc : PacketVector.Packet) (next : List Bool)
    (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hps : ∀ P∈ps,VectorAccumulator.Fits R P) (hold : VectorAccumulator.Fits R oldLeft)
    (hd : ∀ bits∈delta,bits.length=B) (hc : ∀ bits∈ps[i.val],bits.length=B)
    (ha : ∀ bits∈acc,bits.length=B)
    (hmd : ∀ j,(ReusableArithmetic.data B ps[i.val] delta j).length≤R)
    (hmc : NormalizedMultiply.budget B ps[i.val] delta+3≤R)
    (had : ∀ j,(ReusableArithmetic.data B acc (VectorChildArithmetic.term ps[i.val] delta) j).length≤R)
    (hac : NormalizedAddition.budget B acc (VectorChildArithmetic.term ps[i.val] delta)+3≤R) :
    Step child (VectorChildTransaction.budget B R i.val delta ps[i.val] acc)
      (H mh) (A B R i.val pi li oldLeft delta acc (PacketVector.bank R ps) next fields extra)
      (H mh) (A B R i.val pi li (VectorAccumulator.answer acc (VectorChildArithmetic.term ps[i.val] delta))
        (VectorChildArithmetic.term ps[i.val] delta) (VectorAccumulator.answer acc (VectorChildArithmetic.term ps[i.val] delta))
        (PacketVector.bank R ps) next fields extra) := by
  have hi:=hps ps[i.val] (List.getElem_mem i.isLt)
  have hpre : (PacketVector.bank R (ps.take i.val)).length=2*i.val*R := by
    rw [PacketVector.bank_length R _ (fun P hP=>packet_fits R P (hps P (List.mem_of_mem_take hP))),List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  have h:=VectorChildTransaction.run B R i.val delta oldLeft ps[i.val] acc
    (PacketVector.bank R (ps.take i.val)) (PacketVector.bank R (ps.drop (i.val+1)))
    hpre hold hi hd hc ha hmd hmc had hac
  have bank:=PacketVector.bank_split R ps i
  unfold PacketVector.payload PacketVector.count at bank
  dsimp only at h
  rw [←bank] at h
  exact dock_child B R i.val pi li oldLeft delta acc _ _ _ (PacketVector.bank R ps) next mh fields extra h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
