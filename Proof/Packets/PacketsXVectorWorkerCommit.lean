import Proof.Packets.PacketsXVectorWorkerChild

/-! Exact indexed next-vector update and paid accumulator reset in the full
provider arena. All other stored vector entries are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem bank_set (R : Nat) (ps : List PacketVector.Packet) (i : Fin ps.length) (P : PacketVector.Packet) :
    PacketVector.bank R (ps.set i.val P)=PacketVector.bank R (ps.take i.val)++
      PacketVector.payload R P++PacketVector.count R P++PacketVector.bank R (ps.drop (i.val+1)) := by
  rw [List.set_eq_take_append_cons_drop,if_pos i.isLt]
  simp only [PacketVector.bank,List.flatMap_append,List.flatMap_cons,PacketVector.entry,List.append_assoc]

theorem commit_vector_run (B R ci li : Nat) (ns : List PacketVector.Packet) (i : Fin ns.length)
    (left right acc : PacketVector.Packet) (previous : List Bool)
    (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hns : ∀ P∈ns,VectorAccumulator.Fits R P) (ha : VectorAccumulator.Fits R acc) :
    Step commit (VectorParentCommit.budget R i.val)
      (H mh) (A B R ci i.val li left right acc previous (PacketVector.bank R ns) fields extra)
      (H mh) (A B R ci i.val li left right [] previous (PacketVector.bank R (ns.set i.val acc)) fields extra) := by
  have hi:=packet_fits R ns[i.val] (hns _ (List.getElem_mem i.isLt))
  have hpre : (PacketVector.bank R (ns.take i.val)).length=2*i.val*R := by
    rw [PacketVector.bank_length R _ (fun P hP=>packet_fits R P (hns P (List.mem_of_mem_take hP))),List.length_take]
    rw [Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  have h:=VectorParentCommit.run B R ci i.val left right acc previous (PacketVector.bank R (ns.take i.val))
    (PacketVector.payload R ns[i.val]) (PacketVector.count R ns[i.val]) (PacketVector.bank R (ns.drop (i.val+1)))
    hpre ha (PacketVector.payload_length hi) (PacketVector.count_length hi)
  rw [←PacketVector.bank_split R ns i] at h
  have hs:=bank_set R ns i acc
  unfold PacketVector.payload PacketVector.count at hs
  rw [←hs] at h
  exact dock_parent B R ci i.val li left right acc [] previous _ _ mh fields extra h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
