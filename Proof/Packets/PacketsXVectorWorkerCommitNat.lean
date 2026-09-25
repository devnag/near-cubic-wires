import Proof.Packets.PacketsXVectorWorkerCommit
import Proof.Packets.PacketsXVectorWorkerChildNat

/-! The actual parent commit writes the exact natural-code polynomial entry. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

theorem commit_vector_nat (C R ci li : Nat) (ns : List (Ring.Poly Nat)) (i : Fin ns.length)
    (left right : PacketVector.Packet) (acc : Ring.Poly Nat) (previous : List Bool)
    (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hns : ∀P∈ns,VectorAccumulator.Fits R (masks C P)) (ha : VectorAccumulator.Fits R (masks C acc)) :
    Step commit (VectorParentCommit.budget R i.val)
      (H mh) (A C R ci i.val li left right (masks C acc) previous (vectorBank C R ns) fields extra)
      (H mh) (A C R ci i.val li left right [] previous (vectorBank C R (ns.set i.val acc)) fields extra) := by
  let j : Fin (ns.map (masks C)).length:=⟨i.val,by rw [List.length_map];exact i.isLt⟩
  have h:=commit_vector_run C R ci li (ns.map (masks C)) j left right (masks C acc) previous mh fields extra
    (by intro P hP;obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp hP;exact hns Q hQ) ha
  simpa only [vectorBank,List.map_set] using h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
