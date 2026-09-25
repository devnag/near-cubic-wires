import Proof.Packets.PacketsXVectorWorkerParentBody
import Proof.Packets.PhysicalAppendUpdate

/-! Paid parent-counter zeroing while preserving the child Repeat driver. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem reset_parent_run (C R N ci pi li : Nat) (left right acc : PacketVector.Packet)
    (previous next : List Bool) (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hc : pi+1≤R) :
    Step resetParent (2*R+6) (parentH mh) (parentA C R N ci pi li left right acc previous next fields extra)
      (parentH mh) (parentA C R N ci 0 li left right acc previous next fields extra) := by
  let a:=parentA C R N ci pi li left right acc previous next fields extra
  have hzero : a 0=List.replicate R false := by
    change ZeroPadding.pad R []=List.replicate R false
    simp [ZeroPadding.pad]
  have h:=PhysicalIndexReload.run R (31 : Fin 297) 0 259 (by decide) (by decide) (by decide)
    (parentH mh) a rfl rfl rfl rfl (by rw [hzero,List.length_replicate])
    (by change (ZeroPadding.pad R (CompareMachine.word pi)).length=R
        simp [CompareMachine.word,Nat.max_eq_left hc])
  have ho : Function.update a 259 (a 0)=parentA C R N ci 0 li left right acc previous next fields extra := by
    rw [hzero,←VectorAccumulator.zero_count R (by omega)]
    change Function.update (Fin.addCases (m:=296) (n:=1) (motive:=fun _=>List Bool) _ _) ((259 : Fin 296).castAdd 1) _=_
    rw [PhysicalAppendUpdate.left,update_parent_index]
    rfl
  exact h.congr rfl ho

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
