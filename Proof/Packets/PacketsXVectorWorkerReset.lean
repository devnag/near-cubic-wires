import Proof.Packets.PacketsXVectorWorkerState

/-! Actual zero reload of the shared child/final-candidate counter. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem reset_child_run (C R ci pi li : Nat) (left right acc : List (List Bool))
    (previous next : List Bool) (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hc : ci+1≤R) :
    Step resetChild (2*R+6) (H mh) (A C R ci pi li left right acc previous next fields extra)
      (H mh) (A C R 0 pi li left right acc previous next fields extra) := by
  let a:=A C R ci pi li left right acc previous next fields extra
  have hzero : a 0=List.replicate R false := by
    change ZeroPadding.pad R []=List.replicate R false
    simp [ZeroPadding.pad]
  have h:=PhysicalIndexReload.run R (31 : Fin 296) 0 258 (by decide) (by decide) (by decide)
    (H mh) a rfl rfl rfl rfl (by rw [hzero,List.length_replicate])
    (by change (ZeroPadding.pad R (CompareMachine.word ci)).length=R
        simp [CompareMachine.word,Nat.max_eq_left hc])
  have ho : Function.update a 258 (a 0)=A C R 0 pi li left right acc previous next fields extra := by
    rw [hzero,←VectorAccumulator.zero_count R (by omega)]
    exact update_child_index C R ci 0 pi li left right acc previous next fields extra
  exact h.congr rfl ho

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
