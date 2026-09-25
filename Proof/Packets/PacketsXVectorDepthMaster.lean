import Proof.Packets.PacketsXVectorPopulationMaster

/-! Initialize the descending depth index from the genuine retained graded
source result. Both source and target cursor conventions are physically paid. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def depthMaster := PhysicalIndexReload.machine (31 : Fin 299) 177 260

theorem depth_master_run (R depth : Nat) (A : Fin 299→List Bool)
    (hR : A 31=UnaryTemplate.tape R) (hd : A 177=ZeroPadding.pad R (CompareMachine.word depth))
    (hcap : depth+1≤R) (ht : (A 260).length=R) :
    Step depthMaster (2*R+6) heads A heads
      (Function.update A 260 (ZeroPadding.pad R (CompareMachine.word depth))) := by
  have h:=PhysicalIndexReload.run R (31 : Fin 299) 177 260 (by decide) (by decide) (by decide)
    heads A rfl rfl rfl hR (by simp [hd,ZeroPadding.pad_length,CompareMachine.word,Nat.max_eq_left hcap]) ht
  rw [hd] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
