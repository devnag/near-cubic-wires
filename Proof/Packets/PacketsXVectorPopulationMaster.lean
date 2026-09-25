import Proof.Packets.PacketsXVectorPopulationBoot

/-! The original population remains separately resident after the literal
count doubles. Its actual retained counter is copied into the ModeCache ABI. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def populationMaster := PhysicalCopyInto.machine (31 : Fin 299) 281 161

theorem population_master_run (R M : Nat) (A : Fin 299→List Bool)
    (hR : A 31=UnaryTemplate.tape R) (hM : A 281=ZeroPadding.pad R (CompareMachine.word M))
    (hcap : M+1≤R) (ht : (A 161).length=R) :
    Step populationMaster (2*R+2) heads A heads
      (Function.update A 161 (ZeroPadding.pad R (CompareMachine.word M))) := by
  have h:=PhysicalCopyInto.run R (31 : Fin 299) 281 161 (by decide) (by decide) (by decide)
    heads A rfl rfl rfl hR (by simp [hM,ZeroPadding.pad_length,CompareMachine.word,Nat.max_eq_left hcap]) ht
  rw [hM] at h
  exact h

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
