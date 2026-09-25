import Proof.Packets.VectorAccumulatorData
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem load_run (B R : Nat) (left right stored : List (List Bool))
    (hl : Fits R left) (hs : Fits R stored) :
    Step load (copyBudget R) heads (tapes B R left right stored)
      heads (tapes B R stored right stored) := by
  let a:=tapes B R left right stored
  have first:=PhysicalCopyInto.run R (31 : Fin 36) 34 25 (by decide) (by decide) (by decide)
    heads a rfl rfl rfl rfl (flat_length R stored hs) (flat_length R left hl)
  have second:=PhysicalCopyInto.run R (31 : Fin 36) 35 28 (by decide) (by decide) (by decide)
    heads (Function.update a 25 (a 34)) rfl rfl rfl rfl
    (count_length R stored hs) (count_length R left hl)
  have h:=first.seq second
  have out : Function.update (Function.update a 25 (a 34)) 28
      ((Function.update a 25 (a 34)) 35)=tapes B R stored right stored := by
    apply update_pair_eq a (tapes B R stored right stored) 25 28 (a 34) ((Function.update a 25 (a 34)) 35) (by decide) rfl rfl
    intro i h25 h28
    exact tapes_left_outside B R left right stored stored i h25 h28
  have fuel : (2*R+2)+1+(2*R+2)=copyBudget R := by unfold copyBudget;omega
  rw [fuel] at h
  exact h.congr rfl out

theorem save_run (B R : Nat) (left right stored : List (List Bool))
    (hl : Fits R left) (hs : Fits R stored) :
    Step save (copyBudget R) heads (tapes B R left right stored)
      heads (tapes B R left right left) := by
  let a:=tapes B R left right stored
  have first:=PhysicalCopyInto.run R (31 : Fin 36) 25 34 (by decide) (by decide) (by decide)
    heads a rfl rfl rfl rfl (flat_length R left hl) (flat_length R stored hs)
  have second:=PhysicalCopyInto.run R (31 : Fin 36) 28 35 (by decide) (by decide) (by decide)
    heads (Function.update a 34 (a 25)) rfl rfl rfl rfl
    (count_length R left hl) (count_length R stored hs)
  have h:=first.seq second
  have out : Function.update (Function.update a 34 (a 25)) 35
      ((Function.update a 34 (a 25)) 28)=tapes B R left right left := by
    apply update_pair_eq a (tapes B R left right left) 34 35 (a 25) ((Function.update a 34 (a 25)) 28) (by decide) rfl rfl
    intro i h34 h35
    exact tapes_saved_outside B R left right stored left i h34 h35
  have fuel : (2*R+2)+1+(2*R+2)=copyBudget R := by unfold copyBudget;omega
  rw [fuel] at h
  exact h.congr rfl out

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
