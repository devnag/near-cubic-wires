import Proof.Packets.VectorAccumulatorData

/-! Actual transfer of the current right packet into the left operand.
The right packet and both resident accumulator tapes are preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 180000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
noncomputable section

def rightToLeft := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 26 25)
  (PhysicalCopyInto.machine (31 : Fin 36) 27 28)

theorem right_to_left_run (B R : Nat) (left right stored : List (List Bool))
    (hl : Fits R left) (hr : Fits R right) :
    Step rightToLeft (copyBudget R) heads (tapes B R left right stored)
      heads (tapes B R right right stored) := by
  let a:=tapes B R left right stored
  have first:=PhysicalCopyInto.run R (31 : Fin 36) 26 25 (by decide) (by decide) (by decide)
    heads a rfl rfl rfl rfl (flat_length R right hr) (flat_length R left hl)
  have second:=PhysicalCopyInto.run R (31 : Fin 36) 27 28 (by decide) (by decide) (by decide)
    heads (Function.update a 25 (a 26)) rfl rfl rfl rfl
    (count_length R right hr) (count_length R left hl)
  have h:=first.seq second
  have out : Function.update (Function.update a 25 (a 26)) 28
      ((Function.update a 25 (a 26)) 27)=tapes B R right right stored := by
    apply update_pair_eq a (tapes B R right right stored) 25 28 (a 26) ((Function.update a 25 (a 26)) 27) (by decide) rfl rfl
    intro i h25 h28
    exact tapes_left_outside B R left right right stored i h25 h28
  have fuel : (2*R+2)+1+(2*R+2)=copyBudget R := by unfold copyBudget;omega
  rw [fuel] at h
  exact h.congr rfl out

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
