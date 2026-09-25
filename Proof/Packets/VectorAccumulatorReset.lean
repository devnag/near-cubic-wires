import Proof.Packets.VectorAccumulatorData

/-! Reset saved parent-accumulator storage using the arithmetic arena's
actual retained zero tape. The R-bit writes and both cursor returns are paid. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def reset := Composition.machine (PhysicalCopyInto.machine (31 : Fin 36) 0 34)
  (PhysicalCopyInto.machine (31 : Fin 36) 0 35)

theorem zero_source (B R : Nat) (left right stored : List (List Bool)) :
    tapes B R left right stored 0=List.replicate R false := by
  change ZeroPadding.pad R []=List.replicate R false
  simp [ZeroPadding.pad]

theorem zero_count (R : Nat) (hR : 1≤R) :
    ZeroPadding.pad R (CompareMachine.word 0)=List.replicate R false := by
  change List.replicate 1 false++List.replicate (R-1) false=List.replicate R false
  rw [←List.replicate_add,show 1+(R-1)=R by omega]

theorem reset_run (B R : Nat) (left right stored : List (List Bool)) (hs : Fits R stored) :
    Step reset (copyBudget R) heads (tapes B R left right stored)
      heads (tapes B R left right []) := by
  let a:=tapes B R left right stored
  have hz : a 0=List.replicate R false := zero_source B R left right stored
  have hlen : (a 0).length=R := by rw [hz,List.length_replicate]
  have first:=PhysicalCopyInto.run R (31 : Fin 36) 0 34 (by decide) (by decide) (by decide)
    heads a rfl rfl rfl rfl hlen (flat_length R stored hs)
  have second:=PhysicalCopyInto.run R (31 : Fin 36) 0 35 (by decide) (by decide) (by decide)
    heads (Function.update a 34 (a 0)) rfl rfl rfl rfl
    (by simpa only [Function.update_of_ne (show (0 : Fin 36)≠34 by decide)] using hlen)
    (count_length R stored hs)
  have out : Function.update (Function.update a 34 (a 0)) 35
      ((Function.update a 34 (a 0)) 0)=tapes B R left right [] := by
    apply update_pair_eq a (tapes B R left right []) 34 35 (a 0)
      ((Function.update a 34 (a 0)) 0) (by decide)
    · change ZeroPadding.pad R []=a 0
      rw [hz];simp [ZeroPadding.pad]
    · simp only [Function.update_of_ne (show (0 : Fin 36)≠34 by decide)]
      change ZeroPadding.pad R (CompareMachine.word 0)=a 0
      rw [hz]
      exact zero_count R (by have h:=hs.2;omega)
    · intro i h34 h35
      exact tapes_saved_outside B R left right stored [] i h34 h35
  have h:=first.seq second
  have fuel : (2*R+2)+1+(2*R+2)=copyBudget R := by unfold copyBudget;omega
  rw [fuel] at h
  exact h.congr rfl out

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorAccumulator
