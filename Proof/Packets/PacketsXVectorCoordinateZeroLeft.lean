import Proof.Packets.PacketsXWindowProviderZeroLeft
import Proof.Packets.PacketsXVectorCoordinateCallback

/-! The paid left-operand reset in the full coordinate controller arena. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def clearCoordinateLeft:=RecoveryFocus.machine providerSlots WindowProvider.zeroLeft

theorem clear_coordinate_left_run (C R ci pi li : Nat) (left right acc : PacketVector.Packet)
    (previous next : List Bool) (fields : Fin 222 → List Bool) (extra : Fin 32 → List Bool)
    (hR : 1≤R) (hl : VectorAccumulator.Fits R left) :
    Step clearCoordinateLeft (4*R+5) (H (fun _=>0))
      (A C R ci pi li left right acc previous next fields extra) (H (fun _=>0))
      (A C R ci pi li [] right acc previous next fields extra) := by
  let B:=providerA C R left right fields
  have core : ∀i : Fin 34,B (i.castAdd 222)=ReusableArithmetic.state C R left right i := fun i=>Fin.addCases_left i
  obtain ⟨run,output⟩:=WindowProvider.zero_left_provider C R left right B hR hl core
  rw [←provider_heads_eq] at run
  have docked:=provider_dock C R ci pi li left right [] right acc previous next fields extra _ run output
  have kept : (fun j : Fin 222=>WindowProvider.leftZero R B (j.natAdd 34))=fields := by
    funext j
    have ne (i : Fin 256) (hi : i.val<34) : j.natAdd 34≠i := by
      intro he;have h:=congrArg (fun k : Fin 256=>k.val) he
      simp only [Fin.val_natAdd] at h
      omega
    rw [WindowProvider.zero_left_other R B _ (ne 25 (by decide)) (ne 28 (by decide))]
    exact Fin.addCases_right j
  rw [kept] at docked
  exact docked

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
