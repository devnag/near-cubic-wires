import Proof.Packets.PacketsXMajorityCompleteColdRun

/-! The generated visit-count word survives the square, palette copy and
majority initialization. This is the physical column-controller driver. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open Completion.SourceDock
noncomputable section

theorem afterScalar_count (C R n : Nat) (source : List Bool) :
    afterScalar C R n source 146=CompareMachine.word (n+1) := by
  change install scalarSlots _ _ (scalarSlots 5)=_
  rw [install_slot scalarSlots scalar_injective]
  exact scalar_N n

theorem afterCopy_count (C R n : Nat) (source : List Bool) :
    afterCopy C R n source 146=CompareMachine.word (n+1) := by
  change install copySlots _ _ (copySlots 5)=_
  rw [install_slot copySlots copy_injective]
  rfl

theorem result_count (C R n : Nat) (ps : List (Ring.Poly Nat)) :
    result C R n ps 146=CompareMachine.word (n+1) := by
  rw [result,install_other arenaSlots _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    simp only [arenaSlots,Fin.val_castAdd] at hv
    omega)]
  exact afterCopy_count C R n _

theorem result_count_head : resultHeads 146=0 := by
  rw [resultHeads,dockH_other arenaSlots _ _ _ (by
    intro j h
    have hv:=congrArg Fin.val h
    simp only [arenaSlots,Fin.val_castAdd] at hv
    omega)]
  rfl

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Cold
