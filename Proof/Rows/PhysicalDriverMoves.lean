import Proof.MachineModel.Runs

/-! Single paid head moves, retaining all tape words. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace Completion.PhysicalDriverMoves
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def machine (t : Nat) (move : HeadMove) : Machine t 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun s _=>if s.val=0 then some ⟨1,fun _=>none,fun _=>move⟩ else none

theorem run {t : Nat} (move : HeadMove) (H : Fin t→Nat) (A : Fin t→List Bool) :
    Step (machine t move) 1 H A (fun i=>move.apply (H i)) A := by
  have hs : step (machine t move) (⟨0,H,A⟩ : Configuration t 2)=
      some (⟨1,fun i=>move.apply (H i),A⟩ : Configuration t 2) := by
    simp [step,machine]
    apply configuration_ext
    · rfl
    · rfl
    · rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht.le⟩

end Completion.PhysicalDriverMoves
