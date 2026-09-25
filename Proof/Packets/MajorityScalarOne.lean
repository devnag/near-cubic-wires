import Proof.PCP.ProjectionDimensionTemplate
import Proof.Rows.PhysicalDriverMoves
import Proof.Rows.SourceDockCore

/-! The fixed comparison word for one is written by two paid actions. -/
set_option autoImplicit false
set_option warningAsError true
namespace Completion.MajorityScalarOne
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==2
  rule:=fun s _=>if s.val=0 then some ⟨1,fun _=>some false,fun _=>.right⟩
    else if s.val=1 then some ⟨2,fun _=>some true,fun _=>.left⟩ else none

theorem run : Step machine 2 (fun _=>0) (fun _=>[]) (fun _=>0)
    (fun _=>CompareMachine.word 1) := by
  let mid : Configuration 1 3:=⟨1,fun _=>1,fun _=>[false]⟩
  let fin : Configuration 1 3:=⟨2,fun _=>0,fun _=>CompareMachine.word 1⟩
  have first : step machine (initialConfiguration machine (fun _=>[]))=some mid := by
    rfl
  have last : step machine mid=some fin := by rfl
  obtain ⟨r,hr,hf,hs⟩:=((Timed.single (by rfl) first).trans (Timed.single (by rfl) last)).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le⟩

end Completion.MajorityScalarOne
