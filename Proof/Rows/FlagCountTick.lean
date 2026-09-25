import Proof.Rows.MinimumMaskCell

/-! Co-emit one unit of the comparator's actual unary dimension per flag. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000
namespace PCJ45bee56da9f34d5a_FlagCountTick
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairOrdinary.RecoveryExecution
noncomputable section

def machine : Machine 1 2 where
 descriptionBits:=0
 start:=0
 halted:=fun q=>q.val==1
 rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>some true,fun _=>.right⟩ else none

theorem append_run (out : List Bool) :
 Step machine 1 (fun _=>out.length) (fun _=>out)
   (fun _=>out.length+1) (fun _=>out++[true]) := by
 have hs : step machine (⟨0,fun _=>out.length,fun _=>out⟩ : Configuration 1 2)=
   some ⟨1,fun _=>out.length+1,fun _=>out++[true]⟩ := by
  simp only [step,machine]
  apply congrArg some
  apply configuration_ext
  · rfl
  · rfl
  · funext i;simp [applyAction,Streaming.write_append]
 obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
 exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

theorem run (Q : Nat) :
 Step machine 1 (fun _=>Q+1) (fun _=>CompareMachine.word Q)
  (fun _=>Q+1+1) (fun _=>CompareMachine.word (Q+1)) := by
 have hl : (CompareMachine.word Q).length=Q+1 := by simp [CompareMachine.word]
 have ht : CompareMachine.word Q++[true]=CompareMachine.word (Q+1) := by
  simp only [CompareMachine.word,List.replicate_add,List.replicate_one,List.cons_append]
 have h:=append_run (CompareMachine.word Q)
 rw [hl,ht] at h
 exact h
end
end PCJ45bee56da9f34d5a_FlagCountTick
