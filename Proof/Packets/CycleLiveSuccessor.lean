import Proof.MachineModel.UWalkUnary
import Proof.MachineModel.Runs

/-! The Header's Q=live.card+1 word is physically copied from the pool builder's
retained live-count template. The leading/trailing sentinels and all reserves
are literal input/output tape words. All heads return to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace Theorem25Completion.CycleLiveSuccessor
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding


theorem source_eq (K : Nat) : UWalkUnary.source (K+2) K=UnaryTemplate.tape K := by
  simp [UWalkUnary.source,ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape]

theorem pad_compare_template (C K : Nat) (h : K+2≤C) :
    ZeroPadding.pad C (CompareMachine.word K)=ZeroPadding.pad C (UnaryTemplate.tape K) := by
  have hw : (CompareMachine.word K).length=K+1 := by simp [CompareMachine.word]
  have ht : UnaryTemplate.tape K=CompareMachine.word K++[false] := by
    simp [UnaryTemplate.tape,CompareMachine.word]
  rw [ht]
  simp only [ZeroPadding.pad,hw,List.length_append,List.length_singleton,List.append_assoc]
  congr 1
  have he : C-(K+1)=1+(C-(K+1+1)) := by omega
  rw [he,List.replicate_add]
  rfl

end Theorem25Completion.CycleLiveSuccessor
