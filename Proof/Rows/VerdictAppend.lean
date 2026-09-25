import Proof.Rows.ThresholdTraversal

/-! Copy one actual verdict bit to the unbounded output at its append cursor.
The input tape and every preceding output cell remain unchanged. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000
namespace PCJ45bee56da9f34d5a_VerdictAppend
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
noncomputable section

def machine:Machine 2 2 where
 descriptionBits:=0
 start:=0
 halted:=fun q=>q.val==1
 rule:=fun q scanned=>if q.val=0 then some ⟨1,
  fun i=>if i=1 then some (scanned 0) else none,
  fun i=>if i=1 then .right else .stay⟩ else none

theorem run (source out :List Bool) (b :Bool) (hb :readTapeBit source 0=b):
 Step machine 1 (![0,out.length] :Fin 2→Nat) ![source,out]
  (![0,out.length+1] :Fin 2→Nat) ![source,out++[b]] :=by
 have hs:step machine (⟨0,![0,out.length],![source,out]⟩ :Configuration 2 2)=
  some ⟨1,![0,out.length+1],![source,out++[b]]⟩:=by
  simp only [step,machine]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i
    · rfl
    · change writeTapeBit out out.length (readTapeBit source 0)=out++[b]
      rw [hb,Streaming.write_append]
 obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) hs).run (by rfl)
 exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
end
end PCJ45bee56da9f34d5a_VerdictAppend
