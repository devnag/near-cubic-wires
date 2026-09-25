import Proof.Packets.WalkTranscriptColumnFirst
import Proof.Packets.PhysicalRepeatExistsHeads

/-! Existential-workspace version of the paid first-plus-remaining driver.
The supplied local transitions are executed by the fixed worker, while the
physical retained count word determines the exact number of transitions. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace Theorem25Completion.WalkTranscriptColumnController
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed.Materializer
noncomputable section

theorem run_exists {s : Nat} (worker : Machine 471 s) (R M E : Nat)
    (H : Nat→Fin 471→Nat) (P : Nat→(Fin 471→List Bool)→Prop) (A : Fin 471→List Bool)
    (ha : P 0 A)
    (step : ∀i,i<M→∀a,P i a→∃b,Step worker E (H i) a (H (i+1)) b ∧ P (i+1) b) :
    ∃B,Step (machine worker) (budget M E)
      (Function.update (heads (H 0)) 29 0) (tapes R M A)
      (heads (H M)) (tapes R M B) ∧ P M B := by
  obtain ⟨as,h0,hP,hstep⟩:=PhysicalRepeatExists.trajectory P
    (fun i a b=>Step worker E (H i) a (H (i+1)) b) M A ha step
  have actual:=run worker R M E H as hstep
  rw [h0] at actual
  exact ⟨as M,actual,hP M le_rfl⟩

theorem first_then_remaining_exists {s t : Nat} (consumer : Machine 471 s) (worker : Machine 471 t)
    (firstFuel R M E : Nat) (initialH : Fin 471→Nat) (initialA : Fin 471→List Bool)
    (H : Nat→Fin 471→Nat) (P : Nat→(Fin 471→List Bool)→Prop)
    (firstStep : ∃a,Step consumer firstFuel initialH initialA (H 0) a ∧ P 0 a)
    (step : ∀i,i<M→∀a,P i a→∃b,Step worker E (H i) a (H (i+1)) b ∧ P (i+1) b) :
    ∃B,Step (firstThenRemaining consumer worker) (firstFuel+1+budget M E)
      (Function.update (heads initialH) 29 0) (tapes R M initialA)
      (heads (H M)) (tapes R M B) ∧ P M B := by
  obtain ⟨middle,firstStep,hm⟩:=firstStep
  obtain ⟨B,last,hB⟩:=run_exists worker R M E H P middle hm step
  exact ⟨B,(first_run consumer firstFuel R M initialH (H 0) initialA middle firstStep).seq last,hB⟩

end
end Theorem25Completion.WalkTranscriptColumnController
