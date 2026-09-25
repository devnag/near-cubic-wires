import Proof.Packets.PhysicalRepeatExists

/-! Actual counted execution with existential private tapes and changing
resident cursor positions. The repeat driver returns to its own start. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRepeatExists
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem run_heads {t s : Nat} (worker : Machine t s) (N E : Nat) (H : Nat→Fin t→Nat)
    (P : Nat→(Fin t→List Bool)→Prop) (A : Fin t→List Bool) (ha : P 0 A)
    (step : ∀i,i<N→∀a,P i a→∃b,Step worker E (H i) a (H (i+1)) b ∧ P (i+1) b) :
    ∃B,Step (RepeatMachine.machine worker (fun _ _=>true)) (N*(E+3)+3)
      (Fin.addCases (H 0) (fun _ : Fin 1=>1))
      (Fin.addCases A (fun _ : Fin 1=>CompareMachine.word N))
      (Fin.addCases (H N) (fun _ : Fin 1=>1))
      (Fin.addCases B (fun _ : Fin 1=>CompareMachine.word N)) ∧ P N B := by
  obtain ⟨as,h0,hP,hstep⟩:=trajectory P (fun i a b=>Step worker E (H i) a (H (i+1)) b) N A ha step
  have h:=PhysicalRepeatStep.run worker N E H as hstep
  rw [h0] at h
  exact ⟨as N,h,hP N le_rfl⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRepeatExists
