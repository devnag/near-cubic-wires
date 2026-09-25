import Proof.Packets.PhysicalRepeatStep

/-! Existential-state counted execution. A finite physical worker invariant
can hide its cleared private tapes; no externally supplied trajectory is
required to obtain the actual Repeat receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRepeatExists
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem trajectory {α : Type} (P : Nat→α→Prop) (next : Nat→α→α→Prop) (N : Nat)
    (a : α) (ha : P 0 a)
    (step : ∀i,i<N→∀a,P i a→∃b,next i a b ∧ P (i+1) b) :
    ∃as : Nat→α,as 0=a ∧ (∀i,i≤N→P i (as i)) ∧ (∀i,i<N→next i (as i) (as (i+1))) := by
  induction N with
  | zero=>
    refine ⟨fun _=>a,rfl,?_,?_⟩
    · intro i hi
      have he:i=0 := by omega
      subst i
      exact ha
    · intro i hi;omega
  | succ N ih=>
    obtain ⟨as,h0,hP,hstep⟩:=ih (fun i hi=>step i (by omega))
    obtain ⟨b,hb,hPb⟩:=step N (by omega) (as N) (hP N le_rfl)
    let bs:=Function.update as (N+1) b
    refine ⟨bs,?_,?_,?_⟩
    · simpa only [bs,Function.update_of_ne (by omega : 0≠N+1)] using h0
    · intro i hi
      by_cases he:i=N+1
      · subst i;simpa only [bs,Function.update_self] using hPb
      · simpa only [bs,Function.update_of_ne he] using hP i (by omega)
    · intro i hi
      by_cases he:i=N
      · subst i
        simpa only [bs,Function.update_of_ne (by omega : N≠N+1),Function.update_self] using hb
      · simpa only [bs,Function.update_of_ne (by omega : i≠N+1),
          Function.update_of_ne (by omega : i+1≠N+1)] using hstep i (by omega)

theorem run {t s : Nat} (worker : Machine t s) (N E : Nat) (H : Fin t→Nat)
    (P : Nat→(Fin t→List Bool)→Prop) (A : Fin t→List Bool) (ha : P 0 A)
    (step : ∀i,i<N→∀a,P i a→∃b,Step worker E H a H b ∧ P (i+1) b) :
    ∃B,Step (RepeatMachine.machine worker (fun _ _=>true)) (N*(E+3)+3)
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases A (fun _ : Fin 1=>CompareMachine.word N))
      (Fin.addCases H (fun _ : Fin 1=>1))
      (Fin.addCases B (fun _ : Fin 1=>CompareMachine.word N)) ∧ P N B := by
  obtain ⟨as,h0,hP,hstep⟩:=trajectory P (fun _ a b=>Step worker E H a H b) N A ha step
  have h:=PhysicalRepeatStep.run worker N E (fun _=>H) as hstep
  rw [h0] at h
  exact ⟨as N,h,hP N le_rfl⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalRepeatExists
