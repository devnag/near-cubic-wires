import Proof.Packets.PhysicalBitCall

/-! Execute a fixed worker exactly when the physically scanned bit is false. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalBitCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

def acceptFalse (q : Fin 3) : Bool := q.val==2
noncomputable def falseMachine {t s : Nat} (slot : Fin t) (p : Machine t s) :=
  PhysicalConditional.machine (probe slot) p acceptFalse

theorem false_run {t s fuel : Nat} {p : Machine t s} (slot : Fin t)
    {H H' : Fin t→Nat} {A A' : Fin t→List Bool}
    (bit : readTapeBit (A slot) (H slot)=false) (hp : Step p fuel H A H' A') :
    Step (falseMachine slot p) (fuel+3) H A H' A' := by
  obtain ⟨prior,hr,hf,_⟩:=probe_run slot H A
  obtain ⟨last,hl,hh,ht,_⟩:=hp
  have hcall : runFrom p fuel ⟨p.start,prior.final.heads,prior.final.tapes⟩=some last:=by rwa [hf]
  have ha : acceptFalse prior.final.control=true:=by simp [hf,bit,acceptFalse]
  obtain ⟨r,rr,rs,rh,rt⟩:=PhysicalConditional.accepted (probe slot) p acceptFalse 1 fuel H A prior last hr hcall ha
  have hn : 1+1+fuel+1=fuel+3:=by omega
  rw [hn] at rr rs
  exact ⟨r,rr,rh.trans hh,rt.trans ht,rs⟩

theorem true_skip {t s : Nat} {p : Machine t s} (slot : Fin t)
    (H : Fin t→Nat) (A : Fin t→List Bool) (bit : readTapeBit (A slot) (H slot)=true) :
    Step (falseMachine slot p) 2 H A H A := by
  obtain ⟨prior,hr,hf,_⟩:=probe_run slot H A
  have ha : acceptFalse prior.final.control=false:=by simp [hf,bit,acceptFalse]
  obtain ⟨r,rr,rs,rh,rt⟩:=PhysicalConditional.rejected (probe slot) p acceptFalse 1 H A prior hr ha
  exact ⟨r,rr,by simpa only [hf] using rh,by simpa only [hf] using rt,rs⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalBitCall
