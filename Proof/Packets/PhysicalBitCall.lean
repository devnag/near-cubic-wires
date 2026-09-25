import Proof.Packets.PhysicalConditional
import Proof.Rows.PhysicalFocusBoundary

/-! A physical bit test followed by an optional ordinary worker call. The
branch is chosen from the actual tape under the actual head. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalBitCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

def probe {t : Nat} (slot : Fin t) : Machine t 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val != 0
  rule:=fun q bits=>if q.val=0 then
    some ⟨if bits slot then 1 else 2,fun _=>none,fun _=>.stay⟩ else none

def accept (q : Fin 3) : Bool := q.val==1
noncomputable def machine {t s : Nat} (slot : Fin t) (p : Machine t s) :=
  PhysicalConditional.machine (probe slot) p accept

theorem probe_run {t : Nat} (slot : Fin t) (H : Fin t→Nat) (A : Fin t→List Bool) :
    ∃ r,runFrom (probe slot) 1 ⟨(probe slot).start,H,A⟩=some r ∧
      r.final=(⟨if readTapeBit (A slot) (H slot) then 1 else 2,H,A⟩ : Configuration t 3) ∧ r.steps=1 := by
  have hs : step (probe slot) (⟨0,H,A⟩ : Configuration t 3)=
      some ⟨if readTapeBit (A slot) (H slot) then 1 else 2,H,A⟩ := by
    simp only [step,probe]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;simp [applyAction,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by cases readTapeBit (A slot) (H slot) <;>rfl)

theorem run_true {t s fuel : Nat} {p : Machine t s} (slot : Fin t)
    {H H' : Fin t→Nat} {A A' : Fin t→List Bool}
    (bit : readTapeBit (A slot) (H slot)=true) (hp : Step p fuel H A H' A') :
    Step (machine slot p) (fuel+3) H A H' A' := by
  obtain ⟨prior,hr,hf,_⟩ := probe_run slot H A
  obtain ⟨last,hl,hh,ht,_⟩ := hp
  have hcall : runFrom p fuel ⟨p.start,prior.final.heads,prior.final.tapes⟩=some last := by rwa [hf]
  have ha : accept prior.final.control=true := by simp [hf,bit,accept]
  obtain ⟨r,rr,rs,rh,rt⟩ := PhysicalConditional.accepted (probe slot) p accept 1 fuel H A prior last hr hcall ha
  have hn : 1+1+fuel+1=fuel+3 := by omega
  rw [hn] at rr rs
  exact ⟨r,rr,rh.trans hh,rt.trans ht,rs⟩

theorem run_false {t s : Nat} {p : Machine t s} (slot : Fin t)
    (H : Fin t→Nat) (A : Fin t→List Bool) (bit : readTapeBit (A slot) (H slot)=false) :
    Step (machine slot p) 2 H A H A := by
  obtain ⟨prior,hr,hf,_⟩ := probe_run slot H A
  have ha : accept prior.final.control=false := by simp [hf,bit,accept]
  obtain ⟨r,rr,rs,rh,rt⟩ := PhysicalConditional.rejected (probe slot) p accept 1 H A prior hr ha
  exact ⟨r,rr,by simpa only [hf] using rh,by simpa only [hf] using rt,rs⟩

end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalBitCall
