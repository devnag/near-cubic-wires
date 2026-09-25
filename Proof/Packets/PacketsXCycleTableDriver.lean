import Proof.CaseAnalysis.CapacityPower
import Proof.MachineModel.Layout

/-! The complete table loop driver is physically generated in linear time in
its unary length. A single paid write changes raw2^s to Compare(2^s−1) and
boots its sentinel cursor, including the s=0 one-cell table. -/
namespace Theorem25Completion.CycleTableDriver
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.RepairSource
open NearCubicWires.RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section

def mark : Machine 1 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun s _=>if s.val=0 then some ⟨1,fun _=>some false,fun _=>.right⟩ else none

theorem mark_run (n : Nat) : Step mark 1 (fun _=>0) (fun _=>List.replicate (n+1) true)
    (fun _=>1) (fun _=>CompareMachine.word n) := by
  have hs: step mark (⟨0,(fun _=>0),(fun _=>List.replicate (n+1) true)⟩ : Configuration 1 2)=
      some ⟨1,(fun _=>1),(fun _=>CompareMachine.word n)⟩ := by
    simp [step,mark]
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i
      simp [applyAction,writeTapeBit,List.replicate_succ,CompareMachine.word]
  obtain ⟨r,hr,hf,ht⟩:=(Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,ht.le⟩

def slot : Fin 1→Fin 17:=fun _=>15
abbrev machine:=Composition.machine CloseoutCapacity.Power.machine (RecoveryFocus.machine slot mark)
def heads (i : Fin 17) : Nat:=if i=15 then 1 else 0
def budget (s : Nat):=CloseoutCapacity.Power.budget s+2

theorem run (s : Nat) : ∃ out : Fin 17→List Bool,
    Step machine (budget s) (fun _=>0) (CloseoutCapacity.Power.input s) heads out ∧
      out 15=CompareMachine.word (2^s-1) ∧ out 13=UnaryTemplate.tape (2^s) := by
  obtain ⟨mid,ready,hraw,htemplate⟩:=CloseoutCapacity.Power.power_run s
  obtain ⟨r,hr,ht,hh,hsteps⟩:=ready
  have power : Step CloseoutCapacity.Power.machine (CloseoutCapacity.Power.budget s)
      (fun _=>0) (CloseoutCapacity.Power.input s) (fun _=>0) mid :=
    ⟨r,hr,funext hh,ht,hsteps⟩
  have hp:2^s-1+1=2^s:=by have h:=Nat.two_pow_pos s;omega
  have marker:=mark_run (2^s-1)
  rw [hp] at marker
  have h:=marker.dock slot (by decide) (fun _ : Fin 17=>0) mid (fun _=>rfl)
    (by intro i;fin_cases i;exact hraw)
  have hh':dockH slot (fun _ : Fin 17=>0) (fun _ : Fin 1=>1)=heads := by
    funext i
    by_cases hi:i=15
    · subst i;exact dockH_slot slot (by decide) _ _ 0
    · rw [dockH_other slot _ _ i (by intro j hj;exact hi hj.symm)]
      simp [heads,hi]
  refine ⟨_,(power.seq h).congr hh' rfl,?_,?_⟩
  · exact install_slot slot (by decide) _ _ 0
  · exact (install_other slot _ _ 13 (by decide)).trans htemplate

end
end Theorem25Completion.CycleTableDriver
