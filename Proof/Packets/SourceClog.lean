import Proof.CaseAnalysis.RowsOriginalSwitch
import Proof.Rows.PhysicalDriverMoves
import Proof.Rows.SourceDockCore

/-! Ceiling logarithm from actual raw unary input, including zero and one.
The second input cell selects the existing positive worker or the literal zero
writer. The branch and both cursor moves are paid physical transitions. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.SourceClog
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairSource
open NearCubicWires.RepairSource.VerifierDecoding

def sourceSlot : Fin 1→Fin 12:=fun _=>0
noncomputable def right:=RecoveryFocus.machine sourceSlot (PhysicalDriverMoves.machine 1 .right)
noncomputable def left:=RecoveryFocus.machine sourceSlot (PhysicalDriverMoves.machine 1 .left)
def zero : Machine 12 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun s _=>if s.val=0 then some ⟨1,fun i=>if i=10 then some false else none,fun _=>.stay⟩ else none
noncomputable def positive:=Composition.machine left CloseoutSchedule.Clog.machine
noncomputable def small:=Composition.machine left zero
noncomputable def branch:=CloseoutRowsOriginalSwitch.machine positive small 0
noncomputable def machine:=Composition.machine right branch
def input (v : Nat):=CloseoutSchedule.Clog.input v
def bootHeads : Fin 12→Nat:=fun i=>if i=0 then 1 else 0
def smallOutput (v : Nat) : Fin 12→List Bool:=fun i=>if i=10 then [false] else input v i
def budget (v : Nat):=CloseoutSchedule.Clog.budget v+6

theorem right_run (v : Nat) : Step right 1 (fun _=>0) (input v) bootHeads (input v):=by
  have h:=SourceDock.dock (PhysicalDriverMoves.run .right (fun _ : Fin 1=>0)
    (fun _=>input v 0)) sourceSlot (by decide) (fun _=>0) (input v)
    (by intro i;rfl) (by intro i;rfl)
  have hh:dockH sourceSlot (fun _=>0) (fun _=>HeadMove.right.apply 0)=bootHeads:=by
    funext i
    by_cases hi:i=0
    · subst i;exact dockH_slot sourceSlot (by decide) (fun _=>0) _ 0
    · rw [dockH_other sourceSlot _ _ _ (by intro j he;exact hi he.symm)]
      simp [bootHeads,hi]
  rw [hh,install_existing sourceSlot (input v) _ (by intro i;rfl)] at h
  exact h

theorem left_run (v : Nat) : Step left 1 bootHeads (input v) (fun _=>0) (input v):=by
  have h:=SourceDock.dock (PhysicalDriverMoves.run .left (fun _ : Fin 1=>1)
    (fun _=>input v 0)) sourceSlot (by decide) bootHeads (input v)
    (by intro i;rfl) (by intro i;rfl)
  have hh:dockH sourceSlot bootHeads (fun _=>HeadMove.left.apply 1)=(fun _=>0):=by
    funext i
    by_cases hi:i=0
    · subst i;exact dockH_slot sourceSlot (by decide) bootHeads _ 0
    · rw [dockH_other sourceSlot _ _ _ (by intro j he;exact hi he.symm)]
      simp [bootHeads,hi]
  rw [hh,install_existing sourceSlot (input v) _ (by intro i;rfl)] at h
  exact h

theorem zero_run (v : Nat) : Step zero 1 (fun _=>0) (input v) (fun _=>0) (smallOutput v):=by
  have h:step zero (⟨0,fun _=>0,input v⟩ : Configuration 12 2)=
      some ⟨1,fun _=>0,smallOutput v⟩:=by
    simp [step,zero]
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      by_cases hi:i=10
      · subst i;simp [applyAction,smallOutput,input,CloseoutSchedule.Clog.input,writeTapeBit]
      · simp [applyAction,smallOutput,hi]
  obtain ⟨r,hr,hf,hs⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads hf,congrArg Configuration.tapes hf,hs.le⟩

theorem run (v : Nat) : ∃ O,Step machine (budget v) (fun _=>0) (input v) (fun _=>0) O ∧
    O 10=CompareMachine.word (Nat.clog 2 v):=by
  have scanned:readTapeBit (input v 0) (bootHeads 0)=decide (2≤v):=by
    simp only [input,CloseoutSchedule.Clog.input,if_pos rfl,bootHeads,readTapeBit,List.getD,List.getElem?_replicate]
    by_cases hv:2≤v
    · have hh:1<v:=by omega
      simp [hh,hv]
    · have hh:¬1<v:=by omega
      simp [hh,hv]
  by_cases hv:2≤v
  · obtain ⟨O,⟨r,hr,rt,rh,rs⟩,hout⟩:=CloseoutSchedule.Clog.clog_run v hv
    have base:Step CloseoutSchedule.Clog.machine (CloseoutSchedule.Clog.budget v)
        (fun _=>0) (input v) (fun _=>0) O:=⟨r,hr,funext rh,rt,rs⟩
    have h:=CloseoutRowsOriginalSwitch.true_run positive small 0 ((left_run v).seq base)
      (by rw [scanned];simp [hv])
    refine ⟨O,?_,hout⟩
    exact ((right_run v).seq h).enlarge (by simp only [budget];omega)
  · have h:=CloseoutRowsOriginalSwitch.false_run positive small 0 ((left_run v).seq (zero_run v))
      (by rw [scanned];simp [hv])
    refine ⟨smallOutput v,((right_run v).seq h).enlarge ?_,?_⟩
    · simp only [budget,CloseoutSchedule.Clog.budget];omega
    · have he:Nat.clog 2 v=0:=Nat.clog_of_right_le_one (by omega) 2
      simp [smallOutput,he,CompareMachine.word]

end Completion.SourceClog
