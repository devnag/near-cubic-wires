import Proof.Packets.WalkUnframe
import Proof.Rows.SourceDockCore

/-! Read the second coordinate before the first. This is the actual bit
order of the Toeplitz walk equivalence, before low-padding removal. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkVertexBits
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound Completion

def secondSlots : Fin 2→Fin 3:=![1,2]
def firstSlots : Fin 2→Fin 3:=![0,2]
noncomputable def second:=RecoveryFocus.machine secondSlots WalkUnframe.machine
noncomputable def first:=RecoveryFocus.machine firstSlots WalkUnframe.machine
noncomputable def machine:=Composition.machine second first
def input (x y : List Bool) : Fin 3→List Bool:=![frame x,frame y,[]]
def middle (x y : List Bool) : Fin 3→List Bool:=![frame x,frame y,y]
def output (x y : List Bool) : Fin 3→List Bool:=![frame x,frame y,y++x]
def middleHeads (y : List Bool) : Fin 3→Nat:=![0,2*y.length+1,y.length]
def outputHeads (x y : List Bool) : Fin 3→Nat:=![2*x.length+1,2*y.length+1,(y++x).length]
def budget (x y : List Bool):=2*y.length+1+1+(2*x.length+1)

theorem second_run (x y : List Bool) : Step second (2*y.length+1)
    (fun _=>0) (input x y) (middleHeads y) (middle x y) := by
  have base:=WalkUnframe.run [] y [] []
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at base
  have h:=SourceDock.dock base secondSlots (by decide) (fun _=>0) (input x y)
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  apply h.congr
  · funext i;fin_cases i
    · exact dockH_other secondSlots _ _ 0 (by intro j;fin_cases j <;>decide)
    · exact dockH_slot secondSlots (by decide) _ _ 0
    · exact dockH_slot secondSlots (by decide) _ _ 1
  · funext i;fin_cases i
    · exact install_other secondSlots _ _ 0 (by intro j;fin_cases j <;>decide)
    · exact install_slot secondSlots (by decide) _ _ 0
    · exact install_slot secondSlots (by decide) _ _ 1

theorem first_run (x y : List Bool) : Step first (2*x.length+1)
    (middleHeads y) (middle x y) (outputHeads x y) (output x y) := by
  have base:=WalkUnframe.run [] x [] y
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at base
  have h:=SourceDock.dock base firstSlots (by decide) (middleHeads y) (middle x y)
    (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>rfl)
  apply h.congr
  · funext i;fin_cases i
    · exact dockH_slot firstSlots (by decide) _ _ 0
    · exact dockH_other firstSlots _ _ 1 (by intro j;fin_cases j <;>decide)
    · exact dockH_slot firstSlots (by decide) _ _ 1
  · funext i;fin_cases i
    · exact install_slot firstSlots (by decide) _ _ 0
    · exact install_other firstSlots _ _ 1 (by intro j;fin_cases j <;>decide)
    · exact install_slot firstSlots (by decide) _ _ 1

theorem run (x y : List Bool) : Step machine (budget x y)
    (fun _=>0) (input x y) (outputHeads x y) (output x y) :=
  (second_run x y).seq (first_run x y)

noncomputable def ready:=MaskedReset.machine machine (fun _=>true)
def readyInput (x y : List Bool) : Fin 4→List Bool:=![frame x,frame y,[],[]]

theorem ready_run (x y : List Bool) : ∃log,
    Step ready (2*budget x y+2) (fun _=>0) (readyInput x y) (fun _=>0)
      (![frame x,frame y,y++x,log]) ∧ log.length≤budget x y := by
  obtain ⟨base,br,bh,bt,bs⟩:=run x y
  have bound : ∀i,(base.final.heads i)≤base.steps := by
    intro i
    have h:=SelectiveReset.prefix_head (prefix_of_run machine (budget x y)
      (⟨machine.start,fun _=>0,input x y⟩) base br).1 i
    simpa using h
  obtain ⟨r,rr,rf,rs,_⟩:=MaskedReset.reset_run machine (fun _=>true) (budget x y)
    (⟨machine.start,fun _=>0,input x y⟩) base br (by intro i _;exact bound i)
  refine ⟨List.replicate base.steps false,?_,by simpa using bs⟩
  have fuel : 2*base.steps+2≤2*budget x y+2 := by omega
  have hr:=runFrom_moreFuel ready _ (2*budget x y+2-(2*base.steps+2)) _ r rr
  rw [Nat.add_sub_of_le fuel] at hr
  have initial_eq : Rewind.recording (⟨machine.start,fun _=>0,input x y⟩) 0=
      (⟨ready.start,fun _=>0,readyInput x y⟩ : Configuration 4 _) := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>rfl
  rw [initial_eq] at hr
  refine ⟨r,hr,?_,?_,by omega⟩
  · rw [rf]
    funext i;fin_cases i <;>rfl
  · rw [rf]
    change (fun i=>Fin.addCases (motive:=fun _=>List Bool) base.final.tapes
      (fun _ : Fin 1=>List.replicate base.steps false) i)=_
    rw [bt]
    funext i;fin_cases i <;>rfl

end Theorem25Completion.WalkVertexBits
