import Proof.Packets.CycleCommonReserve
import Proof.Rows.PhysicalDriverMoves
import Proof.Rows.PhysicalFocusBoundary
import Proof.Rows.SourceDockCore

/-! Produce the quadratic rewind template from the resident packet-width
word. The square is computed by the fixed unary multiplication program. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Width
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization
open Theorem25Completion
open Completion.SourceDock
noncomputable section

def powerOutput (R : Nat) : Fin 7→List Bool := Classical.choose (DimensionPower.power_run 2 1 R)
def power := TapeEmbedding.machine 2 (DimensionPower.machine 2 1)
def templateSlots : Fin 3→Fin 9 := ![5,7,8]
def template := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def machine := Composition.machine power template

def input (R : Nat) : Fin 9→List Bool :=
  Fin.addCases (m:=7) (n:=2) (motive:=fun _=>List Bool) (DimensionPower.input 2 R) (fun _=>[])
def middle (R : Nat) : Fin 9→List Bool :=
  Fin.addCases (m:=7) (n:=2) (motive:=fun _=>List Bool) (powerOutput R) (fun _=>[])
def output (R : Nat) := install templateSlots (middle R) (DimensionTemplate.output false (R^2))
def budget (R : Nat) := DimensionPower.cost 1 R 2+1+(2*R^2+8)

theorem source_power (R : Nat) : powerOutput R 0=UnaryTemplate.tape R :=
  (Classical.choose_spec (DimensionPower.power_run 2 1 R)).2.1

theorem value_power (R : Nat) : powerOutput R 5=List.replicate (R^2) true := by
  have he : DimensionPower.valueSlot 2 2 le_rfl=(5 : Fin 7) := by
    apply Fin.ext
    rfl
  have h:=(Classical.choose_spec (DimensionPower.power_run 2 1 R)).2.2
  change powerOutput R (DimensionPower.valueSlot 2 2 le_rfl)=List.replicate (1*R^2) true at h
  rw [he,Nat.one_mul] at h
  exact h

theorem zero_heads {t : Nat} (slots : Fin t→Fin 9) :
    dockH slots (fun _ : Fin 9=>0) (fun _=>0)=(fun _=>0) := by
  funext i
  unfold dockH
  cases RecoveryFocus.pick slots i <;>rfl

theorem run (R : Nat) : Step machine (budget R) (fun _=>0) (input R)
    (fun _=>0) (output R) := by
  have first:=(CycleCommonReserve.of_clock
    (Classical.choose_spec (DimensionPower.power_run 2 1 R)).1).embed
    (fun _ : Fin 2=>0) (fun _ : Fin 2=>([] : List Bool))
  have entry : ∀i,middle R (templateSlots i)=DimensionTemplate.input (R^2) i := by
    intro i;fin_cases i
    · exact value_power R
    · rfl
    · rfl
  have second:=Completion.SourceDock.dock
    (CycleCommonReserve.of_clock (DimensionTemplate.ready false (R^2))) templateSlots (by decide) (fun _ : Fin 9=>0) (middle R) (by intros;rfl) entry
  have zero : (Fin.addCases (m:=7) (n:=2) (motive:=fun _=>Nat)
      (fun _=>0) (fun _=>0))=(fun _ : Fin 9=>0) := by
    funext i;fin_cases i <;>rfl
  change Step power (DimensionPower.cost 1 R 2)
    (Fin.addCases (m:=7) (n:=2) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)) (input R)
    (Fin.addCases (m:=7) (n:=2) (motive:=fun _=>Nat) (fun _=>0) (fun _=>0)) (middle R) at first
  rw [zero] at first
  exact (first.seq second).congr (zero_heads templateSlots) rfl

theorem source (R : Nat) : output R 0=UnaryTemplate.tape R := by
  rw [output,install_other templateSlots _ _ _ (by decide)]
  exact source_power R

theorem raw_square (R : Nat) : output R 5=List.replicate (R^2) true := by
  change install templateSlots _ _ (templateSlots 0)=_
  rw [install_slot templateSlots (by decide)]
  rfl

theorem square_template (R : Nat) : output R 7=UnaryTemplate.tape (R^2) := by
  change install templateSlots _ _ (templateSlots 1)=_
  rw [install_slot templateSlots (by decide)]
  rfl

def readyH (i : Fin 9) : Nat := if i=7 then 1 else 0
def position := RecoveryFocus.machine (fun _ : Fin 1=>(7 : Fin 9))
  (Completion.PhysicalDriverMoves.machine 1 .right)
def readyMachine := Composition.machine machine position

theorem ready_run (R : Nat) : Step readyMachine (budget R+2) (fun _=>0) (input R)
    readyH (output R) := by
  have positionRun : Step position 1 (fun _=>0) (output R) readyH (output R) := by
    apply PhysicalFocusBoundary.focus
      (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0) (fun _=>output R 7))
      (fun _ : Fin 1=>(7 : Fin 9)) (by decide)
    · intros;rfl
    · intros;rfl
    · intros;rfl
    · intros;rfl
    · intro i hi
      refine ⟨?_,rfl⟩
      exact (if_neg (Ne.symm (hi 0))).symm
  simpa only [readyMachine,Nat.add_assoc] using (run R).seq positionRun

end
end PCJ9eff70d512234a4c_Fixed.Materializer.MajorityComplete.Width
