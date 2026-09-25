import Proof.Packets.CycleCommonReserve
import Proof.Rows.PhysicalDriverMoves
import Proof.Packets.ReusableArithmeticCore

/-! Cold physical allocation of the reusable 34-tape arithmetic bank.
Only raw R is resident initially. Two unary-template runs generate both R+3
logs, and an executed common sweep writes all thirty zero-backed tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.CycleArithmeticAllocate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairSource
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion CycleCommonReserve
noncomputable section

def input (R : Nat) (i : Fin 35) : List Bool := if i=32 then List.replicate R true else []
def bank1 (R : Nat) (i : Fin 35) : List Bool :=
  if i=31 then UnaryTemplate.tape R else if i=32 then List.replicate R true
  else if i=33 then List.replicate (R+3) false else []
def bank2 (R : Nat) (i : Fin 35) : List Bool :=
  if i=30 ∨ i=33 then List.replicate (R+3) false
  else if i=31 ∨ i=34 then UnaryTemplate.tape R
  else if i=32 then List.replicate R true else []
def output (R : Nat) (i : Fin 35) : List Bool :=
  if i.val<30 then List.replicate R false else bank2 R i
def heads (i : Fin 35) : Nat := if i=31 then 1 else 0

def templateSlots : Fin 3→Fin 35 := ![32,31,33]
def logSlots : Fin 3→Fin 35 := ![32,34,30]
def eraseSlots (i : Fin 32) : Fin 35 :=
  Fin.addCases (fun j : Fin 30=>j.castAdd 5) (![32,33] : Fin 2→Fin 35) i
def bootSlots : Fin 1→Fin 35 := ![31]
def templateMachine := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def logMachine := RecoveryFocus.machine logSlots (DimensionTemplate.machine false)
def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 30)
def bootMachine := RecoveryFocus.machine bootSlots (PhysicalDriverMoves.machine 1 .right)
def machine := Composition.machine (Composition.machine
  (Composition.machine templateMachine logMachine) eraseMachine) bootMachine
def budget (R : Nat) := 6*R+24

theorem template_step (R : Nat) : Step templateMachine (2*R+8)
    (fun _=>0) (input R) (fun _=>0) (bank1 R) := by
  apply PhysicalFocusBoundary.focus (of_clock (DimensionTemplate.ready false R))
    templateSlots (by decide) (fun _=>0) (fun _=>0) (input R) (bank1 R)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    refine ⟨rfl,?_⟩
    fin_cases i <;>simp [templateSlots,Fin.forall_fin_succ] at away
    all_goals rfl

theorem log_step (R : Nat) : Step logMachine (2*R+8)
    (fun _=>0) (bank1 R) (fun _=>0) (bank2 R) := by
  apply PhysicalFocusBoundary.focus (of_clock (DimensionTemplate.ready false R))
    logSlots (by decide) (fun _=>0) (fun _=>0) (bank1 R) (bank2 R)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    refine ⟨rfl,?_⟩
    fin_cases i <;>simp [logSlots,Fin.forall_fin_succ] at away
    all_goals rfl

theorem erase_step (R : Nat) : Step eraseMachine (2*R+4)
    (fun _=>0) (bank2 R) (fun _=>0) (output R) := by
  obtain ⟨r,hr,ht,hh,hs⟩ := RecoveryScratchErase.erase_ready R (R+3)
    (fun _ : Fin 30=>[]) (by intro i;simp)
  have small : Step (RecoveryScratchErase.resetMachine 30) (2*R+4)
      (fun _=>0) _ (fun _=>0) _ := ⟨r,hr,funext hh,ht,hs.le⟩
  apply PhysicalFocusBoundary.focus small eraseSlots (by decide)
    (fun _=>0) (fun _=>0) (bank2 R) (output R)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [eraseSlots,Fin.addCases,output,bank2,
      Nat.max_eq_left (by omega : R+1≤R+3)]
  · intro i away
    refine ⟨rfl,?_⟩
    fin_cases i <;>simp [eraseSlots,Fin.addCases,Fin.forall_fin_succ] at away
    all_goals rfl

theorem boot_step (R : Nat) : Step bootMachine 1
    (fun _=>0) (output R) heads (output R) := by
  have small:=PhysicalDriverMoves.run HeadMove.right (fun _ : Fin 1=>0)
    (fun _ : Fin 1=>UnaryTemplate.tape R)
  apply PhysicalFocusBoundary.focus small bootSlots (by decide)
    (fun _=>0) heads (output R) (output R)
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    refine ⟨?_,rfl⟩
    have hi : i≠31 := by intro h;subst i;exact away 0 rfl
    simp [heads,hi]

theorem run (R : Nat) : Step machine (budget R)
    (fun _=>0) (input R) heads (output R) := by
  have h:=(((template_step R).seq (log_step R)).seq (erase_step R)).seq (boot_step R)
  convert h using 1 <;>first | rfl | (unfold budget;omega)

end
end Theorem25Completion.CycleArithmeticAllocate
