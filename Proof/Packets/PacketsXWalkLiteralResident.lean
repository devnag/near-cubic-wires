import Proof.Packets.PacketsXWalkLiteralPrepare
import Proof.Packets.CycleZeroAllocate

/-! A physical initial walk tuple: vertex words, transition labels and unary
masters are retained, while every scratch tape and the rewind log start empty.
A paid sweep creates the entire zero workspace, then positions the width head. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion
noncomputable section

def residentInput (rank R : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank))
    (code : List Bool) : Fin 15→List Bool :=
  ![WalkEdgeReuse.word (toeplitzWalkSideBits rank) R v.1,
    WalkEdgeReuse.word (toeplitzWalkSideBits rank) R v.2,[],[],List.replicate R true,
    UnaryTemplate.tape R,[],code,[],[],ZeroPadding.pad R (UnaryTemplate.tape rank),[],[],[],[]]
def residentSlots : Fin 10→Fin 15 := ![2,3,8,9,11,12,13,14,4,6]
def residentAllocate := RecoveryFocus.machine residentSlots (CycleFields.ZeroAllocate.machine 8)
def residentRaise := RecoveryFocus.machine (fun _ : Fin 1=>(5 : Fin 15)) (PhysicalDriverMoves.machine 1 .right)
def residentMachine := Composition.machine residentAllocate residentRaise

theorem resident_allocate_run (rank R : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool) :
    Step residentAllocate (2*R+4) (fun _=>0) (residentInput rank R v code)
      (fun _=>0) (WalkSeedResident.input rank R R v code) := by
  apply PhysicalFocusBoundary.focus (CycleFields.ZeroAllocate.run 8 R) residentSlots (by decide)
    (fun _=>0) (fun _=>0) (residentInput rank R v code) (WalkSeedResident.input rank R R v code)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i away
    fin_cases i <;>simp [residentSlots,Fin.forall_fin_succ] at away
    all_goals exact ⟨rfl,rfl⟩

theorem resident_raise_run (data : Fin 15→List Bool) :
    Step residentRaise 1 (fun _=>0) data (WalkSeedResident.heads 0) data := by
  have small:=PhysicalDriverMoves.run HeadMove.right (fun _ : Fin 1=>0) (fun _ : Fin 1=>data 5)
  apply PhysicalFocusBoundary.focus small (fun _ : Fin 1=>(5 : Fin 15))
    (by intro i j _;exact Subsingleton.elim i j) (fun _=>0) (WalkSeedResident.heads 0) data data
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    fin_cases i <;>simp [Fin.forall_fin_succ] at away
    all_goals exact ⟨rfl,rfl⟩

theorem resident_run (rank R : Nat) (v : MargulisVertex (2^toeplitzWalkSideBits rank)) (code : List Bool) :
    Step residentMachine (2*R+6) (fun _=>0) (residentInput rank R v code)
      (WalkSeedResident.heads 0) (WalkSeedResident.input rank R R v code) := by
  have joined:=(resident_allocate_run rank R v code).seq (resident_raise_run _)
  simpa only [residentMachine,show 2*R+4+1+1=2*R+6 by omega] using joined

end
end Theorem25Completion.WalkLiteralCold
