import Proof.Packets.WindowSeedDock
import Proof.Packets.WindowWidthDriver

/-! Paid retirement of temporary unary metadata and construction of the
outer window count from the retained actual half-window. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def clearOneSlots (d : Fin 69) : Fin 3→Fin 69 := ![d,50,51]
def clearOneAt (d : Fin 69) := RecoveryFocus.machine (clearOneSlots d) (RecoveryScratchErase.resetMachine 1)
def widthSlots : Fin 2→Fin 69 := ![61,68]
def widthAt := RecoveryFocus.machine widthSlots WindowWidthDriver.machine

theorem clear_one_at (R : Nat) (d : Fin 69) (A : Fin 69→List Bool)
    (hinj : Function.Injective (clearOneSlots d)) (hd : (A d).length≤R)
    (hr : A 50=List.replicate R true) (hl : A 51=List.replicate (R+3) false) :
    Step (clearOneAt d) (2*R+4) (fun _=>0) A (fun _=>0) (Function.update A d (List.replicate R false)) := by
  have h:=Step.of_ready (RecoveryScratchErase.erase_ready R (R+3) (fun _ : Fin 1=>A d) (fun _=>hd))
  have he : max (R+3) (R+1)=R+3 := by omega
  rw [he] at h
  let localA : Fin 3→List Bool := ![A d,List.replicate R true,List.replicate (R+3) false]
  have h' : Step (RecoveryScratchErase.resetMachine 1) (2*R+4) (fun _=>0) localA
      (fun _=>0) (Function.update localA 0 (List.replicate R false)) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  exact PhysicalOneOutput.focus _ _ _ 0 _ h' (clearOneSlots d) hinj (fun _=>0) A
    (fun _=>rfl) (by intro i;fin_cases i <;>first | rfl | exact hr | exact hl)

theorem width_at (R W : Nat) (A : Fin 69→List Bool) (hR : 1≤R)
    (hs : A 68=source R W) (hd : A 61=List.replicate R false) :
    Step widthAt (WindowWidthDriver.budget W) (fun _=>0) A (fun _=>0)
      (Function.update A 61 (source R (2*W+1))) := by
  have h:=WindowWidthDriver.run R W
  have h' : Step WindowWidthDriver.machine (WindowWidthDriver.budget W)
      (fun _=>0) (WindowWidthDriver.A R 0 W) (fun _=>0)
      (Function.update (WindowWidthDriver.A R 0 W) 0 (source R (2*W+1))) := by
    convert h using 1 <;>first | rfl | (funext i;fin_cases i <;>rfl)
  apply PhysicalOneOutput.focus _ _ _ 0 _ h' widthSlots (by decide) (fun _=>0) A (fun _=>rfl)
  intro i;fin_cases i
  · change A 61=ZeroPadding.pad R (CompareMachine.word 0)
    rw [hd]
    change List.replicate R false=ZeroPadding.pad R (List.replicate 1 false)
    rw [Rewind.Workspace.pad_zeros,Nat.max_eq_left hR]
  · exact hs

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
