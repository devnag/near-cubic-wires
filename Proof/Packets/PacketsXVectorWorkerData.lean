import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerParent
import Proof.Packets.PhysicalFocusAppend

/-! Actual arithmetic/commit boundaries in the full296-port worker, retaining
all32 appended numeric/source work tapes exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def H (mh : Fin 222→Nat) : Fin 296→Nat := fun i => Fin.addCases (m:=264) (n:=32) (motive:=fun _=>Nat) (VectorController.H mh) (fun _ : Fin 32=>0) i
def A (B R ci pi li : Nat) (left right acc : List (List Bool)) (previous next : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool) : Fin 296→List Bool :=
  fun i => Fin.addCases (m:=264) (n:=32) (motive:=fun _=>List Bool) (VectorController.A B R ci pi li left right acc previous next fields) extra i

theorem dock_child {s fuel : Nat} {p : Machine 39 s}
    (B R ci pi li : Nat) (left right acc left' right' acc' : List (List Bool))
    (previous next : List Bool) (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (h : Step p fuel VectorChildTransaction.heads (VectorChildTransaction.tapes B R ci left right acc previous)
      VectorChildTransaction.heads (VectorChildTransaction.tapes B R ci left' right' acc' previous)) :
    Step (RecoveryFocus.machine childSlots p) fuel (H mh) (A B R ci pi li left right acc previous next fields extra)
      (H mh) (A B R ci pi li left' right' acc' previous next fields extra) := by
  apply PhysicalFocusAppend.run h VectorController.childSlots VectorController.childSlots_injective
    (VectorController.H mh) (VectorController.H mh) _ _ (fun _ : Fin 32=>0) extra
  · exact VectorController.child_heads mh
  · exact VectorController.child_tapes B R ci pi li left right acc previous next fields
  · exact VectorController.child_heads mh
  · exact VectorController.child_tapes B R ci pi li left' right' acc' previous next fields
  · intro i away
    exact ⟨rfl,VectorController.A_child_outside B R ci pi li left right acc left' right' acc' previous next fields i away⟩

theorem dock_parent {s fuel : Nat} {p : Machine 41 s}
    (B R ci pi li : Nat) (left right acc acc' : List (List Bool)) (previous next next' : List Bool)
    (mh : Fin 222→Nat) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (h : Step p fuel VectorParentCommit.heads (VectorParentCommit.tapes B R ci pi left right acc previous next)
      VectorParentCommit.heads (VectorParentCommit.tapes B R ci pi left right acc' previous next')) :
    Step (RecoveryFocus.machine parentSlots p) fuel (H mh) (A B R ci pi li left right acc previous next fields extra)
      (H mh) (A B R ci pi li left right acc' previous next' fields extra) := by
  apply PhysicalFocusAppend.run h VectorController.parentSlots VectorController.parentSlots_injective
    (VectorController.H mh) (VectorController.H mh) _ _ (fun _ : Fin 32=>0) extra
  · exact VectorController.parent_heads mh
  · exact VectorController.parent_tapes B R ci pi li left right acc previous next fields
  · exact VectorController.parent_heads mh
  · exact VectorController.parent_tapes B R ci pi li left right acc' previous next' fields
  · intro i away
    exact ⟨rfl,VectorController.A_parent_outside B R ci pi li left right acc acc' previous next next' fields i away⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
