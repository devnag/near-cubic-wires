import Proof.Packets.PacketsXVectorWorkerProjection
import Proof.Packets.PacketsXVectorWorkerCommit

/-! Physically replace the next-bank coordinate at the live candidate index
with the completed right operand. Every arithmetic operand is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def coordinateStoreSlots : Fin 6→Fin 296:=![31,257,26,27,258,263]
attribute [local irreducible] PacketBank.storeSelectedZero
def coordinateStore:=RecoveryFocus.machine coordinateStoreSlots PacketBank.storeSelectedZero

theorem next_outside (C R ci pi li : Nat) (left right acc : PacketVector.Packet)
    (previous next next' : List Bool) (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (i : Fin 296) (away : i≠257) :
    A C R ci pi li left right acc previous next fields extra i=
      A C R ci pi li left right acc previous next' fields extra i := by
  revert away
  refine Fin.addCases (m:=264) (n:=32) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=256) (n:=8) (fun k=>?_) (fun k=>?_) j
    · intro _;simp only [A,VectorController.A,Fin.addCases_left]
    · intro away
      have hn:k≠1 := by intro he;subst k;exact away rfl
      rw [A_saved,A_saved]
      simp only [VectorController.extraTapes,if_neg hn]
  · intro _;rw [A_extra,A_extra]

attribute [local irreducible] coordinateStore

theorem coordinate_store_run (C R pi li : Nat) (ns : List PacketVector.Packet) (i : Fin ns.length)
    (left right acc : PacketVector.Packet) (previous : List Bool)
    (fields : Fin 222→List Bool) (extra : Fin 32→List Bool)
    (hns : ∀P∈ns,PacketVector.Fits R P) (hr : VectorAccumulator.Fits R right) :
    Step coordinateStore (PacketBank.lookupBudget R i.val+4)
      (H (fun _=>0)) (A C R i.val pi li left right acc previous (PacketVector.bank R ns) fields extra)
      (H (fun _=>0)) (A C R i.val pi li left right acc previous (PacketVector.bank R (ns.set i.val right)) fields extra) := by
  have hi:=hns _ (List.getElem_mem i.isLt)
  have hpre : (PacketVector.bank R (ns.take i.val)).length=2*i.val*R := by
    rw [PacketVector.bank_length R _ (fun P hP=>hns P (List.mem_of_mem_take hP)),List.length_take,
      Nat.min_eq_left (Nat.le_of_lt i.isLt)]
  have small:=(PacketBank.store_selected_zero_run R i.val (PacketVector.bank R (ns.take i.val))
    (PacketVector.payload R ns[i.val]) (PacketVector.count R ns[i.val])
    (PacketVector.bank R (ns.drop (i.val+1)))
    (ZeroPadding.pad R right.flatten) (ZeroPadding.pad R (CompareMachine.word right.length))
    hpre (VectorAccumulator.flat_length R right hr) (VectorAccumulator.count_length R right hr)
    (PacketVector.payload_length hi) (PacketVector.count_length hi)).pad
      (![0,0,0,0,R,R] : Fin 6→Nat)
  have split:=PacketVector.bank_split R ns i
  have replaced:=bank_set R ns i right
  unfold PacketVector.payload PacketVector.count at replaced
  rw [←split,←replaced] at small
  unfold coordinateStore
  apply PhysicalFocusBoundary.focus small coordinateStoreSlots (by decide) (H (fun _=>0)) (H (fun _=>0)) _ _
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>simp [coordinateStoreSlots,A,VectorController.A,VectorController.extraTapes,
      PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
      ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,ZeroPadding.pad]
  · intro j;fin_cases j <;>rfl
  · intro j;fin_cases j <;>simp [coordinateStoreSlots,A,VectorController.A,VectorController.extraTapes,
      PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,ReusableArithmetic.padded,
      ReusableArithmetic.data,NormalizedMultiply.data,NormalizedMultiply.extras,ZeroPadding.pad]
  · intro j away
    exact ⟨rfl,next_outside C R i.val pi li left right acc previous _ _ fields extra j
      (fun he=>away 1 he.symm)⟩

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
