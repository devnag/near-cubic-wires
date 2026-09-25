import Proof.Packets.VectorChildTransaction
import Proof.Packets.VectorAccumulatorReset
import Proof.Packets.PacketBankWrite

/-! The actual parent epilogue writes the completed accumulator into the next
resident vector at its physical parent index, then erases saved accumulator
storage by copying the retained zero tape. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorParentCommit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads : Fin 41→Nat := Fin.addCases (m:=39) (n:=2) (motive:=fun _=>Nat)
  VectorChildTransaction.heads (![0,1])
def tapes (B R child parent : Nat) (left right acc : List (List Bool)) (previous next : List Bool) : Fin 41→List Bool :=
  Fin.addCases (m:=39) (n:=2) (motive:=fun _=>List Bool)
    (VectorChildTransaction.tapes B R child left right acc previous)
    (![next,ZeroPadding.pad R (CompareMachine.word parent)])
def slots : Fin 6→Fin 41 := ![31,39,37,38,40,36]
def store := RecoveryFocus.machine slots PacketBank.storeSelectedZero
def reset := TapeEmbedding.machine 2 (RecoveryFocus.machine VectorChildTransaction.slots VectorAccumulator.reset)
def machine := Composition.machine store reset
def budget (R parent : Nat) := PacketBank.lookupBudget R parent+4+1+VectorAccumulator.copyBudget R

attribute [local irreducible] PacketBank.storeSelectedZero PacketBank.storeSelected

theorem store_run (B R child parent : Nat) (left right acc : List (List Bool))
    (previous pre oldPayload oldCount post : List Bool)
    (hpre : pre.length=2*parent*R) (ha : VectorAccumulator.Fits R acc)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step store (PacketBank.lookupBudget R parent+4)
      heads (tapes B R child parent left right acc previous (pre++oldPayload++oldCount++post))
      heads (tapes B R child parent left right acc previous
        (pre++ZeroPadding.pad R acc.flatten++ZeroPadding.pad R (CompareMachine.word acc.length)++post)) := by
  have h:=(PacketBank.store_selected_zero_run R parent pre oldPayload oldCount post
    (ZeroPadding.pad R acc.flatten) (ZeroPadding.pad R (CompareMachine.word acc.length))
    hpre (VectorAccumulator.flat_length R acc ha) (VectorAccumulator.count_length R acc ha) hop hoc).pad
      (![0,0,0,0,R,R] : Fin 6→Nat)
  apply PhysicalFocusBoundary.focus h slots (by decide) heads heads _ _
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,tapes,VectorChildTransaction.tapes,VectorChildLookup.tapes,
      PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
      ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [slots,tapes,VectorChildTransaction.tapes,VectorChildLookup.tapes,
      PacketBank.A,Fin.addCases,ReusableArithmetic.state,ReusableArithmetic.bank,
      ZeroPadding.pad_zero]
    simp [ZeroPadding.pad]
  · intro i away
    refine ⟨rfl,?_⟩
    revert away
    refine Fin.addCases (m:=39) (n:=2) (fun j=>?_) (fun j=>?_) i
    · intro _;unfold tapes;rw [Fin.addCases_left,Fin.addCases_left]
    · intro away;fin_cases j
      · exact False.elim (away 1 rfl)
      · rfl

theorem reset_run (B R child parent : Nat) (left right acc : List (List Bool))
    (previous next : List Bool) (ha : VectorAccumulator.Fits R acc) :
    Step reset (VectorAccumulator.copyBudget R) heads (tapes B R child parent left right acc previous next)
      heads (tapes B R child parent left right [] previous next) := by
  exact (VectorChildTransaction.dock B R child left right acc left right [] previous
    (VectorAccumulator.reset_run B R left right acc ha)).embed
      (![0,1] : Fin 2→Nat) (![next,ZeroPadding.pad R (CompareMachine.word parent)] : Fin 2→List Bool)

theorem run (B R child parent : Nat) (left right acc : List (List Bool))
    (previous pre oldPayload oldCount post : List Bool)
    (hpre : pre.length=2*parent*R) (ha : VectorAccumulator.Fits R acc)
    (hop : oldPayload.length=R) (hoc : oldCount.length=R) :
    Step machine (budget R parent)
      heads (tapes B R child parent left right acc previous (pre++oldPayload++oldCount++post))
      heads (tapes B R child parent left right [] previous
        (pre++ZeroPadding.pad R acc.flatten++ZeroPadding.pad R (CompareMachine.word acc.length)++post)) := by
  exact (store_run B R child parent left right acc previous pre oldPayload oldCount post hpre ha hop hoc).seq
    (reset_run B R child parent left right acc previous _ ha)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorParentCommit
