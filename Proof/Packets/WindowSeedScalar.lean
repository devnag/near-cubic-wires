import Proof.Packets.WindowSeedPrimitives

/-! Actual M-1 and framed scalar construction for the subset enumerator.
Both retained metadata counters return to head zero. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def countPred := Composition.machine (Completion.PhysicalDriverMoves.machine 1 .right)
  (Composition.machine VectorCounter.decrement (Completion.PhysicalDriverMoves.machine 1 .left))

theorem count_pred_run (R n : Nat) (hR : n+1≤R) :
    Step countPred (2*n+7) (fun _=>0) (fun _=>source R n)
      (fun _=>0) (fun _=>source R (n-1)) := by
  have first:=Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0) (fun _=>source R n)
  have middle:=DescendingWindowCounters.decrement_run n R hR
  have last:=Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1) (fun _=>source R (n-1))
  have all:=first.seq (middle.seq last)
  have fuel : 1+1+((2*n+3)+1+1)=2*n+7 := by omega
  simpa only [countPred,fuel,source,HeadMove.apply] using all

def valueData (R u old N : Nat) : Fin 3→List Bool :=
  ![ZeroPadding.pad R (frame (binary u old)),List.replicate (R+3) false,source R N]
def valueHeads : Fin 3→Nat := ![0,0,1]
def countSlot : Fin 1→Fin 3 := ![2]
def valueUp := RecoveryFocus.machine countSlot (Completion.PhysicalDriverMoves.machine 1 .right)
def valueDown := RecoveryFocus.machine countSlot (Completion.PhysicalDriverMoves.machine 1 .left)
def scalarValue := Composition.machine valueUp (Composition.machine ScalarFromCounter.machine valueDown)

theorem value_moves (R u old N : Nat) :
    Step valueUp 1 (fun _=>0) (valueData R u old N) valueHeads (valueData R u old N) ∧
    Step valueDown 1 valueHeads (valueData R u old N) (fun _=>0) (valueData R u old N) := by
  constructor
  · apply PhysicalFocusBoundary.focus
      (Completion.PhysicalDriverMoves.run .right (fun _ : Fin 1=>0) (fun _=>source R N))
      countSlot (by decide) (fun _=>0) valueHeads (valueData R u old N) (valueData R u old N)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)
  · apply PhysicalFocusBoundary.focus
      (Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1) (fun _=>source R N))
      countSlot (by decide) valueHeads (fun _=>0) (valueData R u old N) (valueData R u old N)
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i;fin_cases i;rfl
    · intro i away;fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem scalar_value_run (R u old N : Nat) (hn : N<2^u) (hu : 2*u+1≤R+3) :
    Step scalarValue (ScalarFromCounter.budget u N+4) (fun _=>0) (valueData R u old N)
      (fun _=>0) (valueData R u N N) := by
  have middle:=(ScalarFromCounter.run u old (R+3) N hn hu).pad (![R,0,R] : Fin 3→Nat)
  have middle' : Step ScalarFromCounter.machine (ScalarFromCounter.budget u N)
      valueHeads (valueData R u old N) valueHeads (valueData R u N N) := by
    convert middle using 1 <;>first | rfl |
      (funext i;fin_cases i <;>simp [valueHeads,ScalarFromCounter.heads,valueData,source,ScalarFromCounter.data,ScalarFromCounter.pair,
        Fin.addCases,ZeroPadding.pad_zero])
  have all:=(value_moves R u old N).1.seq (middle'.seq (value_moves R u N N).2)
  have fuel : 1+1+(ScalarFromCounter.budget u N+1+1)=ScalarFromCounter.budget u N+4 := by omega
  simpa only [scalarValue,fuel] using all

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
