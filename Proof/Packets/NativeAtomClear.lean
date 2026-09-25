import Proof.Packets.NativeAtomStore

/-! Pay the index head return and clear both delivered operand blocks and
the decoded index after storage, retaining all cache/bank cursors. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound

def indexSlot : Fin 1→Fin 44 := ![41]
def clearSlots : Fin 5→Fin 44 := ![26,27,41,34,35]
noncomputable def indexDown := RecoveryFocus.machine indexSlot (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def cleanup := Composition.machine indexDown clear

theorem index_down (C R pairPos codePos code : Nat) (pairs codes bank : List Bool) (raw : List (List Bool)) :
    Step indexDown 1 (heads pairPos codePos 1) (data C R pairs codes bank raw code)
      (heads pairPos codePos 0) (data C R pairs codes bank raw code) := by
  have h:=Completion.PhysicalDriverMoves.run .left (fun _ : Fin 1=>1)
    (fun _=>ZeroPadding.pad R (CompareMachine.word code))
  apply PhysicalFocusBoundary.focus h indexSlot (by decide)
    (heads pairPos codePos 1) (heads pairPos codePos 0)
    (data C R pairs codes bank raw code) (data C R pairs codes bank raw code)
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i;fin_cases i;rfl
  · intro i away
    fin_cases i <;> first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl)

theorem clear_run (C R pairPos codePos code : Nat) (pairs codes bank : List Bool)
    (raw : List (List Bool)) (hp : raw.flatten.length≤R) (hc : raw.length+1≤R) (hi : code+1≤R) :
    Step clear (2*R+4) (heads pairPos codePos 0) (data C R pairs codes bank raw code)
      (heads pairPos codePos 0) (data C R pairs codes bank [] 0) := by
  let a : Fin 3→List Bool := ![ZeroPadding.pad R raw.flatten,
    ZeroPadding.pad R (CompareMachine.word raw.length),ZeroPadding.pad R (CompareMachine.word code)]
  have cap : ∀i,(a i).length≤R := by
    intro i;fin_cases i <;>simp [a,ZeroPadding.pad_length,CompareMachine.word,hp,hc,hi]
    simpa only [List.length_flatten] using hp
  obtain ⟨r,hr,ht,hh,hs⟩:=RecoveryScratchErase.erase_ready R (R+3) a cap
  have small : Step (RecoveryScratchErase.resetMachine 3) (2*R+4)
      (fun _=>0) _ (fun _=>0) _ := ⟨r,hr,funext hh,ht,hs.le⟩
  have one : false::List.replicate (R-1) false=List.replicate R false := by
    rw [←List.replicate_succ];congr 1;omega
  apply PhysicalFocusBoundary.focus small clearSlots (by decide)
    (heads pairPos codePos 0) (heads pairPos codePos 0)
    (data C R pairs codes bank raw code) (data C R pairs codes bank [] 0)
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>rfl
  · intro i;fin_cases i <;>simp [data,NativePairNormalize.result,ReusableNative.ready,
      ReusableNative.bank,ReusableNative.readyData,clearSlots,Fin.addCases,ZeroPadding.pad,
      CompareMachine.word,one,Nat.max_eq_left (by omega : R+1≤R+3)]
  · intro i away
    fin_cases i <;>first | exact ⟨rfl,rfl⟩ | exact False.elim (away 0 rfl) |
      exact False.elim (away 1 rfl) | exact False.elim (away 2 rfl)

theorem cleanup_run (C R pairPos codePos code : Nat) (pairs codes bank : List Bool)
    (raw : List (List Bool)) (hp : raw.flatten.length≤R) (hc : raw.length+1≤R) (hi : code+1≤R) :
    Step cleanup (2*R+6) (heads pairPos codePos 1) (data C R pairs codes bank raw code)
      (heads pairPos codePos 0) (data C R pairs codes bank [] 0) := by
  have h:=(index_down C R pairPos codePos code pairs codes bank raw).seq
    (clear_run C R pairPos codePos code pairs codes bank raw hp hc hi)
  have fuel : 1+1+(2*R+4)=2*R+6 := by omega
  simpa only [cleanup,fuel] using h

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
